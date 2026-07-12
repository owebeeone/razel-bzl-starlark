use allocative::Allocative;
use razel_bzl_api::{ActionTemplate, AttrType, BzlValue, GlobSpec, TargetDecl};
use starlark::environment::{GlobalsBuilder, Methods, MethodsBuilder, MethodsStatic};
use starlark::eval::Evaluator;
use starlark::starlark_module;
use starlark::values::dict::DictRef;
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{starlark_value, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, UnpackValue, Value, ValueLike};
use starlark::starlark_simple_value;
use std::cell::RefCell;
use std::fmt;

use crate::convert::convert;
use crate::globals_def::ToolchainTypeReq;
use crate::values::{AttrTypeValue, Provider, RuleValue, RuleValueGen};
use crate::values_label::{parse_label, LabelValue};

/// Extract a toolchain TYPE label from a `rule(toolchains=[…])` entry: a bare type-label string, a `Label`,
/// or a `config_common.toolchain_type(...)` requirement (rules_rust mixes all three). Fail-closed otherwise.
fn toolchain_type_label(v: Value) -> anyhow::Result<String> {
    if let Some(s) = v.unpack_str() {
        return Ok(s.to_owned());
    }
    if let Some(l) = v.downcast_ref::<LabelValue>() {
        return Ok(l.display.clone());
    }
    if let Some(t) = v.downcast_ref::<ToolchainTypeReq>() {
        return Ok(t.label.clone());
    }
    Err(anyhow::anyhow!("a toolchain type must be a label string, a Label, or config_common.toolchain_type()"))
}

/// The load-time `Label()` builtin. rules_cc / rules_rust build Label CONSTANTS at load
/// (`CC_TOOLCHAIN_TYPE = Label("@bazel_tools//tools/cpp:toolchain_type")`), often exported + `load()`ed.
#[starlark_module]
pub(crate) fn label_global(builder: &mut GlobalsBuilder) {
    /// `Label(input)` — construct a `Label` from its canonical string (`@repo//pkg:name` / `//pkg:name`), or
    /// pass a `Label` through (idempotent). v1 parses the absolute forms; repo-mapping-relative resolution of
    /// a bare/relative input is an R-analyze concern (it degrades to best-effort fields here).
    #[allow(non_snake_case)]
    fn Label<'v>(#[starlark(require = pos)] input: Value<'v>, heap: Heap<'v>) -> anyhow::Result<Value<'v>> {
        if let Some(l) = input.downcast_ref::<LabelValue>() {
            return Ok(heap.alloc(l.clone()));
        }
        let s = input.unpack_str().ok_or_else(|| anyhow::anyhow!("Label() expects a label string"))?;
        let p = parse_label(s);
        Ok(heap.alloc(LabelValue {
            package: p.package,
            name: p.name,
            workspace_name: p.workspace_name,
            repo_name: p.repo_name,
            display: p.display,
        }))
    }
}

/// `select()` (T20 select) — Bazel's configurable-attribute selector, a global in BOTH the `.bzl` and the
/// BUILD env (crate_universe emits `deps = select({...})` in BUILDs; rulesets build selects in `.bzl` too).
/// Returns a first-class UNRESOLVED [`crate::values_select::SelectValue`]; it is NEVER resolved here (the
/// configuration is unknown at load) — resolution is analysis (`razel-analysis`), against the target's
/// configuration. `select(conditions, no_match_error = "")`.
#[starlark_module]
pub(crate) fn select_global(builder: &mut GlobalsBuilder) {
    fn select<'v>(
        #[starlark(require = pos)] conditions: Value<'v>,
        #[starlark(require = named)] no_match_error: Option<String>,
        heap: Heap<'v>,
    ) -> anyhow::Result<Value<'v>> {
        let dict = DictRef::from_value(conditions)
            .ok_or_else(|| anyhow::anyhow!("select() expects a dict of {{condition: value}}"))?;
        crate::values_select::make_select(dict, no_match_error.unwrap_or_default(), heap)
    }
}

/// `native` — the Bazel BUILD/macro namespace, available in `.bzl` for MACROS (functions a BUILD calls at
/// load). rules_rust references `native.test_suite(...)` inside the `rust_test_suite` macro body, so the NAME
/// must resolve when rust.bzl loads. razel exposes ONLY what the demanded closure references; a call is
/// fail-closed (the BUILD-macro construct is DEFERRED — row 12 — never a silent no-op).
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct NativeValue;
starlark_simple_value!(NativeValue);
impl fmt::Display for NativeValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<native>")
    }
}
#[starlark_value(type = "native")]
impl<'v> StarlarkValue<'v> for NativeValue {
    fn get_methods() -> Option<&'static Methods> {
        static RES: MethodsStatic = MethodsStatic::new("native", native_methods);
        Some(RES.methods())
    }
}

#[starlark_module]
fn native_methods(builder: &mut MethodsBuilder) {
    /// `native.test_suite(name, tests, **kwargs)` — a BUILD-macro construct (T20 R-load). Referenced in
    /// rules_rust's `rust_test_suite` macro; DEFERRED (row 12), so a call is a fail-closed typed error (never a
    /// silent no-op). The name resolves at load; only an actual BUILD-macro invocation trips this.
    fn test_suite<'v>(
        #[starlark(this)] _this: Value<'v>,
        #[starlark(kwargs)] _kwargs: DictRef<'v>,
    ) -> anyhow::Result<NoneType> {
        Err(anyhow::anyhow!("native.test_suite is deferred (row 12): BUILD-macro test_suite is not built in this wave"))
    }
}

// ──────────────── globals ────────────────
// The per-phase Globals are NAMED, precomputed and digested in `envs` (lockdown §3) — the ad-hoc
// rebuilt-per-call `bzl_globals()` is gone. The registrar fns below stay here (they own the builtins).

/// Accumulates the actions a rule's impl declares (via `ctx.actions.run`/`write`) AND the arg fragments its
/// `ctx.actions.args()` builders accumulate. Installed in `eval.extra` during `evaluate_rule` so the method
/// builtins (a `fn`, can't capture) record into it; the actions are collected into the `RuleResult`. The
/// arg-builder store lives HERE (not in the `Args` value) so `Args` stays an immutable, `Sync` handle — the
/// mutable fragment vector is single-threaded (one impl eval), keyed by the builder's index.
#[derive(Default, ProvidesStaticType)]
pub(crate) struct ActionRegistry {
    pub(crate) actions: RefCell<Vec<ActionTemplate>>,
    pub(crate) arg_builders: RefCell<Vec<Vec<String>>>,
    /// The live-module bridge (T20 R-analyze): `evaluate_rule` installs the ActionRegistry in `eval.extra`, but
    /// a real rule `.bzl` ALSO calls loaded functions (both at module scope — `dedent(…)` — and inside the
    /// impl). Since `eval.extra` holds ONE value, the ActionRegistry carries the bridge so a `LoadedFunction`
    /// invoke resolves the real callable during rule eval. `None` for the write/genrule-fixture registries that
    /// never run a loaded-function-calling `.bzl` (they downcast to ActionRegistry only for `ctx.actions`).
    pub(crate) bridge: Option<crate::bridge::ModuleBridge>,
}

// The `declare_action`/`write_file` GLOBALS are DELETED (D5 — single dialect). Their behavior lives on
// `ctx.actions.run`/`ctx.actions.write` (crate::actions), projecting into the SAME `ActionTemplate` via the
// SAME `ActionRegistry` (still installed in `eval.extra` by `evaluate_rule`).

#[starlark_module]
pub(crate) fn rule_global(builder: &mut GlobalsBuilder) {
    /// `rule(implementation = <fn>, attrs = {name: attr.<type>()}, toolchains = ["//type"], executable = …)` —
    /// define a rule. Records the attr schema + the required toolchain TYPE ids + the per-attr required
    /// providers / mandatory flags (C5, LIVE-only channels enforced at analysis); validates an implementation
    /// is present. `executable = True` is accepted (Appendix A's `rust_binary`) and marks a runnable rule —
    /// razel's build uses the CT's action outputs, not this flag, so it is recorded-not-consumed in this wave.
    /// Running the impl (+ resolving the toolchains) is analysis.
    fn rule<'v>(
        #[starlark(require = named)] implementation: Value<'v>,
        #[starlark(require = named)] attrs: Option<DictRef<'v>>,
        #[starlark(require = named)] toolchains: Option<Value<'v>>,
        #[starlark(require = named)] executable: Option<Value<'v>>,
        #[starlark(require = named)] test: Option<Value<'v>>,
        #[starlark(require = named)] cfg: Option<Value<'v>>,
        #[starlark(require = named)] build_setting: Option<Value<'v>>,
        #[starlark(require = named)] fragments: Option<Value<'v>>,
        #[starlark(require = named)] provides: Option<Value<'v>>,
        #[starlark(require = named)] exec_groups: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<RuleValue<'v>> {
        let _ = executable; // accepted (rust_binary); the runnable-output semantics ride DefaultInfo.executable
        // PARSE-LEVEL kwargs the demanded rules_rust/bazel_skylib closure passes at load. Accepted + recorded
        // (not yet enforced): `test` (a test rule — `rustfmt_test`/`rustdoc_test`; runnable-test semantics are
        // R-analyze), `cfg` (a rule-level configuration TRANSITION — `rule(cfg = _rust_binary_transition)`; the
        // transition is a deferred marker, row 12), `build_setting` (a config.* descriptor — build_setting
        // rules), `fragments`/`provides`/`exec_groups` (analysis-config declarations), `doc` (never identity),
        // plus a `**extra` absorber for the long tail (`initializer`/`subrules`/…). A rule that actually DRIVES
        // any of these at analysis fails closed there, never here.
        let _ = (test, cfg, build_setting, fragments, provides, exec_groups, doc, extra);
        if implementation.is_none() {
            return Err(anyhow::anyhow!("rule() requires an 'implementation' function"));
        }
        let mut schema: Vec<(String, u8)> = Vec::new();
        let mut attr_files: Vec<(String, Vec<String>)> = Vec::new();
        let mut attr_providers: Vec<(String, Vec<String>)> = Vec::new();
        let mut attr_mandatory: Vec<String> = Vec::new();
        let mut attr_string_defaults: Vec<(String, String)> = Vec::new();
        if let Some(d) = attrs {
            for (k, v) in d.iter() {
                let key = k
                    .unpack_str()
                    .ok_or_else(|| anyhow::anyhow!("attr name must be a string"))?
                    .to_owned();
                let at = v
                    .downcast_ref::<AttrTypeValue>()
                    .ok_or_else(|| anyhow::anyhow!("attr '{key}' must be an attr.* type"))?;
                schema.push((key.clone(), at.code));
                // A files attr (`label_list(allow_files=…)`) records its accepted extensions on the live
                // channel, so `evaluate_rule` can build `ctx.files.<attr>` + validate source extensions.
                if let Some(exts) = &at.allow_files {
                    attr_files.push((key.clone(), exts.clone()));
                }
                if !at.providers.is_empty() {
                    attr_providers.push((key.clone(), at.providers.clone()));
                }
                if at.mandatory {
                    attr_mandatory.push(key.clone());
                }
                // P1b: an `attr.string(default=…)` value rides the live channel so `evaluate_rule` applies it
                // when a target omits the attr.
                if let Some(def) = &at.default {
                    attr_string_defaults.push((key.clone(), def.clone()));
                }
            }
        }
        schema.sort_by(|a, b| a.0.cmp(&b.0));
        attr_files.sort_by(|a, b| a.0.cmp(&b.0));
        attr_providers.sort_by(|a, b| a.0.cmp(&b.0));
        attr_mandatory.sort();
        attr_string_defaults.sort_by(|a, b| a.0.cmp(&b.0));
        let mut required: Vec<String> = match toolchains {
            None => Vec::new(),
            Some(v) => {
                let list = ListRef::from_value(v)
                    .ok_or_else(|| anyhow::anyhow!("rule() toolchains must be a list of toolchain types"))?;
                // A toolchain type entry is a type-label STRING, a `Label`, or a
                // `config_common.toolchain_type(...)` requirement (rules_rust mixes all three). Extract the
                // type label from each; the mandatory flag is analysis-time (deferred).
                list.iter()
                    .map(toolchain_type_label)
                    .collect::<anyhow::Result<Vec<String>>>()?
            }
        };
        required.sort();
        required.dedup();
        Ok(RuleValueGen { implementation, attrs: schema, toolchains: required, attr_files, attr_providers, attr_mandatory, attr_string_defaults })
    }
}

/// The well-known builtin `DefaultInfo` provider NAME (the `RazelV4ProviderIdentityLockdown.md` row-G first
/// slice). v1 cut: a well-known NAMED provider under the single-module cap — the reserved builtin NAMESPACE
/// byte (0x01) that partitions builtins from Starlark `FooInfo`s is a later additive step (this v1 identity
/// is namespace 0x00 `DefaultInfo`, `bzl = None`). Referenced by the env registration (a global) AND by
/// `evaluate_rule`'s `dep[Provider]` re-keying (`providers_by_id`) so both agree on one identity.
pub(crate) const DEFAULT_INFO_NAME: &str = "DefaultInfo";

/// The v1 `DefaultInfo` builtin (row-G minimal shape, C5-widened): `files` (a `depset[File]` of the target's
/// default outputs) + `executable` (an optional `File` — a `rust_binary`'s runnable output, `None` for a
/// library). Constructible from a rule impl (`DefaultInfo(files=depset([out]), executable=out)`) and readable
/// via `dep[DefaultInfo]`. The `files` depset elements are Files whose `.path` is the exec-relative output
/// path; a dependent rule flattens them and the InputResolver maps each to its producing action via the owner
/// CT's chaining map (files-chaining — unchanged: that map is keyed on the SAME exec paths, engine-facing).
pub(crate) fn default_info_provider() -> Provider {
    Provider { id: DEFAULT_INFO_NAME.to_owned(), fields: vec!["executable".to_owned(), "files".to_owned()], schemaless: false }
}

/// The builtin `OutputGroupInfo` provider NAME (T20 R-load). Bazel predeclares `OutputGroupInfo` as a global
/// provider; rules_rust's `rustc.bzl:1944` builds `OutputGroupInfo(**output_group_info)` in the library/binary
/// impl. SCHEMALESS (arbitrary named output groups → depsets, `OutputGroupInfo(**kwargs)`), so any group name
/// constructs. Referenced as a global (registered in the env), NOT a module binding.
pub(crate) const OUTPUT_GROUP_INFO_NAME: &str = "OutputGroupInfo";

/// The builtin `OutputGroupInfo` provider — SCHEMALESS (Bazel's `OutputGroupInfo(**kwargs)` names output
/// groups freely). Constructible from a rule impl; its output-group semantics (extra build outputs) are
/// deferred (row 12) — the provider VALUE constructs so the impl EVALUATES.
pub(crate) fn output_group_info_provider() -> Provider {
    Provider { id: OUTPUT_GROUP_INFO_NAME.to_owned(), fields: Vec::new(), schemaless: true }
}

/// The builtin `RunEnvironmentInfo` provider NAME (T20 R-load). Bazel predeclares it as a global; rules_rust's
/// `rustfmt.bzl:280` builds `RunEnvironmentInfo(environment=…, inherited_environment=…)` for a test/runnable
/// target. SCHEMALESS (accepts `environment`/`inherited_environment`); the runfiles-env semantics are deferred
/// (row 12) — the value constructs so the impl EVALUATES.
pub(crate) const RUN_ENVIRONMENT_INFO_NAME: &str = "RunEnvironmentInfo";

/// The builtin `RunEnvironmentInfo` provider — SCHEMALESS (constructs from a rule impl; run-environment
/// behavior deferred).
pub(crate) fn run_environment_info_provider() -> Provider {
    Provider { id: RUN_ENVIRONMENT_INFO_NAME.to_owned(), fields: Vec::new(), schemaless: true }
}

/// The builtin `platform_common.ToolchainInfo` NAME (C6). A rule's `platform_common.ToolchainInfo(rustc=…)`
/// constructs it; toolchain resolution surfaces it as `ctx.toolchains[<type label>]`. The v1 injected registry
/// (rust_toolchain.rs) builds an equivalent `ProviderInstance` under the SAME name so the injection path and
/// the `.bzl` `rust_toolchain` rule agree on one identity.
pub(crate) const TOOLCHAIN_INFO_NAME: &str = "ToolchainInfo";

/// The builtin `ToolchainInfo` provider — SCHEMALESS (Bazel's `platform_common.ToolchainInfo(**kwargs)`), so a
/// toolchain rule can carry any fields (rust carries just `rustc`).
pub(crate) fn toolchain_info_provider() -> Provider {
    Provider { id: TOOLCHAIN_INFO_NAME.to_owned(), fields: Vec::new(), schemaless: true }
}

/// The builtin `platform_common.TemplateVariableInfo` NAME (T20 R-load). rules_rust reads it via
/// `platform_common.TemplateVariableInfo(variables={…})`. SCHEMALESS; make-variable expansion is deferred.
pub(crate) const TEMPLATE_VARIABLE_INFO_NAME: &str = "TemplateVariableInfo";

/// The builtin `TemplateVariableInfo` provider — SCHEMALESS (carries `variables`; expansion deferred, row 9/12).
pub(crate) fn template_variable_info_provider() -> Provider {
    Provider { id: TEMPLATE_VARIABLE_INFO_NAME.to_owned(), fields: Vec::new(), schemaless: true }
}

/// Parse a `provider()` `fields=` value: Bazel's DICT form `{"name": "doc", …}` (the Appendix-A shape — the
/// KEYS are the field names, docs ignored) OR the legacy LIST form `["name", …]` (R5, kept additive).
/// Fail-closed on any other shape. Field names are sorted (deterministic schema; access is order-independent).
fn parse_provider_fields(fields: Option<Value>) -> anyhow::Result<Vec<String>> {
    let mut names: Vec<String> = match fields {
        None => Vec::new(),
        Some(v) if v.is_none() => Vec::new(),
        Some(v) => {
            if let Some(dict) = DictRef::from_value(v) {
                dict.keys()
                    .map(|k| k.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("provider() field names must be strings")))
                    .collect::<anyhow::Result<Vec<String>>>()?
            } else if let Some(list) = ListRef::from_value(v) {
                list.iter()
                    .map(|item| item.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("provider() field names must be strings")))
                    .collect::<anyhow::Result<Vec<String>>>()?
            } else {
                return Err(anyhow::anyhow!("provider() fields must be a dict {{name: doc}} or a list of names"));
            }
        }
    };
    names.sort();
    names.dedup();
    Ok(names)
}

#[starlark_module]
pub(crate) fn provider_global(builder: &mut GlobalsBuilder) {
    /// `provider(name = None, *, doc = None, fields = {..}|[..])` — declare a provider type. The Appendix-A
    /// (real-Bazel) form omits the name entirely (`RustInfo = provider(doc=, fields={dict})`) and takes the
    /// `doc`/dict-`fields` kwargs; the explicit-name positional (R5) is kept additive. Identity under the v1
    /// single-module cap: the explicit name when given, else `""` (name-less) — a name-less provider is
    /// identified consistently within a rule `.bzl` (one custom provider per file today), and its exported
    /// codec-neutral binding is stamped with its variable name in the module-load export loop (like `rule()`).
    /// Full export-on-assignment identity (the defining-`.bzl` `bzl` dim fill) is the deferred additive upgrade.
    fn provider<'v>(
        #[starlark(require = pos)] name: Option<String>,
        #[starlark(require = named)] fields: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
    ) -> anyhow::Result<Provider> {
        let _ = doc; // accepted (Bazel's `provider(doc=)`), not stored — docs aren't identity
        Ok(Provider { id: name.unwrap_or_default(), fields: parse_provider_fields(fields)?, schemaless: false })
    }
}

/// Parse an `allow_files=` value (C3): `True` → allow any file (`Some([])`), a list of extension strings →
/// `Some([".rs", …])`, `False`/absent → `None` (not a files attr). Fail-closed on any other shape.
fn parse_allow_files(v: Option<Value>) -> anyhow::Result<Option<Vec<String>>> {
    match v {
        None => Ok(None),
        Some(val) => {
            if let Some(b) = val.unpack_bool() {
                return Ok(if b { Some(Vec::new()) } else { None });
            }
            if let Some(list) = ListRef::from_value(val) {
                let exts = list
                    .iter()
                    .map(|i| i.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("allow_files entries must be extension strings")))
                    .collect::<anyhow::Result<Vec<String>>>()?;
                return Ok(Some(exts));
            }
            Err(anyhow::anyhow!("allow_files must be True or a list of extension strings"))
        }
    }
}

/// `mandatory = True|False` → a bool (default `False`); any non-bool is ignored (fail-open on the flag only —
/// the value it guards is still schema-validated). C5: the flag is now STORED + ENFORCED at analysis.
fn parse_mandatory(v: Option<Value>) -> bool {
    v.and_then(|val| val.unpack_bool()).unwrap_or(false)
}

/// `default = "…"` on `attr.string` (P1b) → the stored string default (`None` when absent or non-string). The
/// interpreter now APPLIES this: a target omitting the attr sees this value in `ctx.attr.<name>` (Bazel's
/// default semantics), so `edition = attr.string(default = "2021")` yields `"2021"` unset. Only strings carry
/// an explicit default in this slice — list/scalar attrs fall back to the type's implicit zero at analysis.
fn parse_string_default(v: Option<Value>) -> Option<String> {
    v.and_then(|val| val.unpack_str().map(|s| s.to_owned()))
}

/// Parse a `providers = [P, …]` (or the nested `[[A, B], …]`) value into the required provider NAMES (C5).
/// Each entry is a provider TYPE value (`provider()` result). Nested groups are flattened (v1: "require ALL
/// listed"; the AND-of-ORs form is a later refinement). Fail-closed on a non-provider entry.
fn parse_providers(v: Option<Value>) -> anyhow::Result<Vec<String>> {
    let name_of = |p: Value| -> anyhow::Result<String> {
        p.downcast_ref::<Provider>()
            .map(|pr| pr.provider_id().name().to_owned())
            .ok_or_else(|| anyhow::anyhow!("attr providers entries must be provider types (the result of provider())"))
    };
    match v {
        None => Ok(Vec::new()),
        Some(val) if val.is_none() => Ok(Vec::new()),
        Some(val) => {
            let list = ListRef::from_value(val)
                .ok_or_else(|| anyhow::anyhow!("attr providers must be a list of provider types"))?;
            let mut out = Vec::new();
            for item in list.iter() {
                if let Some(inner) = ListRef::from_value(item) {
                    for p in inner.iter() {
                        out.push(name_of(p)?);
                    }
                } else {
                    out.push(name_of(item)?);
                }
            }
            Ok(out)
        }
    }
}

#[starlark_module]
pub(crate) fn attr_namespace(builder: &mut GlobalsBuilder) {
    // Every ctor accepts the common Bazel attr kwargs (`mandatory`/`default`/`doc`/`providers`) so a
    // Bazel-shaped declaration is not rejected. C5 makes `mandatory` (all attrs) and `providers` (label
    // attrs) load-bearing: both are STORED on the marker and ENFORCED at analysis. `allow_files` (on
    // `label_list`) flips the type to `FileList`; `default`/`doc` stay accepted-not-stored. A `**extra`
    // absorber (T20 R-load) accepts the LONG TAIL of real-world attr kwargs (`cfg`/`executable`/`aspects`/
    // `allow_single_file`/`values`/`flags`/…) so a real ruleset's attr declaration EVALUATES; their analysis
    // behavior is deferred (the same accept-and-defer posture `rule()` uses for its config kwargs).
    fn int<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (default, doc, extra);
        Ok(AttrTypeValue { code: AttrType::Int.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: None })
    }
    fn string<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (doc, extra);
        // P1b: `default =` is now STORED (a string) and APPLIED at analysis when the target omits the attr.
        Ok(AttrTypeValue { code: AttrType::String.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: parse_string_default(default) })
    }
    fn bool<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (default, doc, extra);
        Ok(AttrTypeValue { code: AttrType::Bool.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: None })
    }
    fn label<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] providers: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (doc, extra);
        Ok(AttrTypeValue { code: AttrType::Label.code(), allow_files: None, providers: parse_providers(providers)?, mandatory: parse_mandatory(mandatory), default: None })
    }
    fn label_list<'v>(
        #[starlark(require = named)] allow_files: Option<Value<'v>>,
        #[starlark(require = named)] providers: Option<Value<'v>>,
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (doc, extra);
        let allow = parse_allow_files(allow_files)?;
        // allow_files present ⇒ a FILES attr (source files, `ctx.files.<attr>`) — NOT a dep edge; else a
        // plain label_list (dep edges resolved to configured targets).
        let code = if allow.is_some() { AttrType::FileList.code() } else { AttrType::LabelList.code() };
        Ok(AttrTypeValue { code, allow_files: allow, providers: parse_providers(providers)?, mandatory: parse_mandatory(mandatory), default: None })
    }
    fn string_list<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        // A string_list's Bazel-implicit default is `[]` (applied at analysis); an explicit `default =` list is
        // accepted-not-stored in this slice (list defaults aren't the pagable string channel — deferred).
        let _ = (default, doc, extra);
        Ok(AttrTypeValue { code: AttrType::StringList.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: None })
    }
    /// `attr.string_dict()` (T20 R-load, row 5) — a `{string: string}` map attr. rules_rust's toolchain
    /// declares several (`debug_info`/`opt_level`/`strip_level`). NOT a dep edge; analysis surfacing deferred.
    fn string_dict<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (default, doc, extra);
        Ok(AttrTypeValue { code: AttrType::StringDict.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: None })
    }
    /// `attr.string_list_dict()` (T20 R-load, row 5) — a `{string: [string]}` map attr.
    fn string_list_dict<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (default, doc, extra);
        Ok(AttrTypeValue { code: AttrType::StringListDict.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: None })
    }
    /// `attr.label_keyed_string_dict()` (T20 R-load, row 5) — a `{label: string}` map attr. In Bazel its KEYS
    /// are dep edges; razel does NOT yet resolve dict-keyed deps (`is_label()` = FALSE — DEFERRED, documented
    /// on `AttrType::LabelKeyedStringDict`). `providers=` is accepted for the schema but not enforced this wave.
    fn label_keyed_string_dict<'v>(
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
        #[starlark(require = named)] providers: Option<Value<'v>>,
        #[starlark(require = named)] default: Option<Value<'v>>,
        #[starlark(require = named)] doc: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<AttrTypeValue> {
        let _ = (providers, default, doc, extra);
        Ok(AttrTypeValue { code: AttrType::LabelKeyedStringDict.code(), allow_files: None, providers: Vec::new(), mandatory: parse_mandatory(mandatory), default: None })
    }
}

/// How the BUILD-eval `glob()` builtin is serviced (T20 TF-unblocker A — the two-pass Globber). Owned data
/// (no borrows) so it lives inside the `ProvidesStaticType` `TargetRegistry`.
#[derive(Default)]
pub(crate) enum GlobMode {
    /// No globber wired — a `glob()` call is a fail-closed error (the plain `evaluate_build` entry point).
    #[default]
    Unsupported,
    /// COLLECT pass: each `glob()` records its spec here and returns []; the caller resolves them.
    Collect(RefCell<Vec<GlobSpec>>),
    /// RESOLVED pass: each `glob()` returns the pre-resolved sorted file list for its exact spec.
    Resolved(Vec<(GlobSpec, Vec<String>)>),
}

/// Accumulates the targets a BUILD file instantiates. Installed in `Evaluator::extra` so the `target()`
/// builtin and a `RuleProxy`'s `invoke` (neither can capture state) can record into it. Also carries the
/// [`GlobMode`] so the `glob()` builtin (likewise a capture-less `fn`) reaches its globber.
#[derive(Default, ProvidesStaticType)]
pub(crate) struct TargetRegistry {
    pub(crate) targets: RefCell<Vec<TargetDecl>>,
    pub(crate) globs: GlobMode,
    /// The live-module bridge (T20 select): a BUILD file CALLS loaded functions — a macro, or a
    /// crate_universe-style `constraint_values = triple_to_constraint_set(...)` from a loaded rules_rust
    /// module. Since `eval.extra` holds ONE value, the TargetRegistry carries the bridge so a `LoadedFunction`
    /// invoke resolves the real callable from its defining module's cached frozen module (the same mechanism
    /// `ActionRegistry` uses during rule eval). `None` for entry points that never call a loaded function.
    pub(crate) bridge: Option<crate::bridge::ModuleBridge>,
}

/// Record a native-rule-shaped target into the BUILD registry (`toolchain_type`/`toolchain`, C6): kind + name
/// + attrs, NO rule origin (these are native declarations razel resolves structurally, not via a rule impl).
/// Fail-closed on a duplicate name (a package is keyed by name).
fn record_native_target(eval: &mut Evaluator, kind: &str, name: String, attrs: Vec<(String, BzlValue)>) -> anyhow::Result<NoneType> {
    let reg = eval
        .extra
        .and_then(|e| e.downcast_ref::<TargetRegistry>())
        .ok_or_else(|| anyhow::anyhow!("{kind}() can only be called from a BUILD file"))?;
    if reg.targets.borrow().iter().any(|t| t.name == name) {
        return Err(anyhow::anyhow!("duplicate target name '{name}' in package"));
    }
    let mut attrs = attrs;
    attrs.sort_by(|a, b| a.0.cmp(&b.0));
    reg.targets.borrow_mut().push(TargetDecl { kind: kind.to_owned(), name, attrs, origin: None });
    Ok(NoneType)
}

#[starlark_module]
pub(crate) fn build_globals(builder: &mut GlobalsBuilder) {
    /// `toolchain_type(name = ...)` — declare a toolchain TYPE target (C6, native). Its label
    /// (`//pkg:name`) is the key `rule(toolchains=[…])` requests and `ctx.toolchains[…]` is keyed by.
    fn toolchain_type<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] visibility: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let _ = visibility; // common implicit attr (C7) — accepted; toolchain targets are resolution-visible
        record_native_target(eval, "toolchain_type", name, Vec::new())
    }

    /// `toolchain(name = ..., toolchain = ":impl", toolchain_type = ":type")` — register one toolchain (C6,
    /// native): it binds a toolchain TYPE to an implementation target. Resolution demands the impl target,
    /// analyzes it, and extracts its `ToolchainInfo`.
    fn toolchain<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] toolchain: String,
        #[starlark(require = named)] toolchain_type: String,
        #[starlark(require = named)] visibility: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let _ = visibility;
        record_native_target(
            eval,
            "toolchain",
            name,
            vec![
                ("toolchain".to_owned(), BzlValue::Str(toolchain)),
                ("toolchain_type".to_owned(), BzlValue::Str(toolchain_type)),
            ],
        )
    }

    /// `alias(name = ..., actual = "//label", visibility = [...])` — a native forwarding target (Bazel has
    /// `alias` as a builtin, so a BUILD calling it must load under BOTH tools). Analysis re-publishes the
    /// `actual` target's providers VERBATIM and threads its dep-output chaining, so a dependent sees `actual`
    /// exactly as if it depended on it directly. LANGUAGE-AGNOSTIC: it forwards ANY providers (nothing here
    /// assumes rust — the hub for the vendored crates uses it, but non-rust targets will too). Recorded with
    /// NO rule origin (like `toolchain`); the analysis phase resolves `actual` structurally. The alias's OWN
    /// `visibility` governs who may depend on the alias; `actual`'s own visibility is enforced at the alias→
    /// actual edge (a private cross-package `actual` is still a typed error).
    fn alias<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] actual: String,
        #[starlark(require = named)] visibility: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let mut attrs = vec![("actual".to_owned(), BzlValue::Str(actual))];
        if let Some(v) = visibility {
            attrs.push(("visibility".to_owned(), convert(v, None).map_err(|e| anyhow::anyhow!("alias visibility: {e:?}"))?));
        }
        record_native_target(eval, "alias", name, attrs)
    }

    /// `config_setting(name, constraint_values = [], values = {}, define_values = {}, flag_values = {},
    /// visibility = …)` — declare a Bazel `config_setting` (T20 select, native): a target that a `select({...})`
    /// condition names, evaluating to a match/no-match against the resolving target's configuration + the host
    /// platform's constraint set (razel-analysis). v1 slice: `constraint_values` (constraint_value labels) +
    /// `values` (the string dict — analysis supports `cpu`/`compilation_mode`, an unknown key is fail-closed
    /// there) are load-bearing; `define_values`/`flag_values` are ACCEPTED but fail-closed on USE (razel does
    /// not evaluate `--define`/build-setting flags in v1 — a select actually decided by one errors at analysis,
    /// never a silent no-op). Recorded with NO rule origin (a native decl razel resolves structurally, like
    /// `toolchain_type`); the config-match computation is analysis.
    fn config_setting<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] constraint_values: Option<Value<'v>>,
        #[starlark(require = named)] values: Option<Value<'v>>,
        #[starlark(require = named)] define_values: Option<Value<'v>>,
        #[starlark(require = named)] flag_values: Option<Value<'v>>,
        #[starlark(require = named)] visibility: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let mut attrs: Vec<(String, BzlValue)> = Vec::new();
        for (aname, av) in [
            ("constraint_values", constraint_values),
            ("values", values),
            ("define_values", define_values),
            ("flag_values", flag_values),
            ("visibility", visibility),
        ] {
            if let Some(v) = av {
                if !v.is_none() {
                    attrs.push((aname.to_owned(), convert(v, None).map_err(|e| anyhow::anyhow!("config_setting {aname}: {e:?}"))?));
                }
            }
        }
        record_native_target(eval, "config_setting", name, attrs)
    }

    /// `constraint_setting(name, default_constraint_value = None, visibility = …)` — declare a Bazel
    /// constraint_setting (T20 select, native): an IDENTITY target naming a dimension (`@platforms//cpu:cpu`).
    /// razel's thin host-only constraint model matches by LABEL (a platform either carries a constraint_value
    /// label or not), so the setting is recorded for legibility + so the @platforms/rules_rust BUILDs that
    /// declare it LOAD; nothing here computes over it. `default_constraint_value` is accepted (not consumed in
    /// host-only v1).
    fn constraint_setting<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] default_constraint_value: Option<Value<'v>>,
        #[starlark(require = named)] visibility: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let _ = (default_constraint_value, visibility);
        record_native_target(eval, "constraint_setting", name, Vec::new())
    }

    /// `constraint_value(name, constraint_setting = …, visibility = …)` — declare a Bazel constraint_value
    /// (T20 select, native): an IDENTITY target (`@platforms//cpu:aarch64`). Its LABEL is the token the
    /// host platform's constraint set and a `config_setting.constraint_values` list carry; razel's thin model
    /// matches on that label string. Recorded for legibility; `constraint_setting` is accepted (not consumed).
    fn constraint_value<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] constraint_setting: Option<Value<'v>>,
        #[starlark(require = named)] visibility: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let _ = (constraint_setting, visibility);
        record_native_target(eval, "constraint_value", name, Vec::new())
    }

    /// `target(kind = ..., name = ..., **attrs)` — record a target instance with NO rule origin (the spike
    /// placeholder; analysis fails closed on it). The `rule()`-defined callable is the real instantiation path.
    fn target<'v>(
        #[starlark(require = named)] kind: String,
        #[starlark(require = named)] name: String,
        #[starlark(kwargs)] attrs: DictRef<'v>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<TargetRegistry>())
            .ok_or_else(|| anyhow::anyhow!("target() can only be called from a BUILD file"))?;
        // A package is keyed by target name: a duplicate is an error, never a silent last-wins.
        let is_dup = reg.targets.borrow().iter().any(|t| t.name == name);
        if is_dup && !cfg!(feature = "mutant_package_allow_dup_names") {
            return Err(anyhow::anyhow!("duplicate target name '{name}' in package"));
        }
        let mut pairs: Vec<(String, BzlValue)> = Vec::new();
        for (k, v) in attrs.iter() {
            let key = k
                .unpack_str()
                .ok_or_else(|| anyhow::anyhow!("attribute name must be a string"))?
                .to_owned();
            let val = convert(v, None).map_err(|e| anyhow::anyhow!("attribute '{key}': {e:?}"))?;
            pairs.push((key, val));
        }
        pairs.sort_by(|a, b| a.0.cmp(&b.0)); // canonical: name-sorted attrs → order-insensitive value
        reg.targets.borrow_mut().push(TargetDecl { kind, name, attrs: pairs, origin: None });
        Ok(NoneType)
    }

    /// `glob(include, exclude = [], exclude_directories = 1, allow_empty = <False>)` — Bazel's source-file
    /// globber (T20 TF-unblocker A). Runs in the two-pass Globber shape (the PACKAGE node owns resolution):
    /// the COLLECT pass records this call's [`GlobSpec`] and returns []; the RESOLVED pass returns the
    /// pre-resolved sorted, package-relative file list. `include`/`exclude` are lists of package-relative
    /// patterns (`*` within a segment, `**` across segments); `exclude_directories` (int 1/0, default 1)
    /// keeps only files; `allow_empty` (default False — Bazel 7+ `--incompatible_disallow_empty_glob`) makes
    /// an empty result a typed error (enforced in the resolver, which knows the match set). Fail-closed on a
    /// non-list pattern arg and on the plain `evaluate_build` entry point (no globber wired).
    fn glob<'v>(
        #[starlark(require = pos)] include: Value<'v>,
        #[starlark(require = named)] exclude: Option<Value<'v>>,
        #[starlark(require = named)] exclude_directories: Option<Value<'v>>,
        #[starlark(require = named)] allow_empty: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<Value<'v>> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<TargetRegistry>())
            .ok_or_else(|| anyhow::anyhow!("glob() can only be called from a BUILD file"))?;
        let spec = GlobSpec {
            include: parse_pattern_list(include, "glob() include")?,
            exclude: match exclude {
                None => Vec::new(),
                Some(v) if v.is_none() => Vec::new(),
                Some(v) => parse_pattern_list(v, "glob() exclude")?,
            },
            // Bazel `exclude_directories` is an INT (1 = exclude dirs, the default; 0 = include them). Accept
            // an int (1/0) or a bool defensively; anything else keeps the default (exclude dirs).
            exclude_directories: match exclude_directories {
                None => true,
                Some(v) => {
                    if let Some(b) = v.unpack_bool() {
                        b
                    } else if let Ok(Some(i)) = i64::unpack_value(v) {
                        i != 0
                    } else {
                        true
                    }
                }
            },
            allow_empty: allow_empty.and_then(|v| v.unpack_bool()).unwrap_or(false),
        };
        match &reg.globs {
            GlobMode::Unsupported => Err(anyhow::anyhow!(
                "glob() is unsupported in this evaluation entry point (no globber wired) — the PACKAGE node's glob-aware path resolves globs"
            )),
            GlobMode::Collect(sink) => {
                sink.borrow_mut().push(spec);
                Ok(eval.heap().alloc(Vec::<Value>::new())) // collect pass yields [] so eval completes
            }
            GlobMode::Resolved(map) => {
                let files = map.iter().find(|(s, _)| *s == spec).map(|(_, f)| f).ok_or_else(|| {
                    // A resolved-pass call whose spec was not collected is a collect/resolve mismatch — loud,
                    // never a silent empty (that would drop sources).
                    anyhow::anyhow!("glob() spec was not resolved (collect/resolve mismatch): {spec:?}")
                })?;
                Ok(eval.heap().alloc(files.iter().map(|f| eval.heap().alloc(f.as_str())).collect::<Vec<_>>()))
            }
        }
    }
}

/// Parse a `glob()` pattern argument: a list of strings (fail-closed on any non-list / non-string entry).
fn parse_pattern_list(v: Value, what: &str) -> anyhow::Result<Vec<String>> {
    let list = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("{what} must be a list of pattern strings"))?;
    list.iter()
        .map(|i| i.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("{what} entries must be strings")))
        .collect()
}

