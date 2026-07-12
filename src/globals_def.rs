//! DEF-PHASE (load-time) builtins that DECLARE analysis constructs — build settings (`config.*`), aspects
//! (`aspect()`), configuration transitions (`transition()`), late-bound config fields
//! (`configuration_field()`), and toolchain-type references (`config_common.toolchain_type()`). Real-world
//! rulesets (rules_rust + its bazel_skylib/rules_cc transitive closure) DECLARE these at MODULE scope, so
//! they must EVALUATE when a `.bzl` loads. Their ANALYSIS behavior (configuring a build setting, running an
//! aspect, applying a transition) is R-analyze/deferred: each ctor returns an OPAQUE marker value that
//! carries just enough to re-declare, and FAILS CLOSED if actually driven at analysis (never a silent
//! no-op — RazelRulesRustCompatPlan §3 fail-closed enumeration). Only what the demanded closure hits is
//! enabled here; nothing speculative.

use allocative::Allocative;
use starlark::environment::GlobalsBuilder;
use starlark::starlark_module;
use starlark::starlark_simple_value;
use starlark::values::dict::DictRef;
use starlark::values::{starlark_value, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Value, ValueLike};
use std::fmt;

use crate::values_label::LabelValue;

fn unpack_flag(v: Option<Value>) -> bool {
    v.and_then(|val| val.unpack_bool()).unwrap_or(false)
}

// ──────────────── config.* — build-setting descriptors ────────────────

/// An opaque build-setting descriptor produced by `config.int()/.bool()/.string()/.string_list()`. Bazel's
/// build_setting rules (`bazel_skylib//rules:common_settings.bzl` — `int_flag`, `bool_flag`, `string_flag`,
/// `string_list_flag`, …) pass one to `rule(build_setting = …)`. razel carries the descriptor so the
/// `rule()` call EVALUATES; the setting's CONFIGURATION behavior (command-line flags, `ctx.build_setting_value`,
/// transitions) is analysis-time and DEFERRED. A rule actually CONFIGURED as a build setting fails closed at
/// analysis, never silently. `kind`: 0=int 1=bool 2=string 3=string_list.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct BuildSettingValue {
    pub(crate) kind: u8,
    pub(crate) flag: bool,
    pub(crate) repeatable: bool,
}
starlark_simple_value!(BuildSettingValue);
impl fmt::Display for BuildSettingValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<build_setting kind={} flag={}>", self.kind, self.flag)
    }
}
#[starlark_value(type = "build_setting")]
impl<'v> StarlarkValue<'v> for BuildSettingValue {}

#[starlark_module]
pub(crate) fn config_namespace(builder: &mut GlobalsBuilder) {
    /// `config.int(flag = False)` — an int-typed build setting descriptor.
    fn int<'v>(#[starlark(require = named)] flag: Option<Value<'v>>) -> anyhow::Result<BuildSettingValue> {
        Ok(BuildSettingValue { kind: 0, flag: unpack_flag(flag), repeatable: false })
    }
    /// `config.bool(flag = False)` — a bool-typed build setting descriptor.
    fn bool<'v>(#[starlark(require = named)] flag: Option<Value<'v>>) -> anyhow::Result<BuildSettingValue> {
        Ok(BuildSettingValue { kind: 1, flag: unpack_flag(flag), repeatable: false })
    }
    /// `config.string(flag = False)` — a string-typed build setting descriptor.
    fn string<'v>(#[starlark(require = named)] flag: Option<Value<'v>>) -> anyhow::Result<BuildSettingValue> {
        Ok(BuildSettingValue { kind: 2, flag: unpack_flag(flag), repeatable: false })
    }
    /// `config.string_list(flag = False, repeatable = False)` — a string-list-typed build setting descriptor.
    fn string_list<'v>(
        #[starlark(require = named)] flag: Option<Value<'v>>,
        #[starlark(require = named)] repeatable: Option<Value<'v>>,
    ) -> anyhow::Result<BuildSettingValue> {
        Ok(BuildSettingValue { kind: 3, flag: unpack_flag(flag), repeatable: unpack_flag(repeatable) })
    }
}

// ──────────────── config_common.toolchain_type — a toolchain-type requirement ────────────────

/// An opaque toolchain-type REQUIREMENT from `config_common.toolchain_type(label, mandatory = …)`. Bazel
/// rules pass these in `rule(toolchains = [...])` alongside bare type-label strings (rules_cc's
/// `use_cc_toolchain()` returns one). razel carries the type label so the enclosing `rule()`/helper call
/// EVALUATES; the resolution behavior (selecting a matching toolchain) is analysis-time and DEFERRED.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct ToolchainTypeReq {
    pub(crate) label: String,
    pub(crate) mandatory: bool,
}
starlark_simple_value!(ToolchainTypeReq);
impl fmt::Display for ToolchainTypeReq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<toolchain_type {} mandatory={}>", self.label, self.mandatory)
    }
}
#[starlark_value(type = "ToolchainTypeRequirement")]
impl<'v> StarlarkValue<'v> for ToolchainTypeReq {}

#[starlark_module]
pub(crate) fn config_common_namespace(builder: &mut GlobalsBuilder) {
    /// `config_common.toolchain_type(name, mandatory = True)` — a toolchain-type requirement descriptor.
    /// `name` is a `Label` or a label string; `mandatory` defaults to True (Bazel). Carries just the type
    /// label + the flag (analysis resolution deferred).
    fn toolchain_type<'v>(
        #[starlark(require = pos)] name: Value<'v>,
        #[starlark(require = named)] mandatory: Option<Value<'v>>,
    ) -> anyhow::Result<ToolchainTypeReq> {
        let label = if let Some(l) = name.downcast_ref::<LabelValue>() {
            l.display.clone()
        } else if let Some(s) = name.unpack_str() {
            s.to_owned()
        } else {
            return Err(anyhow::anyhow!("config_common.toolchain_type() expects a Label or a label string"));
        };
        Ok(ToolchainTypeReq { label, mandatory: mandatory.and_then(|v| v.unpack_bool()).unwrap_or(true) })
    }
}

// ──────────────── coverage_common — the coverage instrumentation namespace ────────────────

/// An opaque `InstrumentedFilesInfo`-shaped marker produced by `coverage_common.instrumented_files_info(...)`.
/// Bazel predeclares `coverage_common` as a .bzl builtin; rules_rust's `rust/private/rustc.bzl:1898` builds
/// an InstrumentedFilesInfo inside the library/binary impl and returns it in the provider list. razel carries
/// an OPAQUE marker so the NAME resolves at load AND an analysis call does not crash — coverage itself
/// (instrumentation, `--collect_code_coverage`) is DEFERRED (row 12), so the marker carries nothing. It is a
/// provider-INSTANCE-shaped value only in that a rule impl may put it in its return list; its projection to a
/// codec-neutral provider is an R-analyze concern (this wave's probe dies earlier, at cc_common).
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct InstrumentedFilesInfoValue;
starlark_simple_value!(InstrumentedFilesInfoValue);
impl fmt::Display for InstrumentedFilesInfoValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<InstrumentedFilesInfo>")
    }
}
#[starlark_value(type = "InstrumentedFilesInfo")]
impl<'v> StarlarkValue<'v> for InstrumentedFilesInfoValue {}

// ──────────────── aspect() / transition() / configuration_field() — deferred def-phase markers ────────────

/// The reserved sentinel field names marking a codec `struct` as a re-materializable [`DeferredMarker`]. A
/// deferred marker (an `aspect()`/`transition()`/`configuration_field()` result) has no live representation
/// that crosses the `BZL_LOAD` node boundary; rather than a NEW frozen codec tag, it rides the EXISTING tag-9
/// struct carrier under these sentinel keys (the `_razel_`-prefix makes a real user struct collision
/// astronomically unlikely). `convert` maps the live marker to this struct; `alloc` recognizes it and
/// re-materializes a fail-closed live marker (never an inert struct — a driven marker fails closed).
pub(crate) const DEFERRED_MARKER_KIND_FIELD: &str = "_razel_deferred_marker_kind";
pub(crate) const DEFERRED_MARKER_DETAIL_FIELD: &str = "_razel_deferred_marker_detail";

/// An opaque DEFERRED analysis-declaration marker: the result of `aspect()`, `transition()`, or
/// `configuration_field()` (T20 R-load, row 5 "parse-level first"). rules_rust DECLARES these at module scope
/// (`rust_analyzer_aspect = aspect(...)`, `_rust_static_library_transition = transition(...)`, `default =
/// configuration_field(...)`), and defs.bzl RE-EXPORTS the aspects — so the value must both EVALUATE at load
/// and cross the load boundary. It carries a `kind` (aspect/transition/configuration_field) + an opaque
/// `detail` (impl name or fragment:name) so distinct declarations digest distinctly. It has NO methods and NO
/// attributes: any analysis-time USE (running the aspect, applying the transition, reading the late-bound
/// field) is a fail-closed attribute error — coverage/transitions/aspects are DEFERRED (row 12), never a
/// silent no-op.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct DeferredMarker {
    pub(crate) kind: String,
    pub(crate) detail: String,
}
starlark_simple_value!(DeferredMarker);
impl fmt::Display for DeferredMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{} {}>", self.kind, self.detail)
    }
}
#[starlark_value(type = "deferred_marker")]
impl<'v> StarlarkValue<'v> for DeferredMarker {}

/// A best-effort opaque token distinguishing one declaration from another (the impl function's rendered name,
/// else its type) — carried as the marker `detail` so two aspects/transitions with different impls digest
/// distinctly. Never load-bearing; purely for digest distinctness.
fn marker_detail(v: Option<Value>) -> String {
    match v {
        Some(val) => val.to_str(),
        None => String::new(),
    }
}

#[starlark_module]
pub(crate) fn def_markers_global(builder: &mut GlobalsBuilder) {
    /// `aspect(implementation, **kwargs)` — declare an aspect (T20 R-load). rules_rust's rust_analyzer/clippy/
    /// rustfmt/unpretty aspects are declared at module scope and RE-EXPORTED by defs.bzl. razel returns an
    /// opaque [`DeferredMarker`]; running the aspect is DEFERRED (row 12). All kwargs are accepted + ignored.
    fn aspect<'v>(
        #[starlark(require = named)] implementation: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<DeferredMarker> {
        let _ = extra;
        Ok(DeferredMarker { kind: "aspect".to_owned(), detail: marker_detail(implementation) })
    }

    /// `transition(implementation, inputs, outputs)` — declare a configuration transition (T20 R-load).
    /// rules_rust declares static/shared-library transitions (private, consumed by `rule(cfg=…)`). razel
    /// returns an opaque [`DeferredMarker`]; applying the transition is DEFERRED (row 12).
    fn transition<'v>(
        #[starlark(require = named)] implementation: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<DeferredMarker> {
        let _ = extra;
        Ok(DeferredMarker { kind: "transition".to_owned(), detail: marker_detail(implementation) })
    }

    /// `configuration_field(fragment, name)` — a late-bound default drawing from a configuration fragment
    /// (T20 R-load). rules_rust uses it for `attr.label(default = configuration_field("coverage", …))`.
    /// razel returns an opaque [`DeferredMarker`]; the late-bound resolution is DEFERRED (row 12).
    fn configuration_field<'v>(
        #[starlark(require = named)] fragment: Option<Value<'v>>,
        #[starlark(require = named)] name: Option<Value<'v>>,
        #[starlark(kwargs)] extra: DictRef<'v>,
    ) -> anyhow::Result<DeferredMarker> {
        let _ = extra;
        let detail = format!("{}:{}", marker_detail(fragment), marker_detail(name));
        Ok(DeferredMarker { kind: "configuration_field".to_owned(), detail })
    }
}

#[starlark_module]
pub(crate) fn coverage_common_namespace(builder: &mut GlobalsBuilder) {
    /// `coverage_common.instrumented_files_info(ctx, *, source_attributes=[], dependency_attributes=[],
    /// extensions=None, …)` — build an InstrumentedFilesInfo. razel returns an OPAQUE marker (coverage is
    /// deferred, row 12); it accepts and ignores the kwargs so a real rule impl's call EVALUATES.
    fn instrumented_files_info<'v>(
        #[starlark(require = pos)] ctx: Option<Value<'v>>,
        #[starlark(kwargs)] extra: starlark::values::dict::DictRef<'v>,
    ) -> anyhow::Result<InstrumentedFilesInfoValue> {
        let _ = (ctx, extra);
        Ok(InstrumentedFilesInfoValue)
    }
}
