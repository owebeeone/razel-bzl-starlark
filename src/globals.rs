use razel_bzl_api::{ActionTemplate, AttrType, BzlValue, TargetDecl};
use starlark::environment::GlobalsBuilder;
use starlark::eval::Evaluator;
use starlark::starlark_module;
use starlark::values::dict::DictRef;
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{ProvidesStaticType, Value, ValueLike};
use std::cell::RefCell;

use crate::convert::convert;
use crate::values::{AttrTypeValue, Provider, RuleValue, RuleValueGen};

// ──────────────── globals ────────────────
// The per-phase Globals are NAMED, precomputed and digested in `envs` (lockdown §3) — the ad-hoc
// rebuilt-per-call `bzl_globals()` is gone. The registrar fns below stay here (they own the builtins).

/// Accumulates the actions a rule's impl declares (via `declare_action`). Installed in `eval.extra` during
/// `evaluate_rule` so the builtin (a `fn`, can't capture) records into it; collected into the `RuleResult`.
#[derive(Default, ProvidesStaticType)]
pub(crate) struct ActionRegistry {
    pub(crate) actions: RefCell<Vec<ActionTemplate>>,
}

#[starlark_module]
pub(crate) fn action_global(builder: &mut GlobalsBuilder) {
    /// `declare_action(mnemonic=, argv=[...], outputs=[...], inputs=[...])` — a rule impl declares an action the
    /// EXECUTION phase will run. SPIKE: a placeholder for `ctx.actions.run(...)` (the object-method form is a
    /// fidelity refinement); records an `ActionTemplate`. Fail-closed: callable only inside a rule impl.
    fn declare_action<'v>(
        #[starlark(require = named)] mnemonic: String,
        #[starlark(require = named)] argv: Value<'v>,
        #[starlark(require = named)] outputs: Value<'v>,
        #[starlark(require = named)] inputs: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ActionRegistry>())
            .ok_or_else(|| anyhow::anyhow!("declare_action can only be called inside a rule implementation"))?;
        let str_list = |v: Value<'v>, what: &str| -> anyhow::Result<Vec<String>> {
            let l = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("{what} must be a list of strings"))?;
            l.iter()
                .map(|i| i.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("{what} entries must be strings")))
                .collect()
        };
        let argv = str_list(argv, "argv")?;
        let mut outputs = str_list(outputs, "outputs")?;
        outputs.sort();
        outputs.dedup();
        let mut inputs = match inputs {
            Some(v) => str_list(v, "inputs")?,
            None => Vec::new(),
        };
        inputs.sort();
        inputs.dedup();
        reg.actions.borrow_mut().push(ActionTemplate { mnemonic, argv, env: Vec::new(), inputs, outputs });
        Ok(NoneType)
    }

    /// `write_file(output=, content=)` — a rule impl declares a no-subprocess content-write action (Bazel's
    /// `ctx.actions.write` / `FileWriteAction`). It records an `ActionTemplate` whose content rides in the
    /// FROZEN `argv` dimension by the shared convention `mnemonic="WriteFile"`, `argv=["write_file", content]`
    /// — so the declared content is part of the action's 8-dim fingerprint with NO new fingerprint dimension,
    /// and `razel-exec-api`'s `WriteStrategy` (which owns the matching convention) emits the output from that
    /// argv. Content is thus real action DATA end-to-end (edit → re-run, identical → early-cut). Fail-closed:
    /// callable only inside a rule impl; `content` must be a string (v1: UTF-8 content only — a bytes channel
    /// is a later additive refinement).
    fn write_file<'v>(
        #[starlark(require = named)] output: String,
        #[starlark(require = named)] content: String,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ActionRegistry>())
            .ok_or_else(|| anyhow::anyhow!("write_file can only be called inside a rule implementation"))?;
        reg.actions.borrow_mut().push(ActionTemplate {
            // The shared write-action convention (mirrored, by value, in razel-exec-api::conformance —
            // WRITE_FILE_MNEMONIC / WRITE_FILE_ARGV0 / write_file_argv). Kept in lockstep the same way the
            // fingerprint and the SpawnRequest both read `argv` independently: one convention, two readers.
            mnemonic: "WriteFile".to_string(),
            argv: vec!["write_file".to_string(), content],
            env: Vec::new(),
            inputs: Vec::new(),
            outputs: vec![output],
        });
        Ok(NoneType)
    }
}

#[starlark_module]
pub(crate) fn rule_global(builder: &mut GlobalsBuilder) {
    /// `rule(implementation = <fn>, attrs = {name: attr.<type>()}, toolchains = ["//type"])` — define a rule.
    /// Records the attr schema + the required toolchain TYPE ids; validates an implementation is present.
    /// Running the impl (+ resolving the toolchains) is analysis.
    fn rule<'v>(
        #[starlark(require = named)] implementation: Value<'v>,
        #[starlark(require = named)] attrs: Option<DictRef<'v>>,
        #[starlark(require = named)] toolchains: Option<Value<'v>>,
    ) -> anyhow::Result<RuleValue<'v>> {
        if implementation.is_none() {
            return Err(anyhow::anyhow!("rule() requires an 'implementation' function"));
        }
        let mut schema: Vec<(String, u8)> = Vec::new();
        if let Some(d) = attrs {
            for (k, v) in d.iter() {
                let key = k
                    .unpack_str()
                    .ok_or_else(|| anyhow::anyhow!("attr name must be a string"))?
                    .to_owned();
                let at = v
                    .downcast_ref::<AttrTypeValue>()
                    .ok_or_else(|| anyhow::anyhow!("attr '{key}' must be an attr.* type"))?;
                schema.push((key, at.code));
            }
        }
        schema.sort_by(|a, b| a.0.cmp(&b.0));
        let mut required: Vec<String> = match toolchains {
            None => Vec::new(),
            Some(v) => {
                let list = ListRef::from_value(v)
                    .ok_or_else(|| anyhow::anyhow!("rule() toolchains must be a list of type strings"))?;
                list.iter()
                    .map(|i| i.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("toolchain type must be a string")))
                    .collect::<anyhow::Result<Vec<String>>>()?
            }
        };
        required.sort();
        required.dedup();
        Ok(RuleValueGen { implementation, attrs: schema, toolchains: required })
    }
}

#[starlark_module]
pub(crate) fn provider_global(builder: &mut GlobalsBuilder) {
    /// `provider(name, fields = [..])` — declare a provider type. SPIKE: identity is the explicit `name`
    /// (so it is stable across the per-target re-evaluations that the analysis phase performs).
    fn provider<'v>(
        #[starlark(require = pos)] name: String,
        #[starlark(require = named)] fields: Option<Value<'v>>,
    ) -> anyhow::Result<Provider> {
        let field_names = match fields {
            None => Vec::new(),
            Some(v) => {
                let list = ListRef::from_value(v)
                    .ok_or_else(|| anyhow::anyhow!("provider() fields must be a list of strings"))?;
                list.iter()
                    .map(|item| {
                        item.unpack_str()
                            .map(|s| s.to_owned())
                            .ok_or_else(|| anyhow::anyhow!("provider() field names must be strings"))
                    })
                    .collect::<anyhow::Result<Vec<String>>>()?
            }
        };
        Ok(Provider { id: name, fields: field_names })
    }
}

#[starlark_module]
pub(crate) fn attr_namespace(builder: &mut GlobalsBuilder) {
    fn int() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::Int.code() })
    }
    fn string() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::String.code() })
    }
    fn bool() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::Bool.code() })
    }
    fn label() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::Label.code() })
    }
    fn label_list() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::LabelList.code() })
    }
    fn string_list() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::StringList.code() })
    }
}

/// Accumulates the targets a BUILD file instantiates. Installed in `Evaluator::extra` so the `target()`
/// builtin and a `RuleProxy`'s `invoke` (neither can capture state) can record into it.
#[derive(Default, ProvidesStaticType)]
pub(crate) struct TargetRegistry {
    pub(crate) targets: RefCell<Vec<TargetDecl>>,
}

#[starlark_module]
pub(crate) fn build_globals(builder: &mut GlobalsBuilder) {
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
            let val = convert(v).map_err(|e| anyhow::anyhow!("attribute '{key}': {e:?}"))?;
            pairs.push((key, val));
        }
        pairs.sort_by(|a, b| a.0.cmp(&b.0)); // canonical: name-sorted attrs → order-insensitive value
        reg.targets.borrow_mut().push(TargetDecl { kind, name, attrs: pairs, origin: None });
        Ok(NoneType)
    }
}

