use razel_bzl_api::{
    BzlError, BzlEvaluator, BzlModule, BzlValue, DepProviders, Dialect as ApiDialect, EvalEnv, LoadKind,
    PredeclaredEnvId, ProviderId, ProviderInstance, ResolvedToolchain, RuleResult, StarlarkSemanticsId,
    TargetDecl, TypeOptions,
};
use starlark::environment::{FrozenModule, Module};
use starlark::eval::{Evaluator, ReturnFileLoader};
use starlark::syntax::{AstModule, Dialect};
use starlark::values::dict::AllocDict;
use starlark::values::list::ListRef;
use starlark::values::structs::AllocStruct;
use starlark::values::{Value, ValueLike};
use std::collections::{HashMap, HashSet};

use crate::convert::{alloc, alloc_provider_instance, build_frozen, convert, decode_schema, index_providers};
use crate::envs::{env_build_bzl, env_build_file, PhaseEnv};
use crate::globals::{ActionRegistry, TargetRegistry};
use crate::values::{ProviderInstanceValue, RuleValue};
use crate::StarlarkEvaluator;

fn parse(name: &str, source: &str, dialect: &Dialect) -> Result<AstModule, BzlError> {
    AstModule::parse(name, source.to_owned(), dialect).map_err(|e| BzlError::Parse { detail: e.to_string() })
}

/// Select the named phase env an [`EvalEnv`] requests — the kind→env mapping of §1 (key fact A), applied
/// FAIL-CLOSED over what v1 has built: only `(Build{is_prelude:false}, Bzl)` under the single v1 semantics
/// row + v1 TypeOptions sentinel evaluates; every other row is a typed error, never a shared default env.
fn select_bzl_env(env: &EvalEnv) -> Result<&'static PhaseEnv, BzlError> {
    if env.semantics != StarlarkSemanticsId::v1() {
        return Err(BzlError::Unsupported {
            what: "starlark semantics row (v1 registers the single default row — keyed selection with one entry)"
                .to_owned(),
        });
    }
    if env.type_options != TypeOptions::default() {
        return Err(BzlError::Unsupported {
            what: "non-default TypeOptions (the load-time type-check pass is not built in v1)".to_owned(),
        });
    }
    match (env.load_kind, env.dialect) {
        (LoadKind::Build { is_prelude: false }, ApiDialect::Bzl) => Ok(env_build_bzl()),
        (LoadKind::Build { is_prelude: true }, _) => Err(BzlError::Unsupported {
            what: "BUILD prelude evaluation (prelude re-export is not built in v1)".to_owned(),
        }),
        (_, ApiDialect::Scl) => Err(BzlError::Unsupported {
            what: "the .scl environment (EnvScl is not built in v1; .scl is semantics-disabled)".to_owned(),
        }),
        (LoadKind::Builtins, _) | (LoadKind::Bzlmod, _) | (LoadKind::BzlmodBootstrap, _) => {
            Err(BzlError::Unsupported {
                what: format!("the predeclared environment for {:?} (not built in v1)", env.load_kind),
            })
        }
    }
}

pub(crate) fn starlark_err(msg: String) -> starlark::Error {
    starlark::Error::new_other(anyhow::anyhow!(msg))
}

impl BzlEvaluator for StarlarkEvaluator {
    fn load_targets(&self, source: &str) -> Result<Vec<String>, BzlError> {
        // Parse-only load SCAN (dep discovery before any evaluation) — the permissive standard dialect is
        // deliberate: it must parse both `.bzl` and BUILD sources; the phase dialect gates real evaluation.
        let ast = parse("<load-scan>", source, &Dialect::Standard)?;
        Ok(ast.loads().into_iter().map(|l| l.module_id.to_owned()).collect())
    }

    fn predeclared_env_id(&self, kind: &LoadKind, dialect: ApiDialect) -> Result<PredeclaredEnvId, BzlError> {
        match (kind, dialect) {
            // BOTH Build{is_prelude:*} kinds SHARE EnvBuildBzl (R1) — the prelude bit is a LoadKind/key
            // bit, never an environment.
            (LoadKind::Build { .. }, ApiDialect::Bzl) => Ok(env_build_bzl().env_id),
            // Rows 3-6 have no built environment in v1 — fail closed, never a defaulted id.
            _ => Err(BzlError::Unsupported {
                what: format!("the predeclared environment for {kind:?}/{dialect:?} (not built in v1)"),
            }),
        }
    }

    fn evaluate(
        &self,
        env: &EvalEnv,
        module_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
    ) -> Result<BzlModule, BzlError> {
        let phase = select_bzl_env(env)?; // the NAMED row-1 env — fail-closed on any unbuilt row
        let ast = parse(module_name, source, &phase.dialect)?;
        // load()ed symbols are usable locally but are NOT re-exported (Bazel semantics) — collect their
        // local names so we can exclude them from this module's exports.
        let loaded_names: HashSet<String> =
            ast.loads().iter().flat_map(|l| l.symbols.keys().map(|k| k.to_string())).collect();
        let globals = &phase.globals; // EnvBuildBzl: standard + rule()/provider()/declare_action + attr

        // Rebuild each load() target as a FrozenModule, then index by target string for the loader.
        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(target, m)| build_frozen(m).map(|fm| (target.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };

        Module::with_temp_heap(|module| -> Result<BzlModule, BzlError> {
            {
                let mut eval = Evaluator::new(&module);
                eval.set_loader(&loader);
                eval.eval_module(ast, globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            // Decision H: a second same-name provider() reaching module scope is fail-closed at declaration
            // (the index result is unused here — the scan IS the collision check; aliasing stays legal).
            index_providers(&module, module_name)?;
            let mut bindings = Vec::new();
            for name in module.names() {
                let n = name.as_str();
                if n.starts_with('_') || loaded_names.contains(n) {
                    continue; // skip private + load()ed symbols; export only this module's own bindings
                }
                if let Some(v) = module.get(n) {
                    let mut bv = convert(v)?;
                    // Stamp a freshly-defined rule's identity (def-side has no origin yet). A re-exported
                    // loaded rule already carries its origin (name non-empty) — leave it.
                    if let BzlValue::Rule(rd) = &mut bv {
                        if rd.name.is_empty() {
                            rd.name = n.to_owned();
                            rd.bzl = module_name.to_owned();
                        }
                    }
                    bindings.push((n.to_owned(), bv));
                }
            }
            bindings.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(BzlModule { bindings })
        })
    }

    fn evaluate_build(
        &self,
        package_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
    ) -> Result<Vec<TargetDecl>, BzlError> {
        // Row 7, `EnvBuildFile`: the NAMED BUILD-file env (standard + the BUILD-only `target()` builtin)
        // under the def-less BUILD dialect — `def`/`lambda` in a BUILD now fail at PARSE (the spike's
        // admitted permissive-dialect gap is closed; separation is environmental, not runtime-only).
        let phase = env_build_file();
        let ast = parse(package_name, source, &phase.dialect)?;
        let globals = &phase.globals;

        // Rebuild each load() target as a FrozenModule, then index by target string for the loader — same
        // mechanism as `evaluate`; the BUILD's `load()`ed constants AND rule callables resolve through this.
        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(target, m)| build_frozen(m).map(|fm| (target.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };

        let registry = TargetRegistry::default();
        Module::with_temp_heap(|module| -> Result<Vec<TargetDecl>, BzlError> {
            {
                let mut eval = Evaluator::new(&module);
                eval.set_loader(&loader);
                eval.extra = Some(&registry); // target() and rule-callables record into this
                eval.eval_module(ast, globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            Ok(registry.targets.borrow().clone())
        })
    }

    fn evaluate_rule(
        &self,
        env: &EvalEnv,
        rule_source: &str,
        rule_module_name: &str,
        rule_name: &str,
        loaded: &[(String, BzlModule)],
        label: &str,
        attrs: &[(String, BzlValue)],
        deps: &[DepProviders],
        toolchains: &[ResolvedToolchain],
    ) -> Result<RuleResult, BzlError> {
        let phase = select_bzl_env(env)?; // the SAME row-1 env the module was loaded in
        let ast = parse(rule_module_name, rule_source, &phase.dialect)?;
        let globals = &phase.globals;

        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(t, m)| build_frozen(m).map(|fm| (t.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };

        let action_registry = ActionRegistry::default();
        Module::with_temp_heap(|module| -> Result<RuleResult, BzlError> {
            let mut eval = Evaluator::new(&module);
            eval.set_loader(&loader);
            eval.extra = Some(&action_registry); // declare_action (during the impl run below) records into this
            // Define the rule, its impl, and any providers (the impl is NOT run yet — it's just a function).
            eval.eval_module(ast, globals).map_err(|e| BzlError::Eval { detail: e.to_string() })?;

            // The rule + its live implementation function (live in THIS heap — no cross-heap frozen value).
            let rule_v = module
                .get(rule_name)
                .ok_or_else(|| BzlError::Eval { detail: format!("rule '{rule_name}' not found in {rule_module_name}") })?;
            let rule = RuleValue::from_value(rule_v)
                .ok_or_else(|| BzlError::Eval { detail: format!("'{rule_name}' is not a rule") })?;
            let impl_fn = rule.implementation.to_value();
            let schema = decode_schema(&rule.attrs)?;

            // Index this eval's live Provider values by identity — these key the per-dep `{Provider: instance}`
            // dicts, matching a dep's (codec-neutral) provider id back to THIS eval's provider object.
            // Fail-closed on a duplicate declaration (decision H — the silent last-wins is dead).
            let mut providers_by_id = index_providers(&module, rule_module_name)?;
            // Builtin providers (row-G `DefaultInfo`) are GLOBALS, not module bindings, so `index_providers`
            // (which scans module names) never sees them. Register the `DefaultInfo` identity so a
            // `dep[DefaultInfo]` in the impl re-keys through it (the key is a fresh Provider with the SAME
            // ProviderId — dict lookup rides ProviderId's derived Eq/Hash, so it matches the global the impl
            // references). A `.bzl` that also declares `DefaultInfo` keeps its own (`or_insert`).
            providers_by_id
                .entry(ProviderId::from_name(crate::globals::DEFAULT_INFO_NAME))
                .or_insert_with(|| module.heap().alloc(crate::globals::default_info_provider()));

            // Build ctx.attr: scalars alloc directly; label-typed attrs become a list of `{Provider: instance}`
            // dicts (one per dep), so the impl can do `for d in ctx.attr.deps: d[Provider].field`.
            let heap = module.heap();
            let mut attr_fields: Vec<(String, Value)> = Vec::new();
            for (aname, aty) in &schema {
                let aval = attrs.iter().find(|(n, _)| n == aname).map(|(_, v)| v);
                if aty.is_label() {
                    let labels: Vec<String> = if cfg!(feature = "mutant_rule_eval_drops_deps") {
                        // MUTANT: ignore the dependency edges → providers don't propagate (sum is wrong).
                        Vec::new()
                    } else {
                        match aval {
                            Some(BzlValue::List(items)) => items
                                .iter()
                                .filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None })
                                .collect(),
                            Some(BzlValue::Str(s)) => vec![s.clone()],
                            _ => Vec::new(),
                        }
                    };
                    let mut dep_vals: Vec<Value> = Vec::new();
                    for lbl in &labels {
                        // Fail-closed: a dep label referenced by an attr but NOT supplied in `deps` is a caller
                        // error (a declared dependency went unanalyzed) — never a silently-empty provider set.
                        let providers = match deps.iter().find(|d| &d.label == lbl) {
                            Some(d) => d.providers.as_slice(),
                            None if cfg!(feature = "mutant_rule_eval_absorbs_missing_dep") => &[],
                            None => {
                                return Err(BzlError::Eval {
                                    detail: format!("dependency '{lbl}' is referenced by an attr of '{rule_name}' but no providers were supplied for it"),
                                })
                            }
                        };
                        let mut entries: Vec<(Value, Value)> = Vec::new();
                        for pi in providers {
                            // dep[Provider] re-keying rides ProviderId's derived impls (the C2 funnel): a
                            // same-name identity differing in the bzl dim is a DIFFERENT provider — miss,
                            // fail closed — never fused by raw name.
                            let key = if cfg!(feature = "mutant_provider_compares_raw_name") {
                                // MUTANT: compare the raw name only — the §0.3 leak; a bzl-differing
                                // identity silently fuses with this module's provider.
                                providers_by_id.iter().find(|(k, _)| k.name() == pi.provider.name()).map(|(_, v)| *v)
                            } else {
                                providers_by_id.get(&pi.provider).copied()
                            };
                            let key = key.ok_or_else(|| BzlError::Eval {
                                detail: format!(
                                    "provider '{}' (on dep {lbl}) is not defined in this rule's .bzl",
                                    pi.provider.name()
                                ),
                            })?;
                            entries.push((key, alloc_provider_instance(&module, pi)?));
                        }
                        dep_vals.push(heap.alloc(AllocDict(entries)));
                    }
                    attr_fields.push((aname.clone(), heap.alloc(dep_vals)));
                } else {
                    let v = match aval {
                        Some(bv) => alloc(&module, bv)?,
                        None => Value::new_none(),
                    };
                    attr_fields.push((aname.clone(), v));
                }
            }
            let attr_struct = heap.alloc(AllocStruct(attr_fields));
            // ctx.toolchains: a map {toolchain_type -> toolchain_info} (empty until phase #4 supplies resolved
            // toolchains). A missing type indexes to a fail-closed error (native dict KeyError).
            let mut tc_entries: Vec<(Value, Value)> = Vec::new();
            for t in toolchains {
                // This path bypasses the providers_by_id re-keying (a toolchain_info is injected, not looked
                // up), so the cross-module-identity wall is checked HERE: a filled bzl dim has no live
                // representation under the v1 single-module cap — fail closed, never silently drop the dim.
                if t.info.provider.bzl().is_some() {
                    return Err(BzlError::Unsupported {
                        what: format!(
                            "toolchain_info provider '{}' with a cross-module identity (bzl dim) under the v1 single-module cap",
                            t.info.provider.name()
                        ),
                    });
                }
                tc_entries.push((heap.alloc(t.toolchain_type.as_str()), alloc_provider_instance(&module, &t.info)?));
            }
            let toolchains_dict = heap.alloc(AllocDict(tc_entries));
            let ctx = heap.alloc(AllocStruct([
                ("label".to_string(), heap.alloc(label)),
                ("attr".to_string(), attr_struct),
                ("toolchains".to_string(), toolchains_dict),
            ]));

            // Run the impl, then project the returned provider instances to codec-neutral data.
            let result = eval
                .eval_function(impl_fn, &[ctx], &[])
                .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            let list = ListRef::from_value(result)
                .ok_or_else(|| BzlError::Eval { detail: "a rule impl must return a list of providers".into() })?;
            let mut out = Vec::new();
            for item in list.iter() {
                let piv = ProviderInstanceValue::from_value(item)
                    .ok_or_else(|| BzlError::Eval { detail: "a rule impl must return provider instances".into() })?;
                let mut fields = Vec::new();
                for (n, v) in &piv.fields {
                    fields.push((n.clone(), convert(v.to_value())?));
                }
                out.push(ProviderInstance { provider: ProviderId::from_name(piv.provider_id.clone()), fields });
            }
            // Decision E: a duplicate provider key on the rule's RETURN is fail-closed with Bazel's exact
            // error shape (StarlarkRuleConfiguredTargetUtil.java:273-275) — checked over the insertion-ordered
            // result at the boundary, BEFORE the canonical sort. Never a silent last-wins.
            if cfg!(feature = "mutant_rule_result_merges_dup_provider") {
                // MUTANT: restore silent last-wins — a later instance replaces the earlier one.
                let mut merged: Vec<ProviderInstance> = Vec::new();
                for pi in out {
                    match merged.iter_mut().find(|e| e.provider == pi.provider) {
                        Some(slot) => *slot = pi,
                        None => merged.push(pi),
                    }
                }
                out = merged;
            } else {
                for i in 0..out.len() {
                    if out[..i].iter().any(|e| e.provider == out[i].provider) {
                        return Err(BzlError::Eval {
                            detail: format!(
                                "Multiple conflicting returned providers with key {}",
                                out[i].provider.name()
                            ),
                        });
                    }
                }
            }
            // Canonical order (providers are a by-type set, sorted by ProviderId's derived Ord) so the node
            // value is deterministic → A4 early cutoff.
            out.sort_by(|a, b| a.provider.cmp(&b.provider));
            // actions stay empty until phase #5 wires ctx.actions; the RuleResult shape is reserved now.
            // MUTANT: drop the declared actions → they never reach the execution phase (emission test red).
            let actions = if cfg!(feature = "mutant_rule_eval_drops_actions") {
                Vec::new()
            } else {
                action_registry.actions.borrow().clone()
            };
            Ok(RuleResult { providers: out, actions })
        })
    }
}

