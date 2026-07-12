use razel_bzl_api::{
    AttrType, BzlError, BzlEvaluator, BzlModule, BzlValue, DepProviders, Dialect as ApiDialect, EvalEnv, GlobSpec,
    LoadKind, ModuleFileValue, PredeclaredEnvId, ProviderId, ProviderInstance, ResolvedToolchain, RuleResult,
    StarlarkSemanticsId, TargetDecl, TypeOptions,
};
use starlark::environment::{FrozenModule, Module};
use starlark::eval::{Evaluator, ReturnFileLoader};
use starlark::syntax::{AstModule, Dialect};
use starlark::values::list::ListRef;
use starlark::values::structs::AllocStruct;
use starlark::values::{Value, ValueLike};
use std::collections::{HashMap, HashSet};

use crate::actions::ActionsValue;
use crate::bridge::{defining_digest, BridgeCtx};
use crate::convert::{alloc, alloc_provider_instance, build_frozen, convert, decode_schema, index_providers, ConvertCtx};
use crate::envs::{env_build_bzl, env_build_file, PhaseEnv};
use crate::globals::{ActionRegistry, GlobMode, TargetRegistry};
use crate::values::{ProviderInstanceValue, RuleValue};
use crate::values_depset::alloc_depset;
use crate::values_file::make_file;
use crate::values_label::{parse_label, LabelValue};
use crate::values_target::TargetValueGen;
use crate::StarlarkEvaluator;
use razel_bzl_api::DepsetOrder;

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

/// The `target.files` depset[File] from a dep's codec-neutral providers (row 6): the dep's `DefaultInfo.files`,
/// re-materialized live. Absent DefaultInfo (or its `files` field) → an EMPTY depset — a target with no default
/// outputs legitimately has empty `.files` (never a fail-closed hole here). A flat-list `files` (the pre-C5
/// shape some fixtures still use) is WRAPPED into a depset so `target.files` is ALWAYS a depset (row-6 law;
/// `mutant_target_files_not_depset` breaks exactly this).
fn default_info_files<'v>(
    module: &Module<'v>,
    providers: &[razel_bzl_api::ProviderInstance],
) -> Result<Value<'v>, BzlError> {
    let empty = || alloc_depset(module.heap(), DepsetOrder::Default.code(), Vec::new(), Vec::new());
    let depset_val = match providers.iter().find(|p| p.provider.name() == crate::globals::DEFAULT_INFO_NAME) {
        None => empty(),
        Some(di) => match di.fields.iter().find(|(n, _)| n == "files").map(|(_, v)| v) {
            Some(files @ BzlValue::Depset(_)) => alloc(module, files)?,
            Some(BzlValue::List(items)) => {
                let direct: Vec<Value> = items.iter().map(|it| alloc(module, it)).collect::<Result<_, _>>()?;
                alloc_depset(module.heap(), DepsetOrder::Default.code(), direct, Vec::new())
            }
            _ => empty(),
        },
    };
    if cfg!(feature = "mutant_target_files_not_depset") {
        // MUTANT: return `target.files` as a FLAT LIST, not a depset (the row-6 law is `.files` = depset[File]).
        // A consumer that flattens it (`t.files.to_list()`) or re-nests it (`depset(transitive=[t.files])`)
        // then fails closed — `target_files_is_a_depset` goes RED.
        let items = crate::values_depset::depset_to_list(depset_val)
            .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
        return Ok(module.heap().alloc(items));
    }
    Ok(depset_val)
}

/// Build the `LabelValue` for a SOURCE file in an `allow_files` attr (row 6): the dependent's package + repo,
/// the source path as the target name (`//<pkg>:<src>`, or `@<repo>//<pkg>:<src>` external). Best-effort — the
/// probe reads `ctx.files.<attr>` (Files), so a source Target's label is for `.label` completeness, not a path.
fn source_label<'v>(
    heap: starlark::values::Heap<'v>,
    parts: &crate::values_label::LabelParts,
    src: &str,
) -> Value<'v> {
    let display = if parts.repo_name.is_empty() {
        format!("//{}:{}", parts.package, src)
    } else {
        format!("@{}//{}:{}", parts.repo_name, parts.package, src)
    };
    heap.alloc(LabelValue {
        package: parts.package.clone(),
        name: src.to_owned(),
        workspace_name: parts.workspace_name.clone(),
        repo_name: parts.repo_name.clone(),
        display,
    })
}

impl StarlarkEvaluator {
    /// The shared BUILD-file evaluation body (row 7, `EnvBuildFile`), parameterized by the [`GlobMode`] its
    /// `glob()` builtin is serviced under. Returns the recorded targets AND (in the collect pass) the globs
    /// each `glob()` collected. `def`/`lambda` in a BUILD fail at PARSE (the def-less BUILD dialect); target()/
    /// alias()/glob() record into the one `TargetRegistry`.
    fn eval_build_inner(
        &self,
        package_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
        glob_mode: GlobMode,
    ) -> Result<(Vec<TargetDecl>, Vec<GlobSpec>), BzlError> {
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

        // Carry the live-module bridge (T20 select): a BUILD may CALL a loaded function (a macro, or a
        // crate_universe-style `triple_to_constraint_set(...)` from a loaded rules_rust module). The BUILD's
        // loaded deps were evaluated by their BZL_LOAD nodes into the SAME shared bridge cache, so an invoke
        // resolves the real callable. A self-contained BUILD (no loaded-function calls) is unaffected.
        let registry = TargetRegistry { globs: glob_mode, bridge: Some(self.bridge.clone()), ..TargetRegistry::default() };
        Module::with_temp_heap(|module| -> Result<(Vec<TargetDecl>, Vec<GlobSpec>), BzlError> {
            {
                let mut eval = Evaluator::new(&module);
                eval.set_loader(&loader);
                eval.extra = Some(&registry); // target()/alias()/glob() record into this
                eval.eval_module(ast, globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            let collected = match &registry.globs {
                GlobMode::Collect(sink) => sink.borrow().clone(),
                _ => Vec::new(),
            };
            Ok((registry.targets.borrow().clone(), collected))
        })
    }
}

impl BzlEvaluator for StarlarkEvaluator {
    fn load_targets(&self, source: &str) -> Result<Vec<String>, BzlError> {
        // Parse-only load SCAN (dep discovery before any evaluation) — the permissive standard dialect is
        // deliberate: it must parse both `.bzl` and BUILD sources; the phase dialect gates real evaluation.
        // Keyword-only args are enabled so a real `.bzl` (`def f(a, *, kw=…)`) parses at scan time too.
        let scan_dialect = Dialect { enable_keyword_only_arguments: true, ..Dialect::Standard };
        let ast = parse("<load-scan>", source, &scan_dialect)?;
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
        let globals = &phase.globals; // EnvBuildBzl: standard + rule()/provider()/depset() + attr

        // T20 R-load-codec: the defining-module content digest (source ⊕ loaded-dep digests) — stamped onto
        // every function/struct THIS module exports (module-content-level identity) AND the key under which
        // this module's frozen form is cached for the live-module bridge.
        let dd = defining_digest(source, loaded);

        // Rebuild each load() target as a FrozenModule, then index by target string for the loader.
        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(target, m)| build_frozen(m).map(|fm| (target.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };
        // The live-module bridge, installed in `eval.extra` so a load-time call of a loaded function resolves
        // the real callable (`crate::bridge`). Held on the stack for the eval's duration.
        let bridge_ctx = BridgeCtx { bridge: self.bridge.clone() };
        let ctx = ConvertCtx { module: module_name, digest: dd };

        // Evaluate in a temp heap, then FREEZE the module and cache its frozen form for the bridge. `frozen`
        // (the loaded deps) + `loader` + `bridge_ctx` are captured by reference and outlive the closure.
        let (bzl_module, frozen_self) =
            Module::with_temp_heap(|module| -> Result<(BzlModule, FrozenModule), BzlError> {
                {
                    let mut eval = Evaluator::new(&module);
                    eval.set_loader(&loader);
                    eval.extra = Some(&bridge_ctx);
                    eval.eval_module(ast, globals).map_err(|e| BzlError::Eval { detail: e.to_string() })?;
                }
                // Decision H: a second same-name provider() reaching module scope is fail-closed at
                // declaration (the index result is unused here — the scan IS the collision check).
                index_providers(&module, module_name)?;
                let mut bindings = Vec::new();
                for name in module.names() {
                    let n = name.as_str();
                    if n.starts_with('_') || loaded_names.contains(n) {
                        continue; // skip private + load()ed symbols; export only this module's own bindings
                    }
                    if let Some(v) = module.get(n) {
                        let mut bv = convert(v, Some(&ctx))?;
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
                // Freeze inside the temp-heap scope: the FrozenModule owns its own frozen heap and survives.
                let frozen_self = module.freeze().map_err(|e| BzlError::Eval { detail: format!("{e:?}") })?;
                Ok((BzlModule { bindings }, frozen_self))
            })?;
        // Cache the frozen live module under (module_name, dd) — the SAME key the exported FunctionRefs carry.
        // Populated at THIS module's own evaluation, so a later module that load()s a function/struct from it
        // always finds it (the loader graph evaluates a dep before its requester).
        self.bridge.insert(module_name, dd, frozen_self);
        Ok(bzl_module)
    }

    fn evaluate_build(
        &self,
        package_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
    ) -> Result<Vec<TargetDecl>, BzlError> {
        // The glob-LESS entry point: a `glob()` here is a fail-closed error (GlobMode::Unsupported). All its
        // existing callers (conformance, tests) are byte-identical; the PACKAGE node uses the glob-aware path.
        self.eval_build_inner(package_name, source, loaded, GlobMode::Unsupported).map(|(ts, _)| ts)
    }

    fn evaluate_build_globs(
        &self,
        package_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
        resolved: Option<&[(GlobSpec, Vec<String>)]>,
    ) -> Result<(Vec<TargetDecl>, Vec<GlobSpec>), BzlError> {
        // COLLECT pass (resolved = None): glob() records specs + yields []. RESOLVED pass: glob() returns the
        // pre-resolved files. The collected specs (empty in the resolved pass) ride back to the PACKAGE node.
        let mode = match resolved {
            None => GlobMode::Collect(std::cell::RefCell::new(Vec::new())),
            Some(map) => GlobMode::Resolved(map.to_vec()),
        };
        self.eval_build_inner(package_name, source, loaded, mode)
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

        // The ActionRegistry carries the live-module bridge (T20 R-analyze): a real rule .bzl calls loaded
        // functions at module scope (`dedent(…)`) AND in the impl, so the bridge must be resolvable while
        // eval.extra holds the ActionRegistry (the ONE extra slot). Self-contained rule .bzls never invoke a
        // loaded function, so this is inert for them.
        let action_registry = ActionRegistry { bridge: Some(self.bridge.clone()), ..ActionRegistry::default() };
        Module::with_temp_heap(|module| -> Result<RuleResult, BzlError> {
            let mut eval = Evaluator::new(&module);
            eval.set_loader(&loader);
            eval.extra = Some(&action_registry); // ctx.actions.run/write + loaded-function bridge (during eval below)
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
            // The live file-attr channel (C3): which label_list attrs are `allow_files` (source files, not
            // dep edges) + their accepted extensions. Cloned so it outlives the `rule` borrow of the heap.
            let attr_files = rule.attr_files.clone();
            // The live provider-requirement + mandatory channels (C5) — enforced below.
            let attr_providers = rule.attr_providers.clone();
            let attr_mandatory = rule.attr_mandatory.clone();
            // The live string-default channel (P1b) — applied below when a target omits a string attr.
            let attr_string_defaults = rule.attr_string_defaults.clone();
            // Parse the target label ONCE: honest Label fields for ctx.label + the exec-path package dir
            // (byte-identical to the old `_pkg`) for ctx.actions.declare_file / ctx.files.
            let label_parts = parse_label(label);

            // Mandatory attrs (C5, `mandatory=True`): a target omitting one is a typed analysis error
            // (Bazel's behavior). Enforced before the impl runs — a missing required attr never reaches ctx.
            if !cfg!(feature = "mutant_rule_skips_mandatory") {
                for m in &attr_mandatory {
                    if !attrs.iter().any(|(n, _)| n == m) {
                        return Err(BzlError::Eval {
                            detail: format!("mandatory attribute '{m}' is missing from '{rule_name}' ({label})"),
                        });
                    }
                }
            }

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
            // ctx.files.<attr>: the resolved source Files, one field per `allow_files` attr.
            let mut file_fields: Vec<(String, Value)> = Vec::new();
            for (aname, aty) in &schema {
                let aval = attrs.iter().find(|(n, _)| n == aname).map(|(_, v)| v);
                if let Some((_, exts)) = attr_files.iter().find(|(n, _)| n == aname) {
                    // FILES attr (C3, `label_list(allow_files=…)`): each entry is a package-relative source
                    // path resolving to a File at `<package exec dir>/<src>` — BYTE-IDENTICAL to the old
                    // `_all_srcs` staging. Validate the extension (a real allow_files check). NOT a dep edge
                    // (analysis already skips FileList), so no provider lookup.
                    let srcs: Vec<String> = match aval {
                        Some(BzlValue::List(items)) => {
                            items.iter().filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None }).collect()
                        }
                        Some(BzlValue::Str(s)) => vec![s.clone()],
                        _ => Vec::new(),
                    };
                    let mut files: Vec<Value> = Vec::new();
                    for s in &srcs {
                        if !exts.is_empty() && !exts.iter().any(|e| s.ends_with(e.as_str())) {
                            return Err(BzlError::Eval {
                                detail: format!(
                                    "source '{s}' in attr '{aname}' of '{rule_name}' lacks an allowed extension {exts:?}"
                                ),
                            });
                        }
                        files.push(heap.alloc(make_file(format!("{}/{}", label_parts.exec_dir, s))));
                    }
                    // C3 RECONCILE (row 6): `ctx.files.<attr>` stays the flat File list (rust.bzl reads
                    // `ctx.files.srcs` — UNCHANGED). `ctx.attr.<attr>` flips to Bazel semantics: a list of
                    // SOURCE Targets (each `.files = depset([the File])`, `.label` set, no indexable providers),
                    // NOT the raw File list. No existing rule reads `ctx.attr.<allow_files>`, so this is inert
                    // for them and Bazel-faithful for a real ruleset.
                    file_fields.push((aname.clone(), heap.alloc(files.clone())));
                    let mut src_targets: Vec<Value> = Vec::with_capacity(files.len());
                    for (s, f) in srcs.iter().zip(files.iter()) {
                        let files_ds = alloc_depset(heap, DepsetOrder::Default.code(), vec![*f], Vec::new());
                        let lbl = source_label(heap, &label_parts, s);
                        src_targets.push(heap.alloc(TargetValueGen {
                            label: lbl,
                            provider_keys: Vec::new(),
                            provider_instances: Vec::new(),
                            files: files_ds,
                        }));
                    }
                    attr_fields.push((aname.clone(), heap.alloc(src_targets)));
                } else if aty.is_label() {
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
                        // Required providers (C5, `providers=[P,…]`): each dep must supply every required
                        // provider — a miss is a typed analysis error naming both (Bazel's `providers=` /
                        // `provides=` check). RED under `mutant_provider_requirement_unenforced`.
                        if !cfg!(feature = "mutant_provider_requirement_unenforced") {
                            if let Some((_, required)) = attr_providers.iter().find(|(n, _)| n == aname) {
                                for req in required {
                                    let req_id = ProviderId::from_name(req.clone());
                                    if !providers.iter().any(|pi| pi.provider == req_id) {
                                        return Err(BzlError::Eval {
                                            detail: format!(
                                                "dependency '{lbl}' of '{rule_name}' is missing required provider '{}' (attr '{aname}')",
                                                if req.is_empty() { "<unnamed>" } else { req }
                                            ),
                                        });
                                    }
                                }
                            }
                        }
                        // C3 RECONCILE (row 6): a dep is a `Target` (not a `{Provider: instance}` dict). Its
                        // PARALLEL provider keys/instances back `dep[Provider]` — the SAME identity indexing the
                        // dict did (a dict and a Target both key by `Provider::equals`, the C2 funnel), so
                        // rust.bzl's `dep[RustInfo]` keeps working UNCHANGED. `.label`/`.files` (DefaultInfo.files
                        // depset) are the added Target surface.
                        let mut prov_keys: Vec<Value> = Vec::new();
                        let mut prov_insts: Vec<Value> = Vec::new();
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
                            prov_keys.push(key);
                            prov_insts.push(alloc_provider_instance(&module, pi)?);
                        }
                        let files = default_info_files(&module, providers)?;
                        let dp = parse_label(lbl);
                        let dep_label = heap.alloc(LabelValue {
                            package: dp.package,
                            name: dp.name,
                            workspace_name: dp.workspace_name,
                            repo_name: dp.repo_name,
                            display: lbl.clone(),
                        });
                        dep_vals.push(heap.alloc(TargetValueGen {
                            label: dep_label,
                            provider_keys: prov_keys,
                            provider_instances: prov_insts,
                            files,
                        }));
                    }
                    attr_fields.push((aname.clone(), heap.alloc(dep_vals)));
                } else {
                    // Scalar (String/Int/Bool) or StringList. SET → the value; UNSET → the explicit
                    // `attr.string(default=…)` if any, else the type's Bazel-implicit zero (`""` string,
                    // `[]` string_list). P1b: this makes `edition` default to "2021" and
                    // `crate_features`/`rustc_flags` default to `[]`, so an unset new attr widens the rustc
                    // argv by nothing (the action stays byte-identical → recompute-0).
                    let v = match aval {
                        // MUTANT `mutant_string_list_attr_dropped`: a SET string_list resolves EMPTY → the
                        // `--cfg feature="…"` args vanish from the dependent's rustc argv, so a
                        // `#[cfg(feature)]`-gated fn is not compiled and the dependent fails closed (the P1b
                        // crate_features proof goes RED).
                        Some(_)
                            if cfg!(feature = "mutant_string_list_attr_dropped")
                                && matches!(aty, AttrType::StringList) =>
                        {
                            heap.alloc(Vec::<Value>::new())
                        }
                        Some(bv) => alloc(&module, bv)?,
                        None => match aty {
                            AttrType::String => match attr_string_defaults.iter().find(|(n, _)| n == aname) {
                                // MUTANT `mutant_attr_string_default_ignored`: drop the stored default → e.g.
                                // `edition` is "" → `--edition=` is emitted with no value → rustc rejects it →
                                // the target fails closed (the P1b edition-default proof goes RED).
                                Some((_, def)) if !cfg!(feature = "mutant_attr_string_default_ignored") => {
                                    heap.alloc(def.as_str())
                                }
                                _ => heap.alloc(""),
                            },
                            AttrType::StringList => heap.alloc(Vec::<Value>::new()),
                            _ => Value::new_none(),
                        },
                    };
                    attr_fields.push((aname.clone(), v));
                }
            }
            let attr_struct = heap.alloc(AllocStruct(attr_fields));
            // ctx.toolchains: the toolchain CONTEXT (row 9-adjacent) — `{toolchain_type -> toolchain_info}`
            // indexable by a Label OR a label string (Bazel's ToolchainContext, not a plain dict). Empty until
            // phase #4 supplies resolved toolchains. A missing MANDATORY type indexes to a fail-closed KeyError.
            let mut tc_entries: Vec<(String, Value)> = Vec::new();
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
                tc_entries.push((t.toolchain_type.clone(), alloc_provider_instance(&module, &t.info)?));
            }
            let toolchains_dict = heap.alloc(crate::values_ctx::ToolchainContextValueGen { entries: tc_entries });
            // ctx.label is now a Label VALUE (C1): honest fields, no string methods. ctx.actions (C4) carries
            // the package exec dir for declare_file. ctx.files (C3) holds the resolved source Files.
            let label_value = heap.alloc(LabelValue {
                package: label_parts.package.clone(),
                name: label_parts.name.clone(),
                workspace_name: label_parts.workspace_name.clone(),
                repo_name: label_parts.repo_name.clone(),
                display: label_parts.display.clone(),
            });
            let actions_value = heap.alloc(ActionsValue { exec_dir: label_parts.exec_dir.clone() });
            let files_struct = heap.alloc(AllocStruct(file_fields));
            // ctx is a custom `CtxValue` (row 9): the core fields + the row-9 scalar fields
            // (var/bin_dir/genfiles_dir/workspace_name/features/disabled_features/configuration), plus the
            // expand_location/expand_make_variables methods (get_methods on CtxValue). workspace_name comes
            // from the target label's repo (the main-repo "" sentinel internally).
            let mut ctx_fields: Vec<(String, Value)> = vec![
                ("label".to_string(), label_value),
                ("attr".to_string(), attr_struct),
                ("toolchains".to_string(), toolchains_dict),
                ("actions".to_string(), actions_value),
                ("files".to_string(), files_struct),
            ];
            ctx_fields.extend(crate::values_ctx::ctx_scalar_fields(heap, &label_parts.workspace_name));
            let ctx = heap.alloc(crate::values_ctx::CtxValueGen { fields: ctx_fields });

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
                    fields.push((n.clone(), convert(v.to_value(), None)?));
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

    fn evaluate_module_file(&self, source: &str) -> Result<ModuleFileValue, BzlError> {
        crate::module_file::evaluate_module_file(source)
    }
}

