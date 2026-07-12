#[cfg(test)]
mod tests {
    use crate::StarlarkEvaluator;
    use razel_bzl_api::conformance;
    use razel_bzl_api::{
        BzlError, BzlEvaluator, Dialect as ApiDialect, EvalEnv, LoadKind, StarlarkSemanticsId, TypeOptions,
    };

    #[test]
    fn passes_bzl_api_conformance() {
        conformance::supports_basic_bindings(&StarlarkEvaluator::new());
        conformance::parse_error_is_fail_closed(&StarlarkEvaluator::new());
        conformance::supports_load(&StarlarkEvaluator::new());
        conformance::loaded_symbols_not_reexported(&StarlarkEvaluator::new());
        conformance::rejects_unsupported_types(&StarlarkEvaluator::new());
    }

    #[test]
    fn passes_build_eval_conformance() {
        conformance::supports_target_instantiation(&StarlarkEvaluator::new());
        conformance::build_dup_name_is_fail_closed(&StarlarkEvaluator::new());
        conformance::build_uses_loaded_constant(&StarlarkEvaluator::new());
        conformance::build_rejects_unsupported_attr(&StarlarkEvaluator::new());
    }

    #[test]
    fn passes_rule_conformance() {
        conformance::supports_rule_definition(&StarlarkEvaluator::new());
        conformance::build_rule_call_records_origin(&StarlarkEvaluator::new());
        conformance::build_rule_rejects_unknown_attr(&StarlarkEvaluator::new());
        conformance::build_rule_rejects_wrong_attr_type(&StarlarkEvaluator::new());
        conformance::rule_call_outside_build_is_fail_closed(&StarlarkEvaluator::new());
    }

    #[test]
    fn passes_rule_evaluation_conformance() {
        conformance::supports_rule_evaluation(&StarlarkEvaluator::new());
        conformance::rule_eval_missing_provider_is_fail_closed(&StarlarkEvaluator::new());
        conformance::provider_rejects_unknown_field(&StarlarkEvaluator::new());
        conformance::rule_eval_missing_dep_label_is_fail_closed(&StarlarkEvaluator::new());
        conformance::supports_action_declaration(&StarlarkEvaluator::new());
    }

    /// Row 6 (Target model, the C3 reconcile): `ctx.attr.<label-attr>` yields `Target` objects, so a rule
    /// impl reads `dep[Provider]` (UNCHANGED from the old dict), `dep.label`, and `dep.files` (a depset[File] =
    /// the dep's DefaultInfo.files). The depset-ness is the row-6 law: `depset(transitive=[dep.files])` only
    /// works because `.files` is a depset. RED under `mutant_target_files_not_depset` (which surfaces `.files`
    /// as a flat list — `depset(transitive=[list])` then fails closed).
    #[test]
    fn target_model_reconciles_dict_to_target() {
        use razel_bzl_api::{BzlValue, Depset, DepProviders, DepsetOrder, ProviderId, ProviderInstance};
        let e = StarlarkEvaluator::new();
        // The impl reads all three Target surfaces: `dep[Info]` (indexing), `dep.label.name`, and `dep.files`
        // (fed to `depset(transitive=…)`, which REQUIRES a depset).
        let src = "\
Info = provider(\"Info\", fields = [\"v\"])\n\
def _impl(ctx):\n\
\x20   dep = ctx.attr.deps[0]\n\
\x20   merged = depset(transitive = [dep.files])\n\
\x20   return [Info(v = \"%s|%s|%d\" % (dep.label.name, dep[Info].v, len(merged.to_list())))]\n\
my_rule = rule(implementation = _impl, attrs = {\"deps\": attr.label_list()})\n";
        let files_depset = BzlValue::Depset(Depset {
            order: DepsetOrder::Default,
            elem: Some("File".into()),
            direct: vec![BzlValue::File("p/liblib.rlib".into())],
            transitive: Vec::new(),
        });
        let dep = DepProviders {
            label: ":lib".into(),
            providers: vec![
                ProviderInstance {
                    provider: ProviderId::from_name("DefaultInfo"),
                    fields: vec![("files".into(), files_depset)],
                },
                ProviderInstance {
                    provider: ProviderId::from_name("Info"),
                    fields: vec![("v".into(), BzlValue::Str("hello".into()))],
                },
            ],
        };
        let attrs = vec![("deps".to_string(), BzlValue::List(vec![BzlValue::Str(":lib".into())]))];
        let result = e
            .evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &attrs, &[dep], &[])
            .expect("the Target model surfaces dep[Info]/dep.label/dep.files (a depset)");
        let info = result.providers.iter().find(|p| p.provider.name() == "Info").expect("Info returned");
        assert_eq!(
            info.get("v"),
            Some(&BzlValue::Str("lib|hello|1".into())),
            "dep.label.name='lib', dep[Info].v='hello', and dep.files is a depset flattening to 1 File"
        );
    }

    /// Row 8 (Args full): `map_each` (a live callable per item), `format_each`/`format`/`format_joined` (`%s`
    /// templates), `before_each` (a literal before each item), `add_joined` (join_with), and `uniquify`
    /// (first-wins dedup) all project — IN ORDER — into the frozen action argv. RED under
    /// `mutant_args_map_each_skipped` (the map_each callable is dropped, so `Dm`/`Dn` become raw `m`/`n`).
    #[test]
    fn args_full_projects_into_argv() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let src = "\
def _double(x):\n\
\x20   return \"D\" + x\n\
def _impl(ctx):\n\
\x20   args = ctx.actions.args()\n\
\x20   args.add(\"--flag\", \"v\", format = \"val=%s\")\n\
\x20   args.add_all([\"a\", \"b\", \"a\"], format_each = \"-I%s\", before_each = \"-X\", uniquify = True)\n\
\x20   args.add_joined([\"p\", \"q\"], join_with = \",\", format_joined = \"L=%s\")\n\
\x20   args.add_all([\"m\", \"n\"], map_each = _double)\n\
\x20   ctx.actions.run(executable = \"tool\", arguments = [args], outputs = [\"o\"], mnemonic = \"M\")\n\
\x20   return [DefaultInfo(files = depset([]))]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let result = e
            .evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &[], &[], &[])
            .expect("the Args-full surface projects into the action");
        let act = result.actions.first().expect("one action declared");
        assert_eq!(
            act.argv,
            vec!["tool", "--flag", "val=v", "-X", "-Ia", "-X", "-Ib", "L=p,q", "Dm", "Dn"],
            "add(format=) + add_all(format_each/before_each/uniquify) + add_joined + add_all(map_each) flatten in order"
        );
        let _ = BzlValue::None; // (import anchor)
    }

    /// Row 9 (ctx scalars): the minimal honest scalar surface — `ctx.var["COMPILATION_MODE"]`,
    /// `ctx.bin_dir.path`, `ctx.workspace_name`, `ctx.features`, `ctx.configuration.default_shell_env`, and
    /// `ctx.expand_make_variables`/`ctx.expand_location` (pass-through on a plain string; `$(VAR)` resolved
    /// from ctx.var).
    #[test]
    fn ctx_scalars_and_expanders() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let src = "\
Info = provider(\"Info\", fields = [\"v\"])\n\
def _impl(ctx):\n\
\x20   parts = [\n\
\x20       ctx.var[\"COMPILATION_MODE\"],\n\
\x20       ctx.bin_dir.path,\n\
\x20       str(len(ctx.features)),\n\
\x20       str(len(ctx.configuration.default_shell_env)),\n\
\x20       ctx.expand_location(\"plain-no-directives\"),\n\
\x20       ctx.expand_make_variables(\"a\", \"mode=$(COMPILATION_MODE)\"),\n\
\x20   ]\n\
\x20   return [Info(v = \"|\".join(parts))]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let result = e
            .evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &[], &[], &[])
            .expect("the ctx scalar surface + expanders evaluate");
        let info = result.providers.iter().find(|p| p.provider.name() == "Info").expect("Info returned");
        assert_eq!(
            info.get("v"),
            Some(&BzlValue::Str("fastbuild||0|0|plain-no-directives|mode=fastbuild".into())),
            "COMPILATION_MODE=fastbuild, bin_dir.path='', 0 features, empty default_shell_env, plain expand, $(COMPILATION_MODE)→fastbuild"
        );
    }

    /// Row 9 fail-closed law: `ctx.expand_location` on an unresolvable `$(...)` directive is a typed error
    /// (razel does not resolve location targets this wave), NEVER a silent pass-through. RED under
    /// `mutant_expand_location_absorbs_unknown` (which absorbs the directive → the eval succeeds).
    #[test]
    fn expand_location_fails_closed_on_unknown() {
        let e = StarlarkEvaluator::new();
        let src = "\
def _impl(ctx):\n\
\x20   x = ctx.expand_location(\"$(location //x:y)\")\n\
\x20   return [DefaultInfo(files = depset([]))]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r = e.evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &[], &[], &[]);
        assert!(
            r.is_err(),
            "expand_location must FAIL CLOSED on an unresolvable $(location …) — RED (Ok) under mutant_expand_location_absorbs_unknown"
        );
    }

    /// Row-G first slice: the builtin `DefaultInfo` is (1) constructible from a rule impl
    /// (`DefaultInfo(files=[...])` — a global, no declaration) and (2) readable across a dep edge via
    /// `dep[DefaultInfo].files` (the re-keying registers the builtin identity in `providers_by_id`). This is
    /// the files-chaining carrier: a dep's DefaultInfo files reach a dependent rule's impl.
    #[test]
    fn default_info_builtin_constructible_and_readable() {
        use razel_bzl_api::{BzlValue, DepProviders, ProviderId, ProviderInstance};
        let e = StarlarkEvaluator::new();
        let src = "\
Out = provider(\"Out\", fields = [\"paths\"])\n\
def _impl(ctx):\n\
\x20   files = []\n\
\x20   for d in ctx.attr.deps:\n\
\x20       files = files + d[DefaultInfo].files\n\
\x20   return [DefaultInfo(files = [\"self.o\"]), Out(paths = files)]\n\
my_rule = rule(implementation = _impl, attrs = {\"deps\": attr.label_list()})\n";
        let dep = DepProviders {
            label: ":dep".into(),
            providers: vec![ProviderInstance {
                provider: ProviderId::from_name("DefaultInfo"),
                fields: vec![("files".into(), BzlValue::List(vec![BzlValue::Str("dep.rlib".into())]))],
            }],
        };
        let attrs = vec![("deps".to_string(), BzlValue::List(vec![BzlValue::Str(":dep".into())]))];
        let result = e
            .evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &attrs, &[dep], &[])
            .expect("the rule evaluates (DefaultInfo builtin is available + dep[DefaultInfo] re-keys)");
        let out = result.providers.iter().find(|p| p.provider.name() == "Out").expect("Out provider present");
        assert_eq!(
            out.get("paths"),
            Some(&BzlValue::List(vec![BzlValue::Str("dep.rlib".into())])),
            "the impl read the dep's DefaultInfo.files via dep[DefaultInfo] (the builtin re-keys, no declaration)"
        );
        assert!(
            result.providers.iter().any(|p| p.provider.name() == "DefaultInfo"),
            "DefaultInfo(files=[...]) is constructible from the impl (the global builtin) and returned"
        );
    }

    /// The provider-identity lockdown gates (ADR-0004 / RazelV4ProviderIdentityLockdown §4): opaque identity
    /// comparison (C2), fail-closed duplicate declaration (H), fail-closed duplicate return (E).
    #[test]
    fn passes_provider_identity_conformance() {
        conformance::provider_identity_opaque_comparison(&StarlarkEvaluator::new());
        conformance::provider_dup_declaration_fail_closed(&StarlarkEvaluator::new());
        conformance::rule_result_dup_provider_fail_closed(&StarlarkEvaluator::new());
    }

    // ──────────────── phase-environment lockdown gates (ADR-0003 §4) ────────────────

    /// Gate `build_loaded_and_build_file_not_conflated` (the v1 cut of
    /// `build_loaded_and_bzlmod_loaded_not_conflated`): the two phases that exist today are distinct BOTH
    /// by env identity and by name-set. RED under `mutant_one_globals_all_loadkinds` (the spike's one
    /// bzl_globals() served for every phase).
    #[test]
    fn one_globals_per_phase_not_conflated() {
        conformance::phase_envs_not_conflated(&StarlarkEvaluator::new());
        assert_ne!(
            crate::envs::env_build_bzl().env_id,
            crate::envs::env_build_file().env_id,
            "EnvBuildBzl and EnvBuildFile must have distinct PredeclaredEnvIds (phase separation is keyed)"
        );
    }

    /// Gate `predeclared_env_id_is_canonical` (§4, NEW — the impl side): the SERVED ids equal the api's
    /// canonical derivation from the DECLARED registry tables, are deterministic across evaluators, and
    /// the prelude kind SHARES EnvBuildBzl (R1). RED under `mutant_env_digest_from_heap_iteration` (the
    /// id derived from live `Globals` name enumeration — heap/seam bytes — instead of the registry).
    #[test]
    fn predeclared_env_id_is_canonical() {
        use razel_bzl_api::{derive_predeclared_env_id, EnvTag};
        let e = StarlarkEvaluator::new();
        let build_bzl = e
            .predeclared_env_id(&LoadKind::Build { is_prelude: false }, ApiDialect::Bzl)
            .expect("the row-1 env id is served");
        assert_eq!(
            build_bzl,
            derive_predeclared_env_id(EnvTag::EnvBuildBzl, &crate::envs::entries(crate::envs::ENV_BUILD_BZL_TABLE), None),
            "the served id must be the canonical derivation of the DECLARED registry — never heap bytes"
        );
        assert_eq!(
            crate::envs::env_build_file().env_id,
            derive_predeclared_env_id(EnvTag::EnvBuildFile, &crate::envs::entries(crate::envs::ENV_BUILD_FILE_TABLE), None),
            "the BUILD-file env id must be the canonical derivation of its declared registry"
        );
        assert_eq!(
            e.predeclared_env_id(&LoadKind::Build { is_prelude: true }, ApiDialect::Bzl).unwrap(),
            build_bzl,
            "Build{{is_prelude:true}} SHARES EnvBuildBzl (R1) — prelude-ness is a key bit, not an env"
        );
        assert_eq!(
            StarlarkEvaluator::new().predeclared_env_id(&LoadKind::Build { is_prelude: false }, ApiDialect::Bzl).unwrap(),
            build_bzl,
            "deterministic across evaluator instances"
        );
        // Rows v1 has not built fail closed — never a defaulted id.
        assert!(e.predeclared_env_id(&LoadKind::Bzlmod, ApiDialect::Bzl).is_err());
        assert!(e.predeclared_env_id(&LoadKind::Builtins, ApiDialect::Bzl).is_err());
        assert!(e.predeclared_env_id(&LoadKind::Build { is_prelude: false }, ApiDialect::Scl).is_err());
    }

    /// The per-phase Dialect consts (§3): the BUILD dialect forbids `def` at PARSE (Bazel's BUILD
    /// dialect), closing the spike's permissive-dialect gap; `.bzl` keeps the standard set.
    #[test]
    fn build_dialect_forbids_def_at_parse() {
        assert!(
            matches!(
                StarlarkEvaluator::new().evaluate_build("pkg", "def f():\n    pass\n", &[]),
                Err(BzlError::Parse { .. })
            ),
            "a def in a BUILD file must be a PARSE error under the BUILD dialect (environmental, not runtime)"
        );
        assert!(
            StarlarkEvaluator::new()
                .evaluate(&EvalEnv::default(), "m.bzl", "def _f():\n    return 1\nx = _f()\n", &[])
                .is_ok(),
            ".bzl keeps the standard dialect (def is legal)"
        );
    }

    /// T19-P2: the native `alias()` builtin records a `kind="alias"` TargetDecl (no rule origin) with its
    /// `actual` label and `visibility` as attrs — the loading side of the vendored-crates hub. Analysis
    /// (razel-analysis) forwards `actual`'s providers; here we prove the BUILD-file surface parses + records.
    #[test]
    fn alias_builtin_records_native_target() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let src = "\
alias(name = \"anyhow\", actual = \"//crates/anyhow-1.0.103:anyhow\", visibility = [\"//visibility:public\"])\n";
        let targets = e.evaluate_build("crates", src, &[]).expect("alias() parses + records in a BUILD file");
        assert_eq!(targets.len(), 1, "one alias target recorded");
        let t = &targets[0];
        assert_eq!(t.kind, "alias");
        assert_eq!(t.name, "anyhow");
        assert!(t.origin.is_none(), "an alias has NO rule origin (native, resolved structurally at analysis)");
        assert_eq!(
            t.attrs.iter().find(|(n, _)| n == "actual").map(|(_, v)| v),
            Some(&BzlValue::Str("//crates/anyhow-1.0.103:anyhow".to_string())),
            "the actual label is recorded"
        );
        assert_eq!(
            t.attrs.iter().find(|(n, _)| n == "visibility").map(|(_, v)| v),
            Some(&BzlValue::List(vec![BzlValue::Str("//visibility:public".to_string())])),
            "the alias's own visibility is recorded (a dependent enforces it)"
        );
        // `alias` is a BUILD-only builtin — it must NOT exist in the `.bzl` env (phase separation).
        assert!(
            e.evaluate(&EvalEnv::default(), "m.bzl", "alias(name=\"x\", actual=\"//a:b\")\n", &[]).is_err(),
            "alias() is not a .bzl toplevel (BUILD-file env only)"
        );
    }

    /// T20 select: a bare `select({...})` in a BUILD attr position crosses as an UNRESOLVED
    /// `BzlValue::Select` (one Branch arm) — NEVER resolved at load. Its conditions are CANONICALLY
    /// label-sorted regardless of declaration order (order-independent for matching).
    #[test]
    fn select_in_build_crosses_as_unresolved_bzlvalue() {
        use razel_bzl_api::{BzlValue, SelectArm};
        let e = StarlarkEvaluator::new();
        // Declared b-then-a; the crossed Select must be label-sorted a-then-b.
        let src = "target(kind = \"x\", name = \"t\", deps = select({\":b\": [\"//b\"], \":a\": [\"//a\"]}, no_match_error = \"boom\"))\n";
        let targets = e.evaluate_build("p", src, &[]).expect("select() in a BUILD attr evaluates (unresolved)");
        let deps = targets[0].attrs.iter().find(|(n, _)| n == "deps").map(|(_, v)| v).expect("deps attr recorded");
        match deps {
            BzlValue::Select(arms) => {
                assert_eq!(arms.len(), 1, "a bare select is ONE Branch arm");
                let SelectArm::Branch { conditions, no_match_error } = &arms[0] else { panic!("expected a Branch arm") };
                assert_eq!(no_match_error, "boom", "no_match_error is carried");
                let labels: Vec<&str> = conditions.iter().map(|(k, _)| k.as_str()).collect();
                assert_eq!(labels, vec![":a", ":b"], "conditions canonically label-sorted (declared b,a)");
            }
            other => panic!("deps must be an UNRESOLVED Select, got {other:?}"),
        }
    }

    /// T20 select: `["//base"] + select({...})` builds a Bazel SelectorList — a MULTI-arm `BzlValue::Select`
    /// whose first arm is the Concrete base list and second is the select Branch (the `list + select` / `radd`
    /// path). `select(...) + select(...)` likewise concatenates two Branch arms.
    #[test]
    fn list_plus_select_is_a_multi_arm_selectorlist() {
        use razel_bzl_api::{BzlValue, SelectArm};
        let e = StarlarkEvaluator::new();
        let src = "target(kind = \"x\", name = \"t\", deps = [\"//base\"] + select({\":a\": [\"//a\"], \"//conditions:default\": []}))\n";
        let targets = e.evaluate_build("p", src, &[]).expect("list + select evaluates");
        let deps = targets[0].attrs.iter().find(|(n, _)| n == "deps").map(|(_, v)| v).unwrap();
        let BzlValue::Select(arms) = deps else { panic!("expected a Select, got {deps:?}") };
        assert_eq!(arms.len(), 2, "`[..] + select(..)` is a two-arm SelectorList");
        assert!(
            matches!(&arms[0], SelectArm::Concrete(BzlValue::List(items)) if items == &vec![BzlValue::Str("//base".into())]),
            "arm 0 is the Concrete base list"
        );
        assert!(matches!(&arms[1], SelectArm::Branch { .. }), "arm 1 is the select Branch");

        // select + select → two Branch arms concatenated.
        let src2 = "target(kind = \"x\", name = \"t\", deps = select({\":a\": [\"//a\"]}) + select({\":b\": [\"//b\"]}))\n";
        let t2 = e.evaluate_build("p", src2, &[]).expect("select + select evaluates");
        let deps2 = t2[0].attrs.iter().find(|(n, _)| n == "deps").map(|(_, v)| v).unwrap();
        let BzlValue::Select(arms2) = deps2 else { panic!("expected a Select") };
        assert_eq!(arms2.len(), 2, "select + select is two Branch arms");
        assert!(arms2.iter().all(|a| matches!(a, SelectArm::Branch { .. })), "both arms are Branches");
    }

    /// T20 select: `config_setting`/`constraint_setting`/`constraint_value` are NATIVE BUILD decls (no rule
    /// origin, resolved structurally at analysis) — the load-side proof. `values` crosses as a dict,
    /// `constraint_values` as a list. Native decls are BUILD-only (phase separation: not in the `.bzl` env).
    #[test]
    fn config_and_constraint_native_decls_record() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let src = "\
constraint_setting(name = \"cpu\")\n\
constraint_value(name = \"aarch64\", constraint_setting = \":cpu\")\n\
config_setting(name = \"cs\", constraint_values = [\"@platforms//cpu:aarch64\"], values = {\"cpu\": \"darwin_arm64\"})\n";
        let targets = e.evaluate_build("p", src, &[]).expect("native config/constraint decls record");
        let by = |k: &str| targets.iter().find(|t| t.name == k).expect("target recorded");
        assert_eq!(by("cpu").kind, "constraint_setting");
        assert_eq!(by("aarch64").kind, "constraint_value");
        let cs = by("cs");
        assert_eq!(cs.kind, "config_setting");
        assert!(cs.origin.is_none(), "config_setting is native (no rule origin)");
        assert_eq!(
            cs.attrs.iter().find(|(n, _)| n == "constraint_values").map(|(_, v)| v),
            Some(&BzlValue::List(vec![BzlValue::Str("@platforms//cpu:aarch64".into())])),
            "constraint_values recorded as a list"
        );
        assert!(
            matches!(cs.attrs.iter().find(|(n, _)| n == "values").map(|(_, v)| v), Some(BzlValue::Dict(_))),
            "values recorded as a dict"
        );
        // config_setting is a BUILD-only builtin — NOT a `.bzl` toplevel (phase separation).
        assert!(
            e.evaluate(&EvalEnv::default(), "m.bzl", "config_setting(name=\"x\")\n", &[]).is_err(),
            "config_setting() is BUILD-file-only"
        );
    }

    /// Fail-closed row selection (§3): environments v1 has not built are typed errors at the seam —
    /// an unknown semantics row, non-default TypeOptions, prelude, `.scl`, and the bzlmod kinds.
    #[test]
    fn unbuilt_env_rows_fail_closed() {
        let e = StarlarkEvaluator::new();
        let src = "x = 1\n";
        let with = |f: &dyn Fn(&mut EvalEnv)| {
            let mut env = EvalEnv::default();
            f(&mut env);
            e.evaluate(&env, "m.bzl", src, &[])
        };
        assert!(with(&|_| {}).is_ok(), "the row-1 v1 env evaluates");
        assert!(
            matches!(with(&|env| env.semantics = StarlarkSemanticsId([9; 32])), Err(BzlError::Unsupported { .. })),
            "an unknown semantics row must fail closed (keyed selection with one v1 entry)"
        );
        assert!(
            matches!(
                with(&|env| env.type_options = TypeOptions { use_type_syntax: true, ..Default::default() }),
                Err(BzlError::Unsupported { .. })
            ),
            "non-default TypeOptions must fail closed until the load-time type-check pass exists"
        );
        assert!(
            matches!(
                with(&|env| env.load_kind = LoadKind::Build { is_prelude: true }),
                Err(BzlError::Unsupported { .. })
            ),
            "prelude evaluation (re-export) is not built — fail closed"
        );
        assert!(
            matches!(with(&|env| env.dialect = ApiDialect::Scl), Err(BzlError::Unsupported { .. })),
            ".scl is semantics-disabled in v1 — fail closed"
        );
        for kind in [LoadKind::Builtins, LoadKind::Bzlmod, LoadKind::BzlmodBootstrap] {
            assert!(
                matches!(with(&|env| env.load_kind = kind), Err(BzlError::Unsupported { .. })),
                "{kind:?} has no built environment in v1 — fail closed"
            );
        }
    }

    // ──────────────── T17-C: Label / depset / File / ctx.actions (C1–C4) ────────────────

    use razel_bzl_api::BzlValue;

    /// Evaluate a rule impl and return its `RuleResult` (the common C1–C4 harness).
    fn eval_impl(src: &str, label: &str) -> Result<razel_bzl_api::RuleResult, BzlError> {
        StarlarkEvaluator::new().evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], label, &[], &[], &[])
    }
    fn provider_field<'a>(r: &'a razel_bzl_api::RuleResult, provider: &str, field: &str) -> &'a BzlValue {
        r.providers
            .iter()
            .find(|p| p.provider.name() == provider)
            .unwrap_or_else(|| panic!("provider {provider} present"))
            .get(field)
            .unwrap_or_else(|| panic!("field {field} present"))
    }

    /// C1: `ctx.label` is a Label object with honest fields; an INTERNAL and an EXTERNAL label parse right.
    #[test]
    fn label_value_exposes_honest_fields() {
        let src = "Out = provider(\"Out\", fields = [\"pkg\", \"name\", \"repo\", \"ws\"])\n\
def _impl(ctx):\n\
\x20   return [Out(pkg = ctx.label.package, name = ctx.label.name, repo = ctx.label.repo_name, ws = ctx.label.workspace_name)]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r = eval_impl(src, "//razel-wire-cbor:razel_wire_cbor").expect("internal label evaluates");
        assert_eq!(provider_field(&r, "Out", "pkg"), &BzlValue::Str("razel-wire-cbor".into()));
        assert_eq!(provider_field(&r, "Out", "name"), &BzlValue::Str("razel_wire_cbor".into()));
        assert_eq!(provider_field(&r, "Out", "repo"), &BzlValue::Str(String::new()), "main repo repo_name is \"\"");

        let r2 = eval_impl(src, "@taut-shape//:taut_shape").expect("external label evaluates");
        // Bazel-honest: package is "" (root package), the repo rides repo_name/workspace_name.
        assert_eq!(provider_field(&r2, "Out", "pkg"), &BzlValue::Str(String::new()), "external root package is \"\"");
        assert_eq!(provider_field(&r2, "Out", "name"), &BzlValue::Str("taut_shape".into()));
        assert_eq!(provider_field(&r2, "Out", "repo"), &BzlValue::Str("taut-shape".into()));
        assert_eq!(provider_field(&r2, "Out", "ws"), &BzlValue::Str("taut-shape".into()));
    }

    /// C1: a Label is NOT a string — `.split` is a typed error, never a silent success.
    #[test]
    fn label_is_not_a_string() {
        let src = "Out = provider(\"Out\", fields = [\"x\"])\n\
def _impl(ctx):\n\
\x20   y = ctx.label.split(\":\")\n\
\x20   return [Out(x = 1)]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        assert!(eval_impl(src, "//p:t").is_err(), "ctx.label.split must fail (a Label is not a string)");
    }

    /// C2 + the reserved-tag codec seat: a module-scope depset projects to `BzlValue::Depset` and encodes
    /// under tag 7 with the default order code — the pinned frame, additively filled.
    #[test]
    fn depset_fills_reserved_tag7_codec_seat() {
        use razel_bzl_api::{encode_bzl_value, DepsetOrder};
        let e = StarlarkEvaluator::new();
        let src = "x = depset(direct = [\"a\"], transitive = [depset(direct = [\"b\"])])\n";
        let m = e.evaluate(&EvalEnv::default(), "m.bzl", src, &[]).expect("module evaluates");
        let x = m.get("x").expect("x exported");
        match x {
            BzlValue::Depset(d) => {
                assert_eq!(d.order, DepsetOrder::Default, "no order= ⇒ default (STABLE_ORDER)");
                assert_eq!(d.direct, vec![BzlValue::Str("a".into())]);
                assert_eq!(d.transitive.len(), 1);
                assert_eq!(d.transitive[0].direct, vec![BzlValue::Str("b".into())]);
            }
            other => panic!("x is not a depset: {other:?}"),
        }
        let mut b = Vec::new();
        encode_bzl_value(x, &mut b);
        assert_eq!(b[0], 7, "depset encodes under the reserved tag 7");
        assert_eq!(b[1], 0, "default order code byte is 0 (STABLE_ORDER)");
    }

    /// C2 MUTANT `mutant_depset_tolist_drops_transitive`: `to_list()` is postorder (transitive first, then
    /// direct), deduplicated. Under the mutant only the direct elements survive → the transitive element
    /// vanishes and this reds.
    #[test]
    fn depset_to_list_is_postorder_with_transitive() {
        let src = "Out = provider(\"Out\", fields = [\"items\"])\n\
def _impl(ctx):\n\
\x20   d = depset(direct = [\"a\"], transitive = [depset(direct = [\"b\", \"a\"])])\n\
\x20   return [Out(items = d.to_list())]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r = eval_impl(src, "//p:t").expect("evaluates");
        // postorder: transitive ["b","a"] first, then direct ["a"] deduped away → ["b", "a"].
        assert_eq!(
            provider_field(&r, "Out", "items"),
            &BzlValue::List(vec![BzlValue::Str("b".into()), BzlValue::Str("a".into())]),
            "to_list is postorder + deduped (transitive first) — RED under mutant_depset_tolist_drops_transitive"
        );
    }

    /// C2: a depset is NOT a sequence — `len`/indexing/iteration/`in` all fail closed.
    #[test]
    fn depset_rejects_sequence_ops() {
        let mk = |body: &str| {
            format!(
                "Out = provider(\"Out\", fields = [\"x\"])\n\
def _impl(ctx):\n\
\x20   d = depset(direct = [\"a\"])\n\
\x20   {body}\n\
\x20   return [Out(x = 1)]\n\
my_rule = rule(implementation = _impl, attrs = {{}})\n"
            )
        };
        assert!(eval_impl(&mk("y = len(d)"), "//p:t").is_err(), "len(depset) must fail");
        assert!(eval_impl(&mk("y = d[0]"), "//p:t").is_err(), "depset indexing must fail");
        assert!(eval_impl(&mk("y = [e for e in d]"), "//p:t").is_err(), "depset iteration must fail");
        assert!(eval_impl(&mk("y = \"a\" in d"), "//p:t").is_err(), "`in` on a depset must fail");
    }

    /// C3 MUTANT `mutant_declare_file_ignores_package`: `declare_file(name)` lands at `<pkg exec dir>/<name>`.
    /// Under the mutant the File is at the bare name → this reds. Also checks the external exec prefix.
    #[test]
    fn declare_file_places_under_package_exec_dir() {
        let src = "Out = provider(\"Out\", fields = [\"path\", \"dir\", \"base\"])\n\
def _impl(ctx):\n\
\x20   f = ctx.actions.declare_file(\"libx.rlib\")\n\
\x20   return [Out(path = f.path, dir = f.dirname, base = f.basename)]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r = eval_impl(src, "//mypkg:t").expect("evaluates");
        assert_eq!(
            provider_field(&r, "Out", "path"),
            &BzlValue::Str("mypkg/libx.rlib".into()),
            "declare_file lands under the package exec dir — RED under mutant_declare_file_ignores_package"
        );
        assert_eq!(provider_field(&r, "Out", "dir"), &BzlValue::Str("mypkg".into()), "File.dirname");
        assert_eq!(provider_field(&r, "Out", "base"), &BzlValue::Str("libx.rlib".into()), "File.basename");

        // External target: the exec prefix is external/<repo> (byte-identical to the old _pkg).
        let r2 = eval_impl(src, "@taut-shape//:taut_shape").expect("external evaluates");
        assert_eq!(provider_field(&r2, "Out", "path"), &BzlValue::Str("external/taut-shape/libx.rlib".into()));
    }

    /// C3: `ctx.files.<attr>` resolves `allow_files` source labels to Files under the package exec dir, and a
    /// non-matching extension fails closed (the real allow_files check).
    #[test]
    fn ctx_files_resolves_sources_and_validates_extension() {
        let src = "Out = provider(\"Out\", fields = [\"p0\", \"p1\"])\n\
def _impl(ctx):\n\
\x20   fs = ctx.files.srcs\n\
\x20   return [Out(p0 = fs[0].path, p1 = fs[1].path)]\n\
my_rule = rule(implementation = _impl, attrs = {\"srcs\": attr.label_list(allow_files = [\".rs\"])})\n";
        let attrs = vec![(
            "srcs".to_string(),
            BzlValue::List(vec![BzlValue::Str("src/lib.rs".into()), BzlValue::Str("src/cbor.rs".into())]),
        )];
        let r = StarlarkEvaluator::new()
            .evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//wire:t", &attrs, &[], &[])
            .expect("files attr evaluates");
        assert_eq!(provider_field(&r, "Out", "p0"), &BzlValue::Str("wire/src/lib.rs".into()));
        assert_eq!(provider_field(&r, "Out", "p1"), &BzlValue::Str("wire/src/cbor.rs".into()));

        let bad = vec![("srcs".to_string(), BzlValue::List(vec![BzlValue::Str("src/data.txt".into())]))];
        let err = StarlarkEvaluator::new().evaluate_rule(
            &EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//wire:t", &bad, &[], &[],
        );
        assert!(err.is_err(), "a .txt src under allow_files=[.rs] must fail closed (extension check)");
    }

    /// C4 MUTANT `mutant_ctx_actions_run_drops_arguments`: run projects `argv = [executable] + flattened
    /// arguments`, incl. an `Args` object flattened in order. Under the mutant argv is just the executable →
    /// this reds. Also checks input/output projection + sort/dedup and the WriteFile projection.
    #[test]
    fn ctx_actions_run_projects_argv_inputs_outputs() {
        let src = "Out = provider(\"Out\", fields = [\"x\"])\n\
def _impl(ctx):\n\
\x20   a = ctx.actions.args()\n\
\x20   a.add(\"--flag\")\n\
\x20   a.add(\"--name\", \"v\")\n\
\x20   a.add_all([\"-L\", \"dir\"])\n\
\x20   ctx.actions.run(mnemonic = \"M\", executable = \"tool\", arguments = [a, \"tail\"], inputs = [\"b\", \"a\", \"a\"], outputs = [\"z\", \"y\"])\n\
\x20   return [Out(x = 1)]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r = eval_impl(src, "//p:t").expect("evaluates");
        assert_eq!(r.actions.len(), 1);
        let a = &r.actions[0];
        assert_eq!(
            a.argv,
            vec!["tool", "--flag", "--name", "v", "-L", "dir", "tail"].iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "argv = [executable] + flattened Args + list args, IN ORDER — RED under mutant_ctx_actions_run_drops_arguments"
        );
        assert_eq!(a.inputs, vec!["a".to_string(), "b".to_string()], "inputs sorted + deduped (projection law)");
        assert_eq!(a.outputs, vec!["y".to_string(), "z".to_string()], "outputs sorted");
        assert_eq!(a.mnemonic, "M");
    }

    /// C4: `ctx.actions.write` projects the shared WriteFile convention byte-identically to the deleted
    /// `write_file` global, with a File output.
    #[test]
    fn ctx_actions_write_projects_write_file_convention() {
        let src = "Out = provider(\"Out\", fields = [\"x\"])\n\
def _impl(ctx):\n\
\x20   out = ctx.actions.declare_file(\"out.txt\")\n\
\x20   ctx.actions.write(output = out, content = \"hello\\n\")\n\
\x20   return [Out(x = 1)]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r = eval_impl(src, "//hello:t").expect("evaluates");
        assert_eq!(r.actions.len(), 1);
        assert_eq!(r.actions[0].mnemonic, "WriteFile");
        assert_eq!(r.actions[0].argv, vec!["write_file".to_string(), "hello\n".to_string()]);
        assert_eq!(r.actions[0].outputs, vec!["hello/out.txt".to_string()], "the File output projects to its .path");
    }

    // ──────────────── T17-C5: providers to Bazel shape (RustInfo/depset[File]/providers=/mandatory=) ────────────────

    /// C5 MUTANT `mutant_provider_requirement_unenforced`: `deps = attr.label_list(providers = [MyInfo])`
    /// ENFORCES the requirement — a dep supplying MyInfo passes; a dep missing it is a typed analysis error
    /// (Bazel's `providers=` check). Under the mutant the check is skipped and a MyInfo-less dep silently
    /// resolves → the fail-closed assertion reds.
    #[test]
    fn provider_requirement_enforced() {
        use razel_bzl_api::{DepProviders, ProviderId, ProviderInstance};
        let src = "MyInfo = provider(\"MyInfo\", fields = [\"v\"])\n\
def _impl(ctx):\n\
\x20   return [MyInfo(v = 1)]\n\
my_rule = rule(implementation = _impl, attrs = {\"deps\": attr.label_list(providers = [MyInfo])})\n";
        let e = StarlarkEvaluator::new();
        let dep_ok = DepProviders {
            label: ":good".into(),
            providers: vec![ProviderInstance { provider: ProviderId::from_name("MyInfo"), fields: vec![("v".into(), BzlValue::Int(1))] }],
        };
        let dep_bad = DepProviders {
            label: ":bad".into(),
            providers: vec![ProviderInstance { provider: ProviderId::from_name("DefaultInfo"), fields: vec![] }],
        };
        let a_ok = vec![("deps".to_string(), BzlValue::List(vec![BzlValue::Str(":good".into())]))];
        let a_bad = vec![("deps".to_string(), BzlValue::List(vec![BzlValue::Str(":bad".into())]))];
        assert!(
            e.evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &a_ok, &[dep_ok], &[]).is_ok(),
            "a dep supplying the required provider MyInfo passes"
        );
        assert!(
            e.evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &a_bad, &[dep_bad], &[]).is_err(),
            "a dep MISSING the required provider MyInfo must fail closed — RED under mutant_provider_requirement_unenforced"
        );
    }

    /// C5 MUTANT `mutant_provider_file_field_stringified`: a File carried in a provider field survives the
    /// codec as a File (`BzlValue::File`, tag 8) — so the exec `.path` is intact and the CONSUMING side can
    /// read `dep[MyInfo].rlib.path` (the Appendix-A `--extern name=path` scheme). Under the mutant the File
    /// degrades to a bare `Str`, so (1) the produced field is a `Str` and (2) `.path` on the consuming side
    /// fails → both reds.
    #[test]
    fn provider_file_field_round_trips() {
        use razel_bzl_api::DepProviders;
        // (1) producing side: a rule returns MyInfo(rlib = <declared File>). The field projects to a File.
        let prod = "MyInfo = provider(\"MyInfo\", fields = [\"rlib\"])\n\
def _impl(ctx):\n\
\x20   return [MyInfo(rlib = ctx.actions.declare_file(\"libx.rlib\"))]\n\
my_rule = rule(implementation = _impl, attrs = {})\n";
        let r_prod = eval_impl(prod, "//p:t").expect("producing rule evaluates");
        assert_eq!(
            provider_field(&r_prod, "MyInfo", "rlib"),
            &BzlValue::File("p/libx.rlib".into()),
            "a File in a provider field projects to BzlValue::File (its exec path) — RED under mutant_provider_file_field_stringified"
        );
        // (2) consuming side: feed the producing providers as a dep and read dep[MyInfo].rlib.path — the
        // File must round-trip so `.path` is readable (a Str would have no `.path`).
        let cons = "MyInfo = provider(\"MyInfo\", fields = [\"rlib\", \"p\"])\n\
def _impl(ctx):\n\
\x20   d = ctx.attr.deps[0][MyInfo]\n\
\x20   return [MyInfo(rlib = d.rlib, p = d.rlib.path)]\n\
my_rule = rule(implementation = _impl, attrs = {\"deps\": attr.label_list(providers = [MyInfo])})\n";
        let dep = DepProviders { label: ":lib".into(), providers: r_prod.providers.clone() };
        let attrs = vec![("deps".to_string(), BzlValue::List(vec![BzlValue::Str(":lib".into())]))];
        let r_cons = StarlarkEvaluator::new()
            .evaluate_rule(&EvalEnv::default(), cons, "m.bzl", "my_rule", &[], "//q:t", &attrs, &[dep], &[])
            .expect("the consuming rule reads dep[MyInfo].rlib.path — the File round-trips with .path intact");
        assert_eq!(provider_field(&r_cons, "MyInfo", "p"), &BzlValue::Str("p/libx.rlib".into()), "dep[MyInfo].rlib.path is the exec path");
        assert_eq!(provider_field(&r_cons, "MyInfo", "rlib"), &BzlValue::File("p/libx.rlib".into()), "the File re-projects as a File");
    }

    /// C5 MUTANT `mutant_rule_skips_mandatory`: a `mandatory = True` attr is ENFORCED — a target supplying it
    /// passes; a target omitting it is a typed analysis error (Bazel's behavior). Under the mutant the check
    /// is skipped → the fail-closed assertion reds.
    #[test]
    fn mandatory_attr_enforced() {
        let src = "Out = provider(\"Out\", fields = [\"v\"])\n\
def _impl(ctx):\n\
\x20   return [Out(v = ctx.attr.rustc)]\n\
my_rule = rule(implementation = _impl, attrs = {\"rustc\": attr.string(mandatory = True)})\n";
        let e = StarlarkEvaluator::new();
        let with = vec![("rustc".to_string(), BzlValue::Str("/x/rustc".into()))];
        assert!(
            e.evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &with, &[], &[]).is_ok(),
            "a target supplying the mandatory attr passes"
        );
        assert!(
            e.evaluate_rule(&EvalEnv::default(), src, "m.bzl", "my_rule", &[], "//p:t", &[], &[], &[]).is_err(),
            "a target OMITTING the mandatory attr must fail closed — RED under mutant_rule_skips_mandatory"
        );
    }

    /// T20 R-load def-builtins (rows 4-5): a `.bzl` using `config.*` (all four build-setting ctors),
    /// `struct()`, and the new parse-level `rule()` kwargs (`build_setting`/`doc`/`provides`/`fragments`/
    /// `exec_groups`) EVALUATES. The build-setting markers + the struct are kept PRIVATE (`_`-prefixed): their
    /// analysis behavior is deferred AND they have no codec representation to cross a node boundary (the R-load
    /// frozen-surface STOP), so only the scalar `probe` (a struct field read) and `flag_rule` (a rule) export.
    #[test]
    fn def_builtins_config_struct_and_rule_kwargs_evaluate() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let src = "\
_int_s = config.int(flag = True)\n\
_bool_s = config.bool()\n\
_str_s = config.string(flag = True)\n\
_list_s = config.string_list(flag = True, repeatable = True)\n\
probe = struct(k = 7, name = \"x\").k\n\
def _impl(ctx):\n\
\x20   return []\n\
flag_rule = rule(implementation = _impl, build_setting = _bool_s, doc = \"d\", provides = [], fragments = [\"cpp\"], exec_groups = {})\n";
        let m = e.evaluate(&EvalEnv::default(), "m.bzl", src, &[]).expect("config/struct/rule-kwargs evaluate");
        assert_eq!(
            m.bindings.iter().find(|(n, _)| n == "probe").map(|(_, v)| v),
            Some(&BzlValue::Int(7)),
            "struct() constructs and its field read exports as a scalar"
        );
        assert!(
            m.bindings.iter().any(|(n, v)| n == "flag_rule" && matches!(v, BzlValue::Rule(_))),
            "a rule() taking build_setting/doc/provides/fragments/exec_groups is defined + exported"
        );
    }

    // ── T20 R-load-codec: the live-module bridge (functions + structs cross the BZL_LOAD boundary) ──

    /// A `.bzl`-exported function crosses the load boundary as a `FunctionRef` (identity, never the body) and
    /// is re-materialized as a REAL callable by the live-module bridge: a sibling module `load()`s it and
    /// CALLS it at load time, seeing the real result.
    #[test]
    fn loaded_function_crosses_boundary_and_is_callable() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let a = e
            .evaluate(&EvalEnv::default(), "a.bzl", "def greet():\n    return \"hi\"\n", &[])
            .expect("A evaluates (caches its frozen module for the bridge)");
        assert!(matches!(a.get("greet"), Some(BzlValue::FunctionRef(_))), "A exports greet as a FunctionRef");
        let b = e
            .evaluate(
                &EvalEnv::default(),
                "b.bzl",
                "load(\"a.bzl\", \"greet\")\nmsg = greet()\n",
                &[("a.bzl".to_string(), a)],
            )
            .expect("B evaluates, calling the loaded function at load time");
        assert_eq!(b.get("msg"), Some(&BzlValue::Str("hi".into())), "the loaded function really ran through the bridge");
    }

    /// The re-evaluation gate (mutant `mutant_live_module_cache_ignores_digest`): editing the DEFINING
    /// module's function body must re-fingerprint it so a dependent that CALLS the function sees the new
    /// behavior (module-content-level early cutoff, the same granularity as Bazel). Under the mutant the
    /// bridge cache ignores the defining digest and serves the stale v1 module → this goes red.
    #[test]
    fn loaded_function_reeval_sees_new_body() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let run = |src_a: &str| -> BzlValue {
            let a = e.evaluate(&EvalEnv::default(), "a.bzl", src_a, &[]).expect("A evaluates");
            let b = e
                .evaluate(
                    &EvalEnv::default(),
                    "b.bzl",
                    "load(\"a.bzl\", \"greet\")\nmsg = greet()\n",
                    &[("a.bzl".to_string(), a)],
                )
                .expect("B evaluates");
            b.get("msg").cloned().expect("msg is exported")
        };
        assert_eq!(run("def greet():\n    return \"v1\"\n"), BzlValue::Str("v1".into()), "first body observed");
        assert_eq!(
            run("def greet():\n    return \"v2\"\n"),
            BzlValue::Str("v2".into()),
            "after editing A's function body, B must see the NEW behavior (not a stale cached module)"
        );
    }

    /// The rules_rust `rust_common = struct(create_crate_info = _create_crate_info, default_version = \"…\")`
    /// shape: a struct whose fields mix a (private) FUNCTION and DATA crosses the load boundary. A sibling
    /// reads the data field AND calls the struct-field function (materialized by the bridge under the
    /// function's own private name).
    #[test]
    fn loaded_struct_field_function_crosses_and_data_roundtrips() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let a_src = "def _mk():\n    return \"made\"\nbundle = struct(mk = _mk, tag = \"T\")\n";
        let a = e.evaluate(&EvalEnv::default(), "a.bzl", a_src, &[]).expect("A evaluates");
        match a.get("bundle") {
            Some(BzlValue::Struct(fields)) => {
                assert!(
                    fields.iter().any(|(n, v)| n == "mk" && matches!(v, BzlValue::FunctionRef(_))),
                    "the struct's function field surfaces as a FunctionRef"
                );
                assert!(
                    fields.iter().any(|(n, v)| n == "tag" && matches!(v, BzlValue::Str(s) if s == "T")),
                    "the struct's data field crosses as a Str"
                );
            }
            other => panic!("bundle must surface as a Struct, got {other:?}"),
        }
        let b = e
            .evaluate(
                &EvalEnv::default(),
                "b.bzl",
                "load(\"a.bzl\", \"bundle\")\nt = bundle.tag\nmade = bundle.mk()\n",
                &[("a.bzl".to_string(), a)],
            )
            .expect("B evaluates, reading + calling struct fields across the load boundary");
        assert_eq!(b.get("t"), Some(&BzlValue::Str("T".into())), "struct data field read across the boundary");
        assert_eq!(b.get("made"), Some(&BzlValue::Str("made".into())), "struct-field function called across the boundary");
    }

    /// Function identity is MODULE-SCOPED end to end: two modules export a same-named `f` with different
    /// behavior; a consumer loading BOTH and calling each gets the RIGHT one (a name-only ref would alias
    /// them — the codec mutant `mutant_function_ref_drops_module` is the red twin at the codec layer).
    #[test]
    fn loaded_function_identity_is_module_scoped() {
        use razel_bzl_api::BzlValue;
        let e = StarlarkEvaluator::new();
        let m1 = e.evaluate(&EvalEnv::default(), "m1.bzl", "def f():\n    return 1\n", &[]).expect("m1");
        let m2 = e.evaluate(&EvalEnv::default(), "m2.bzl", "def f():\n    return 2\n", &[]).expect("m2");
        let c = e
            .evaluate(
                &EvalEnv::default(),
                "c.bzl",
                "load(\"m1.bzl\", f1 = \"f\")\nload(\"m2.bzl\", f2 = \"f\")\na = f1()\nb = f2()\n",
                &[("m1.bzl".to_string(), m1), ("m2.bzl".to_string(), m2)],
            )
            .expect("C evaluates, calling a same-named function from two modules");
        assert_eq!(c.get("a"), Some(&BzlValue::Int(1)), "f from m1 returns 1");
        assert_eq!(c.get("b"), Some(&BzlValue::Int(2)), "f from m2 returns 2 (module-scoped, never name-aliased)");
    }
}
