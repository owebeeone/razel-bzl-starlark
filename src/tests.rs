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
}
