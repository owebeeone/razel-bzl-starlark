//! NAMED, precomputed, digested per-phase environments (the ADR-0003 phase-env lockdown §3). The spike's
//! two ad-hoc, rebuilt-per-call Globals are replaced by one [`PhaseEnv`] per matrix row that v1 builds:
//! `EnvBuildBzl` (rows 1-2 — the `.bzl`-for-BUILD env) and `EnvBuildFile` (row 7 — the BUILD-file env).
//! Each env is built ONCE (`Globals(Arc<GlobalsData>)` is immutable + cheaply shared), carries its own
//! per-phase parse [`Dialect`], and produces its [`PredeclaredEnvId`] once, deterministically, from the
//! DECLARED registry table below — never from live heap enumeration (`Globals::iter()` is not a
//! cross-build encoding; R1). Rows 3-6 (`Builtins`/`Bzlmod`/`BzlmodBootstrap`/`Scl`) have no built env in
//! v1: the evaluator fails closed on them (their env TAGS are already pinned in `razel-bzl-api`).
//!
//! Phase separation is thereby ENVIRONMENTAL: the BUILD-file env does not contain `rule`/`provider`/
//! `attr`/`declare_action`, and the `.bzl` env does not contain `target`. The `eval.extra` registry
//! fail-closes stay as belt-and-braces, no longer the only wall.

use crate::globals::{action_global, attr_namespace, build_globals, provider_global, rule_global};
use razel_bzl_api::{derive_predeclared_env_id, EnvEntry, EnvTag, PredeclaredEnvId};
use starlark::environment::{Globals, GlobalsBuilder};
use starlark::syntax::Dialect;
use std::sync::OnceLock;

/// One named phase environment: the frozen Globals, the phase's parse dialect, and the env identity.
pub(crate) struct PhaseEnv {
    pub(crate) globals: Globals,
    pub(crate) dialect: Dialect,
    pub(crate) env_id: PredeclaredEnvId,
}

/// The DECLARED registry of `EnvBuildBzl` (rows 1-2): every razel-registered `.bzl` toplevel as a
/// `(name, builtin-identity, builtin-version)` triple. The interpreter universe (`len`, `print`, …) is
/// excluded per the §1 matrix (all rows exclude it). Editing a builtin's observable behavior BUMPS its
/// version here — that is what re-fingerprints the env (R1), not a heap iteration.
pub(crate) const ENV_BUILD_BZL_TABLE: &[(&str, &str, &str)] = &[
    ("attr", "razel.attr", "1"),
    ("declare_action", "razel.declare_action", "1"),
    ("provider", "razel.provider", "1"),
    ("rule", "razel.rule", "1"),
    ("write_file", "razel.write_file", "1"),
];

/// The DECLARED registry of `EnvBuildFile` (row 7): the BUILD-file toplevels.
pub(crate) const ENV_BUILD_FILE_TABLE: &[(&str, &str, &str)] = &[("target", "razel.target", "1")];

/// Materialize a declared table as the api's `EnvEntry` enumeration (the derivation input).
pub(crate) fn entries(table: &[(&str, &str, &str)]) -> Vec<EnvEntry> {
    table
        .iter()
        .map(|(n, i, v)| EnvEntry { name: (*n).to_owned(), identity: (*i).to_owned(), version: (*v).to_owned() })
        .collect()
}

/// The `.bzl` parse dialect (rows 1-5): the standard set, as before.
fn bzl_dialect() -> Dialect {
    Dialect::Standard
}

/// The BUILD-file parse dialect (row 7): no `def`, no `lambda` — Bazel's BUILD dialect forbids function
/// definitions. This closes the spike's admitted gap ("the Standard dialect also permits `def`").
fn build_dialect() -> Dialect {
    Dialect { enable_def: false, enable_lambda: false, ..Dialect::Standard }
}

/// Build a phase env: the id comes from the DECLARED table via the api's canonical derivation (v1 passes
/// no injected-builtins value — the fold slot's sentinel; a live `STARLARK_BUILTINS` node later supplies a
/// `BuiltinsDigest` here, additively). MUTANT `mutant_env_digest_from_heap_iteration`: the id is instead
/// derived from the live `Globals` name enumeration — heap/seam bytes (interpreter universe included,
/// identities and versions lost) — the exact seam leak the `predeclared_env_id_is_canonical` gate kills.
fn make_env(tag: EnvTag, table: &[(&str, &str, &str)], globals: Globals, dialect: Dialect) -> PhaseEnv {
    let env_id = if cfg!(feature = "mutant_env_digest_from_heap_iteration") {
        let heap: Vec<EnvEntry> = globals
            .names()
            .map(|n| EnvEntry { name: n.as_str().to_owned(), identity: String::new(), version: String::new() })
            .collect();
        derive_predeclared_env_id(tag, &heap, None)
    } else {
        derive_predeclared_env_id(tag, &entries(table), None)
    };
    PhaseEnv { globals, dialect, env_id }
}

/// `EnvBuildBzl` (rows 1-2): standard + `rule()` + `provider()` + `declare_action()` + the `attr`
/// namespace. Shared by BOTH `Build{is_prelude:*}` kinds (R1: prelude-ness is a LoadKind bit, not an env)
/// and by module load AND rule-impl re-evaluation (the same row-1 environment).
pub(crate) fn env_build_bzl() -> &'static PhaseEnv {
    if cfg!(feature = "mutant_one_globals_all_loadkinds") {
        return shared_env();
    }
    static E: OnceLock<PhaseEnv> = OnceLock::new();
    E.get_or_init(|| {
        let globals = GlobalsBuilder::standard()
            .with(rule_global)
            .with(provider_global)
            .with(action_global)
            .with_namespace("attr", attr_namespace)
            .build();
        make_env(EnvTag::EnvBuildBzl, ENV_BUILD_BZL_TABLE, globals, bzl_dialect())
    })
}

/// `EnvBuildFile` (row 7): standard + the BUILD-only `target()` builtin, under the def-less BUILD dialect.
pub(crate) fn env_build_file() -> &'static PhaseEnv {
    if cfg!(feature = "mutant_one_globals_all_loadkinds") {
        return shared_env();
    }
    static E: OnceLock<PhaseEnv> = OnceLock::new();
    E.get_or_init(|| {
        let globals = GlobalsBuilder::standard().with(build_globals).build();
        make_env(EnvTag::EnvBuildFile, ENV_BUILD_FILE_TABLE, globals, build_dialect())
    })
}

/// MUTANT SHAPE (`mutant_one_globals_all_loadkinds`): the spike's ONE ad-hoc Globals served for every
/// phase — `.bzl` toplevels and `target()` in a single env, one id, one permissive dialect. Restores the
/// exact surface §4.6 branded "structurally INCAPABLE"; the phase-separation gates must go red under it.
fn shared_env() -> &'static PhaseEnv {
    static E: OnceLock<PhaseEnv> = OnceLock::new();
    E.get_or_init(|| {
        let globals = GlobalsBuilder::standard()
            .with(rule_global)
            .with(provider_global)
            .with(action_global)
            .with(build_globals)
            .with_namespace("attr", attr_namespace)
            .build();
        let mut table: Vec<(&str, &str, &str)> = ENV_BUILD_BZL_TABLE.to_vec();
        table.extend_from_slice(ENV_BUILD_FILE_TABLE);
        make_env(EnvTag::EnvBuildBzl, &table, globals, Dialect::Standard)
    })
}
