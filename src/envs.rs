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
//! `attr`/`depset`, and the `.bzl` env does not contain `target`. The `eval.extra` registry
//! fail-closes stay as belt-and-braces, no longer the only wall.

use crate::globals::{
    attr_namespace, build_globals, default_info_provider, label_global, output_group_info_provider,
    provider_global, rule_global, run_environment_info_provider, select_global, NativeValue, DEFAULT_INFO_NAME,
    OUTPUT_GROUP_INFO_NAME, RUN_ENVIRONMENT_INFO_NAME,
};
use crate::globals_def::{config_common_namespace, config_namespace, coverage_common_namespace, def_markers_global};
use crate::values::PlatformCommon;
use crate::values_depset::depset_global;
use razel_bzl_api::{derive_predeclared_env_id, EnvEntry, EnvTag, PredeclaredEnvId};
use starlark::environment::{Globals, GlobalsBuilder, LibraryExtension};
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
    ("DefaultInfo", "razel.DefaultInfo", "2"), // C5: files→depset[File] + executable → observable, version bumped.
    ("attr", "razel.attr", "4"), // T20 R-load: +string_dict/string_list_dict/label_keyed_string_dict (was C3/C5 v3).
    // C4 (D5): `declare_action`/`write_file` are DELETED — their behavior is on `ctx.actions.*` (not globals,
    // so not in the env table). `depset` (C2) is a NEW global. `platform_common` (C6) is the newest — its
    // `.ToolchainInfo` is the schemaless toolchain provider. The env id re-fingerprints (no goldens).
    ("depset", "razel.depset", "1"),
    // T20 R-load: `platform_common.TemplateVariableInfo` added alongside `.ToolchainInfo` → observable, bumped.
    ("platform_common", "razel.platform_common", "2"),
    ("provider", "razel.provider", "2"), // C5: doc/dict-fields kwargs + optional name → observable, bumped.
    ("rule", "razel.rule", "4"), // T20 R-load: +test/cfg/**extra kwargs (was build_setting/…/doc at v3) → bumped.
    // T20 R-load def-phase builtins (rows 4-5), added strictly by the demand trace. `config` (build settings)
    // is the first — bazel_skylib's common_settings.bzl declares build_setting rules at load. Each new global
    // re-fingerprints the env additively (the id is derived from THIS table, never heap enumeration).
    ("config", "razel.config", "1"),
    // `config_common.toolchain_type()` (T20 R-load) — rules_cc's `use_cc_toolchain()` builds one.
    ("config_common", "razel.config_common", "1"),
    // `struct()` (rules_rust's `rust_common`/`triple.bzl` build structs at load) — starlark-rust's
    // `LibraryExtension::StructType`, enabled on the `.bzl` base builder (NOT a razel builtin fn).
    ("struct", "starlark.struct", "1"),
    // `json` (T20 R-load): the Starlark json builtin module (`json.encode_indent` in rust_analyzer.bzl) —
    // starlark-rust's `LibraryExtension::Json`, a pure/deterministic builtin. Additive row → env re-fingerprints.
    ("json", "starlark.json", "1"),
    // `Label()` (T20 R-load): the load-time Label constructor rules_cc/rules_rust use for toolchain-type +
    // dep constants. Additive row → env re-fingerprints.
    ("Label", "razel.Label", "1"),
    // `coverage_common` (T20 R-load): the predeclared coverage namespace. rules_rust's rustc.bzl references
    // `coverage_common.instrumented_files_info(...)` inside the library/binary impl; the name must resolve at
    // load. Analysis behavior (coverage instrumentation) is deferred (row 12) — an opaque marker. Additive row.
    ("coverage_common", "razel.coverage_common", "1"),
    // `OutputGroupInfo` (T20 R-load): the predeclared schemaless output-group provider. rustc.bzl builds
    // `OutputGroupInfo(**output_group_info)` in the library/binary impl. Additive row → env re-fingerprints.
    ("OutputGroupInfo", "razel.OutputGroupInfo", "1"),
    // `aspect`/`transition`/`configuration_field` (T20 R-load, row 5 def markers): declared at module scope by
    // rules_rust (aspects are RE-EXPORTED by defs.bzl). Opaque deferred markers (row 12); each additive row
    // re-fingerprints the env.
    ("aspect", "razel.aspect", "1"),
    ("transition", "razel.transition", "1"),
    ("configuration_field", "razel.configuration_field", "1"),
    // `RunEnvironmentInfo` (T20 R-load): the predeclared schemaless run-environment provider (rustfmt.bzl test
    // targets build one). `platform_common.TemplateVariableInfo` rides the existing `platform_common` global
    // (version bumped below), so it needs no table row of its own. Additive row → env re-fingerprints.
    ("RunEnvironmentInfo", "razel.RunEnvironmentInfo", "1"),
    // `native` (T20 R-load): the BUILD/macro namespace referenced by rules_rust macros (`native.test_suite`).
    // Fail-closed on a call (deferred macro construct, row 12). Additive row → env re-fingerprints.
    ("native", "razel.native", "1"),
    // `select()` (T20 select): Bazel's configurable-attribute selector — a first-class UNRESOLVED value in
    // BOTH envs (rulesets build selects in `.bzl` too). Additive row → env re-fingerprints.
    ("select", "razel.select", "1"),
];

/// The DECLARED registry of `EnvBuildFile` (row 7): the BUILD-file toplevels. C6 adds the native
/// `toolchain_type`/`toolchain` declarations (the honest toolchain-resolution graph path reads them).
pub(crate) const ENV_BUILD_FILE_TABLE: &[(&str, &str, &str)] = &[
    // `alias` (T19-P2): the native forwarding rule Bazel has as a builtin — the vendored-crates hub package
    // (`crates/BUILD.bazel`) is all `alias()` calls, so a BUILD loading it must parse under both
    // tools. Analysis forwards the `actual`'s providers (razel-analysis). Additive row → env re-fingerprints.
    ("alias", "razel.alias", "1"),
    // `glob()` (T20 TF-unblocker A): the source-file globber, serviced two-pass by the PACKAGE node. Additive
    // BUILD builtin → env re-fingerprints.
    ("glob", "razel.glob", "1"),
    // `select()` (T20 select): the same first-class selector, available in BUILD attr positions
    // (crate_universe emits `deps = select({...})`). Additive BUILD builtin → env re-fingerprints.
    ("select", "razel.select", "1"),
    // `config_setting`/`constraint_setting`/`constraint_value` (T20 select): the native config/constraint
    // decls a select condition + the @platforms/rules_rust platform BUILDs use. Additive → env re-fingerprints.
    ("config_setting", "razel.config_setting", "1"),
    ("constraint_setting", "razel.constraint_setting", "1"),
    ("constraint_value", "razel.constraint_value", "1"),
    ("target", "razel.target", "1"),
    ("toolchain", "razel.toolchain", "1"),
    ("toolchain_type", "razel.toolchain_type", "1"),
];

/// Materialize a declared table as the api's `EnvEntry` enumeration (the derivation input).
pub(crate) fn entries(table: &[(&str, &str, &str)]) -> Vec<EnvEntry> {
    table
        .iter()
        .map(|(n, i, v)| EnvEntry { name: (*n).to_owned(), identity: (*i).to_owned(), version: (*v).to_owned() })
        .collect()
}

/// The `.bzl` parse dialect (rows 1-5): the standard set PLUS keyword-only arguments (`def f(a, *, kw=…)`),
/// which Bazel's Starlark permits and real rulesets use heavily (rules_rust's `can_build_metadata(toolchain,
/// ctx, crate_type, *, disable_pipelining = False)`). `Dialect::Standard` disables it; enabling it is a
/// Bazel-fidelity fix, not a relaxation of BUILD-file rules (the BUILD dialect is unaffected).
fn bzl_dialect() -> Dialect {
    Dialect { enable_keyword_only_arguments: true, ..Dialect::Standard }
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

/// `EnvBuildBzl` (rows 1-2): standard + `rule()` + `provider()` + `depset()` + the `attr`
/// namespace. Shared by BOTH `Build{is_prelude:*}` kinds (R1: prelude-ness is a LoadKind bit, not an env)
/// and by module load AND rule-impl re-evaluation (the same row-1 environment).
pub(crate) fn env_build_bzl() -> &'static PhaseEnv {
    if cfg!(feature = "mutant_one_globals_all_loadkinds") {
        return shared_env();
    }
    static E: OnceLock<PhaseEnv> = OnceLock::new();
    E.get_or_init(|| {
        // `print` (T20 R-load): rules_rust's toolchain.bzl calls `print(...)` in a function body — an
        // interpreter-universe debug builtin (no build-output effect), EXCLUDED from the digest table per §1
        // (like `len`), enabled here only so the name resolves. `Json`/`StructType` DO ride the table (semantic).
        let globals = GlobalsBuilder::extended_by(&[
            LibraryExtension::StructType,
            LibraryExtension::Json,
            LibraryExtension::Print,
        ])
            .with(rule_global)
            .with(provider_global)
            .with(depset_global)
            .with(label_global)
            .with(select_global)
            .with(|b: &mut GlobalsBuilder| b.set(DEFAULT_INFO_NAME, default_info_provider()))
            .with(|b: &mut GlobalsBuilder| b.set(OUTPUT_GROUP_INFO_NAME, output_group_info_provider()))
            .with(|b: &mut GlobalsBuilder| b.set(RUN_ENVIRONMENT_INFO_NAME, run_environment_info_provider()))
            .with(|b: &mut GlobalsBuilder| b.set("platform_common", PlatformCommon))
            .with(|b: &mut GlobalsBuilder| b.set("native", NativeValue))
            .with(def_markers_global)
            .with_namespace("attr", attr_namespace)
            .with_namespace("config", config_namespace)
            .with_namespace("config_common", config_common_namespace)
            .with_namespace("coverage_common", coverage_common_namespace)
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
        let globals = GlobalsBuilder::standard().with(build_globals).with(select_global).build();
        make_env(EnvTag::EnvBuildFile, ENV_BUILD_FILE_TABLE, globals, build_dialect())
    })
}

/// MUTANT SHAPE (`mutant_one_globals_all_loadkinds`): the spike's ONE ad-hoc Globals served for every
/// phase — `.bzl` toplevels and `target()` in a single env, one id, one permissive dialect. Restores the
/// exact surface §4.6 branded "structurally INCAPABLE"; the phase-separation gates must go red under it.
fn shared_env() -> &'static PhaseEnv {
    static E: OnceLock<PhaseEnv> = OnceLock::new();
    E.get_or_init(|| {
        // `print` (T20 R-load): rules_rust's toolchain.bzl calls `print(...)` in a function body — an
        // interpreter-universe debug builtin (no build-output effect), EXCLUDED from the digest table per §1
        // (like `len`), enabled here only so the name resolves. `Json`/`StructType` DO ride the table (semantic).
        let globals = GlobalsBuilder::extended_by(&[
            LibraryExtension::StructType,
            LibraryExtension::Json,
            LibraryExtension::Print,
        ])
            .with(rule_global)
            .with(provider_global)
            .with(depset_global)
            .with(label_global)
            .with(select_global)
            .with(|b: &mut GlobalsBuilder| b.set(DEFAULT_INFO_NAME, default_info_provider()))
            .with(|b: &mut GlobalsBuilder| b.set(OUTPUT_GROUP_INFO_NAME, output_group_info_provider()))
            .with(|b: &mut GlobalsBuilder| b.set(RUN_ENVIRONMENT_INFO_NAME, run_environment_info_provider()))
            .with(|b: &mut GlobalsBuilder| b.set("platform_common", PlatformCommon))
            .with(|b: &mut GlobalsBuilder| b.set("native", NativeValue))
            .with(build_globals)
            .with(def_markers_global)
            .with_namespace("attr", attr_namespace)
            .with_namespace("config", config_namespace)
            .with_namespace("config_common", config_common_namespace)
            .with_namespace("coverage_common", coverage_common_namespace)
            .build();
        let mut table: Vec<(&str, &str, &str)> = ENV_BUILD_BZL_TABLE.to_vec();
        table.extend_from_slice(ENV_BUILD_FILE_TABLE);
        make_env(EnvTag::EnvBuildBzl, &table, globals, Dialect::Standard)
    })
}
