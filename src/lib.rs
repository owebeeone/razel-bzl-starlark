//! `razel-bzl-starlark` — the `BzlEvaluator` impl over `starlark-rust`. Parses/evaluates a `.bzl`'s module
//! body, resolves `load()` against caller-supplied modules (rebuilt as `FrozenModule`s and served via a
//! `ReturnFileLoader`), and projects the exports into the codec-neutral `BzlModule`. The codec-neutral model
//! is what makes early cutoff work; the frozen-module round-trip is lossless for the spike's value kinds
//! (None/Bool/Int (full i64)/Str/List) plus `rule()` definitions (`BzlValue::Rule`).
//!
//! `rule()` machinery (A1): a `.bzl` defines `my_rule = rule(implementation=…, attrs=…)`; the BUILD `load()`s and
//! calls it, recording a target carrying the rule's ORIGIN (defining `.bzl` + symbol).
//!
//! Rule EVALUATION (A2, the analysis seam): `evaluate_rule` re-evaluates the rule's `.bzl` in ONE fresh heap,
//! builds a `ctx` (native `struct`: `ctx.label`, `ctx.attr.<name>`; label attrs → a list of native `dict`s
//! `{Provider: instance}`), invokes the live impl with `eval_function`, and projects the returned provider
//! instances to codec-neutral `ProviderInstance`. Because the impl is invoked in the SAME heap it was defined in,
//! no frozen value crosses a heap boundary (no `add_reference`/GC caveat). `RuleValue` (holds the impl) and
//! `ProviderInstanceValue` (holds field values) are COMPLEX values; `Provider`/`RuleProxy`/`AttrTypeValue` are
//! SIMPLE. Provider identity is the declared NAME (minimal, by-type; no merge-algebra assumptions — ADR-0004).

/// The named, precomputed, digested per-phase environments (lockdown §3).
mod envs;

/// The `ctx.actions` surface (`run`/`write`/`declare_file`/`args`) — replaces the deleted globals (C4).
mod actions;
/// The live-module bridge (T20 R-load-codec): content-hash + the frozen-module cache keyed by
/// (module path, defining_digest) that re-materializes loaded functions/structs.
mod bridge;
/// Value↔heap projection: `convert`/`alloc`/`build_frozen`/`index_providers`.
mod convert;
/// The `BzlEvaluator` impl (`evaluate`/`evaluate_build`/`evaluate_rule`) + phase-env selection.
mod eval;
/// The registrar builtins (`rule()`/`provider()`/`target()`/`depset()`/`attr.*`) + their registries.
mod globals;
/// The def-phase (load-time) builtins that DECLARE analysis constructs (`config.*` build settings,
/// `aspect()`, `transition()`, `configuration_field()`, `config_common`) — parse/eval-level, behavior deferred.
mod globals_def;
/// MODULE.bazel evaluation (D6): the module-dialect env (`module`/`register_toolchains`/`use_repo_rule`).
mod module_file;
/// The custom Starlark values (`RuleValue`/`Provider`/`ProviderInstanceValue`/`RuleProxy`/attr markers).
mod values;
/// `ctx.actions.args()` — the Args builder (C4).
mod values_args;
/// The `LoadedFunction` value (T20 R-load-codec, tag 10 alloc form) — a bridge-resolved callable.
mod values_function;
/// The live `depset` value + constructor + `.to_list()` (C2).
mod values_depset;
/// The `File` value (`.path`/`.dirname`/`.basename`) (C3).
mod values_file;
/// The `Label` value (`.package`/`.name`/`.workspace_name`/`.repo_name`) + exec-dir parsing (C1).
mod values_label;
/// The `Target` value (row 6): `ctx.attr.<label-attr>` = Target (`t[Provider]`, `.label`, `.files` depset).
mod values_target;
/// The `ctx` value (row 9): fields (label/attr/…/var/bin_dir/…/configuration) + the expand_location/
/// expand_make_variables methods.
mod values_ctx;

#[cfg(test)]
mod tests;

/// The `starlark-rust`-backed `BzlEvaluator`. Carries the live-module bridge cache (T20 R-load-codec): the
/// frozen live module of every `.bzl` it has evaluated, keyed by `(path, defining_digest)`, so a module that
/// `load()`s and CALLS a function/struct-field-function from another module resolves the real callable. The
/// cache is a cheap `Arc` handle — cloning the evaluator (or sharing it via `Arc`, as the engine does) shares
/// one cache. `Send + Sync` (the `BzlEvaluator` bound): the cache is a `Mutex` over `Send + Sync`
/// `FrozenModule`s.
#[derive(Clone, Default)]
pub struct StarlarkEvaluator {
    bridge: bridge::ModuleBridge,
}

impl StarlarkEvaluator {
    pub fn new() -> Self {
        StarlarkEvaluator::default()
    }
}

