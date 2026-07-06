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

/// Value↔heap projection: `convert`/`alloc`/`build_frozen`/`index_providers`.
mod convert;
/// The `BzlEvaluator` impl (`evaluate`/`evaluate_build`/`evaluate_rule`) + phase-env selection.
mod eval;
/// The registrar builtins (`rule()`/`provider()`/`target()`/`declare_action`/`attr.*`) + their registries.
mod globals;
/// The custom Starlark values (`RuleValue`/`Provider`/`ProviderInstanceValue`/`RuleProxy`/attr markers).
mod values;

#[cfg(test)]
mod tests;

pub struct StarlarkEvaluator;

impl StarlarkEvaluator {
    pub fn new() -> Self {
        StarlarkEvaluator
    }
}
impl Default for StarlarkEvaluator {
    fn default() -> Self {
        Self::new()
    }
}

