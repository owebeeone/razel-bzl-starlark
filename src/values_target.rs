//! `Target` — the row-6 value that `ctx.attr.<label-attr>` yields (reconciling the C3 Files-vs-dict shim to
//! Bazel semantics). A Bazel `Target` (a "configured target" as seen by a dependent's rule impl) supports:
//!   * `target[SomeProvider]` — provider indexing (the SAME thing the old per-dep `{Provider: instance}` dict
//!     did, so `dep[RustInfo]` in rust.bzl keeps working UNCHANGED — a dict and a Target both index by a
//!     Provider key via `ProviderId`'s identity Eq),
//!   * `target.label` — a `Label` object,
//!   * `target.files` — a `depset[File]` (the target's default outputs = its `DefaultInfo.files`).
//!
//! Provider keys are the live `Provider` values (from the impl eval's `providers_by_id`), so indexing rides
//! `Provider::equals` (the C2 identity funnel) — a bzl-differing identity misses, fail-closed, never fused.
//! A SOURCE-file target (an `allow_files` attr entry) carries `.files = depset([the File])` + `.label` and NO
//! indexable providers (indexing one fails closed). MUTANT `mutant_target_files_not_depset`: `.files` returns a
//! flat list instead of a depset → a probe that flattens `target.files.to_list()` (or feeds it to a depset)
//! fails closed.

use allocative::Allocative;
use starlark::starlark_complex_value;
use starlark::values::{
    starlark_value, Coerce, Freeze, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Trace,
    Value, ValueLifetimeless, ValueLike,
};
use std::fmt;

use crate::eval::starlark_err;

/// A `Target` (row 6): the dependency as a dependent's rule impl sees it. `provider_keys`/`provider_instances`
/// are PARALLEL (key i indexes instance i) — the live Provider value + its instance, for `target[Provider]`.
/// `label` is a `LabelValue`; `files` is a `depset[File]` (the `DefaultInfo.files`, or an empty depset).
#[derive(Debug, Trace, Coerce, Freeze, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct TargetValueGen<V: ValueLifetimeless> {
    pub(crate) label: V,
    pub(crate) provider_keys: Vec<V>,
    pub(crate) provider_instances: Vec<V>,
    pub(crate) files: V,
}
starlark_complex_value!(pub(crate) TargetValue);
impl<V: ValueLifetimeless> fmt::Display for TargetValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // `V` (a lifetimeless value) has no `Display` reachable here; the label text is available live via
        // `.label` (a `Label`, which Displays). Keep the type-tag rendering (like `depset(...)`).
        write!(f, "<target>")
    }
}
#[starlark_value(type = "Target")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for TargetValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    /// `target[Provider]` — return the instance whose provider key matches `index` by identity (the C2 funnel,
    /// via `Provider::equals`). Fail-closed (Bazel raises) when the target does not provide it — never `None`.
    fn at(&self, index: Value<'v>, _heap: Heap<'v>) -> starlark::Result<Value<'v>> {
        for (k, inst) in self.provider_keys.iter().zip(self.provider_instances.iter()) {
            if k.to_value().equals(index)? {
                return Ok(inst.to_value());
            }
        }
        Err(starlark_err(format!("target {} does not provide {}", self.label.to_value(), index)))
    }
    fn get_attr(&self, attribute: &str, _heap: Heap<'v>) -> Option<Value<'v>> {
        match attribute {
            "label" => Some(self.label.to_value()),
            // `.files` is a depset[File] (DefaultInfo.files). RED under `mutant_target_files_not_depset` (which
            // surfaces a flat list here), so a consumer feeding it to `depset(transitive=[t.files])` breaks.
            "files" => Some(self.files.to_value()),
            _ => None, // fail closed — a Target exposes label/files + provider indexing, nothing else in v1.
        }
    }
    fn dir_attr(&self) -> Vec<String> {
        vec!["files".to_owned(), "label".to_owned()]
    }
}
