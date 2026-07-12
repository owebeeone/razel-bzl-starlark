//! `select()` — Bazel's configurable-attribute selector, as a FIRST-CLASS load-time value (T20 select). A
//! `select({condition: value, …})` is NEVER resolved during BUILD/.bzl evaluation: it is carried as an
//! unresolved [`SelectValue`], crosses the PACKAGE boundary as [`razel_bzl_api::BzlValue::Select`], and is
//! resolved at ANALYSIS against the target's configuration (the locus that owns constraint matching). The `+`
//! operator on selects/lists builds a [`SelectorListValue`] (Bazel's SelectorList): `["//a"] + select({…})`
//! and `select({…}) + select({…})` concatenate — each arm resolved independently, then joined.
//!
//! The branch VALUES are held LIVE (`Vec<(String, Value)>`) and converted to codec-neutral form only at the
//! boundary (`crate::convert`), so a select over any attr-legal value (lists of label strings, string lists,
//! dicts) round-trips without an eager projection here.

use allocative::Allocative;
use starlark::values::dict::DictRef;
use starlark::values::{
    starlark_value, Coerce, Freeze, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Trace,
    Value, ValueLifetimeless, ValueLike,
};
use starlark::starlark_complex_value;
use std::fmt;

/// A single `select({condition: value, …}, no_match_error = "…")`. `conditions` are (condition-label, live
/// value) pairs, SORTED by label at construction (a select dict is order-independent for matching → the
/// canonical form is label-sorted, matching the tag-15 codec frame). `no_match_error` is Bazel's
/// `select(no_match_error=)` message (`""` = razel's default). A COMPLEX value (holds live `V` branch values).
#[derive(Debug, Trace, Coerce, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct SelectValueGen<V: ValueLifetimeless> {
    pub(crate) conditions: Vec<(String, V)>,
    pub(crate) no_match_error: String,
}
starlark_complex_value!(pub(crate) SelectValue);
impl<V: ValueLifetimeless> fmt::Display for SelectValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "select({} conditions)", self.conditions.len())
    }
}
// Manual Freeze (not derived): freeze each live branch value; the label strings + no_match_error move as-is.
impl<'v> Freeze for SelectValueGen<Value<'v>> {
    type Frozen = SelectValueGen<starlark::values::FrozenValue>;
    fn freeze(self, freezer: &starlark::values::Freezer) -> starlark::values::FreezeResult<Self::Frozen> {
        let conditions = self
            .conditions
            .into_iter()
            .map(|(k, v)| Ok((k, v.freeze(freezer)?)))
            .collect::<starlark::values::FreezeResult<Vec<_>>>()?;
        Ok(SelectValueGen { conditions, no_match_error: self.no_match_error })
    }
}
#[starlark_value(type = "select")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for SelectValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    /// `select(...) + rhs` — Bazel's SelectorList concatenation. `rhs` is a list/tuple/scalar (a Concrete arm),
    /// another `select(...)` (a Branch arm), or a SelectorList (its arms are spliced in). Produces a
    /// [`SelectorListValue`]; NEVER resolves (resolution is analysis).
    fn add(&self, rhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms = vec![reclone_select(self, heap)];
        splice_arm(&mut arms, rhs, heap);
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
    /// `lhs + select(...)` — the `radd` half (e.g. `["//a"] + select({…})`): `lhs` is a Concrete arm prepended
    /// before this select's Branch arm.
    fn radd(&self, lhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms = Vec::new();
        splice_arm(&mut arms, lhs, heap);
        arms.push(reclone_select(self, heap));
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
}

/// A `+`-concatenation of select/list arms (Bazel's SelectorList). Each `arm` is EITHER a [`SelectValue`] (a
/// Branch) or a plain value (a Concrete operand); the split is recovered by downcast at [`crate::convert`].
/// Arms are FLATTENED at construction (a SelectorList arm never nests). A COMPLEX value.
#[derive(Debug, Trace, Coerce, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct SelectorListValueGen<V: ValueLifetimeless> {
    pub(crate) arms: Vec<V>,
}
starlark_complex_value!(pub(crate) SelectorListValue);
impl<V: ValueLifetimeless> fmt::Display for SelectorListValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "selector_list({} arms)", self.arms.len())
    }
}
impl<'v> Freeze for SelectorListValueGen<Value<'v>> {
    type Frozen = SelectorListValueGen<starlark::values::FrozenValue>;
    fn freeze(self, freezer: &starlark::values::Freezer) -> starlark::values::FreezeResult<Self::Frozen> {
        let arms = self.arms.into_iter().map(|v| v.freeze(freezer)).collect::<starlark::values::FreezeResult<Vec<_>>>()?;
        Ok(SelectorListValueGen { arms })
    }
}
#[starlark_value(type = "selector_list")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for SelectorListValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    fn add(&self, rhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms: Vec<Value<'v>> = self.arms.iter().map(|a| a.to_value()).collect();
        splice_arm(&mut arms, rhs, heap);
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
    fn radd(&self, lhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms: Vec<Value<'v>> = Vec::new();
        splice_arm(&mut arms, lhs, heap);
        arms.extend(self.arms.iter().map(|a| a.to_value()));
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
}

/// Re-materialize a live equivalent of `self` (the `add`/`radd` trait gives `&self`, not the `Value` handle);
/// a select is immutable data so a clone is behavior-identical. Its branch values are Copy `Value`s.
fn reclone_select<'v, V: ValueLike<'v>>(s: &SelectValueGen<V>, heap: Heap<'v>) -> Value<'v> {
    heap.alloc(SelectValueGen {
        conditions: s.conditions.iter().map(|(k, v)| (k.clone(), v.to_value())).collect(),
        no_match_error: s.no_match_error.clone(),
    })
}

/// Append `arm` to the SelectorList's arm list, FLATTENING a SelectorList operand (its arms splice in — a
/// SelectorList never nests) so `convert` sees a flat Concrete/Branch sequence.
fn splice_arm<'v>(arms: &mut Vec<Value<'v>>, arm: Value<'v>, heap: Heap<'v>) {
    if let Some(list) = SelectorListValue::from_value(arm) {
        for a in &list.arms {
            arms.push(a.to_value());
        }
    } else {
        let _ = heap; // arm is either a SelectValue (Branch) or a plain value (Concrete) — kept verbatim.
        arms.push(arm);
    }
}

/// Build a [`SelectValue`] from a `select({...})` dict, canonicalizing the conditions to label-sorted order.
/// Fail-closed on a non-string condition key (Bazel condition keys are label strings). The branch values stay
/// LIVE (converted at the boundary).
pub(crate) fn make_select<'v>(dict: DictRef<'v>, no_match_error: String, heap: Heap<'v>) -> anyhow::Result<Value<'v>> {
    let mut conditions: Vec<(String, Value<'v>)> = Vec::with_capacity(dict.len());
    for (k, v) in dict.iter() {
        let key = k
            .unpack_str()
            .ok_or_else(|| anyhow::anyhow!("select() condition keys must be label strings"))?
            .to_owned();
        conditions.push((key, v));
    }
    conditions.sort_by(|a, b| a.0.cmp(&b.0)); // canonical label-sorted (order-independent for matching)
    Ok(heap.alloc(SelectValueGen { conditions, no_match_error }))
}
