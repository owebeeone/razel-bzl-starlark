//! `depset` — the C2 live value filling the reserved codec seat (tag 7, `RazelV4ProviderIdentityLockdown`
//! row C). Constructor `depset(direct=, transitive=, order=)` + `.to_list()` (postorder default, deduplicated,
//! deterministic). A depset is an ordered DAG, NOT a list: `len`/indexing/iteration/`in` are all errors (a
//! consumer flattens with `.to_list()`). Codec: `convert` (convert.rs) projects a live depset to
//! `BzlValue::Depset` and `encode_bzl_value` renders it under the pinned tag-7 frame — exactly the reserved
//! encoding, additively filled.

use allocative::Allocative;
use razel_bzl_api::DepsetOrder;
use starlark::environment::{GlobalsBuilder, Methods, MethodsBuilder, MethodsStatic};
use starlark::values::list::ListRef;
use starlark::values::{
    starlark_value, Coerce, Freeze, FreezeResult, Freezer, FrozenValue, Heap, NoSerialize, ProvidesStaticType,
    StarlarkPagable, StarlarkValue, Trace, Value, ValueLifetimeless, ValueLike,
};
use starlark::{starlark_complex_value, starlark_module};
use std::fmt;

/// A live `depset`: the traversal `order` (a `DepsetOrder::code()`, the ONE pinned table), the `direct`
/// elements, and the `transitive` children (each itself a depset value). COMPLEX (holds live `V`s); manual
/// `Freeze` because the `u8` order does not implement starlark's `Freeze` (same reason `RuleValueGen` is
/// manual). Deliberately implements NO `length`/`at`/`iterate`/`is_in` — so `len(d)`, `d[0]`, `for x in d`,
/// `x in d` all fail closed (a depset is not a sequence).
#[derive(Debug, Trace, Coerce, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct DepsetValueGen<V: ValueLifetimeless> {
    pub(crate) order: u8,
    pub(crate) direct: Vec<V>,
    pub(crate) transitive: Vec<V>,
}
starlark_complex_value!(pub(crate) DepsetValue);
impl<'v> Freeze for DepsetValueGen<Value<'v>> {
    type Frozen = DepsetValueGen<FrozenValue>;
    fn freeze(self, freezer: &Freezer) -> FreezeResult<Self::Frozen> {
        Ok(DepsetValueGen {
            order: self.order,
            direct: self.direct.into_iter().map(|v| v.freeze(freezer)).collect::<FreezeResult<_>>()?,
            transitive: self.transitive.into_iter().map(|v| v.freeze(freezer)).collect::<FreezeResult<_>>()?,
        })
    }
}
impl<V: ValueLifetimeless> fmt::Display for DepsetValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "depset(...)")
    }
}
#[starlark_value(type = "depset")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for DepsetValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    fn get_methods() -> Option<&'static Methods> {
        static RES: MethodsStatic = MethodsStatic::new("depset", depset_methods);
        Some(RES.methods())
    }
}

/// Allocate a live depset from already-live parts (used by the constructor AND the codec `alloc` seat).
pub(crate) fn alloc_depset<'v>(heap: Heap<'v>, order: u8, direct: Vec<Value<'v>>, transitive: Vec<Value<'v>>) -> Value<'v> {
    heap.alloc(DepsetValueGen { order, direct, transitive })
}

/// `.to_list()` — the flattened traversal. Postorder for `default`/`postorder` (transitive children first,
/// then direct); preorder for `preorder` (direct first); `topological`'s link-order is DEFERRED this wave
/// (fail-closed, never a wrong order — nothing constructs one). Dedup keeps the FIRST occurrence.
pub(crate) fn depset_to_list<'v>(root: Value<'v>) -> anyhow::Result<Vec<Value<'v>>> {
    let ds = DepsetValue::from_value(root).ok_or_else(|| anyhow::anyhow!("to_list receiver is not a depset"))?;
    let order = DepsetOrder::from_code(ds.order)
        .ok_or_else(|| anyhow::anyhow!("depset has an invalid order code {}", ds.order))?;
    let direct_first = match order {
        DepsetOrder::Preorder => true,
        DepsetOrder::Default | DepsetOrder::Postorder => false,
        DepsetOrder::Topological => {
            return Err(anyhow::anyhow!("depset topological (link) order to_list is deferred this wave"))
        }
    };
    let mut out: Vec<Value<'v>> = Vec::new();
    collect(root, &mut out, direct_first)?;
    Ok(out)
}

fn push_dedup<'v>(out: &mut Vec<Value<'v>>, v: Value<'v>) -> anyhow::Result<()> {
    for existing in out.iter() {
        if existing.equals(v).map_err(|e| anyhow::anyhow!("{e}"))? {
            return Ok(());
        }
    }
    out.push(v);
    Ok(())
}

fn collect<'v>(node: Value<'v>, out: &mut Vec<Value<'v>>, direct_first: bool) -> anyhow::Result<()> {
    let ds = DepsetValue::from_value(node).ok_or_else(|| anyhow::anyhow!("depset transitive entry is not a depset"))?;
    let emit_direct = |out: &mut Vec<Value<'v>>| -> anyhow::Result<()> {
        for d in ds.direct.iter() {
            push_dedup(out, d.to_value())?;
        }
        Ok(())
    };
    // MUTANT: skip the transitive recursion → to_list yields the direct elements only, so a transitive
    // rlib's `-L`/`--extern` contribution vanishes and the multi-crate chain breaks.
    let recurse = !cfg!(feature = "mutant_depset_tolist_drops_transitive");
    if direct_first {
        emit_direct(out)?;
        if recurse {
            for t in ds.transitive.iter() {
                collect(t.to_value(), out, direct_first)?;
            }
        }
    } else {
        if recurse {
            for t in ds.transitive.iter() {
                collect(t.to_value(), out, direct_first)?;
            }
        }
        emit_direct(out)?;
    }
    Ok(())
}

#[starlark_module]
fn depset_methods(builder: &mut MethodsBuilder) {
    /// `d.to_list()` — flatten the depset to a deduplicated list in the depset's order.
    fn to_list<'v>(#[starlark(this)] this: Value<'v>, heap: Heap<'v>) -> anyhow::Result<Value<'v>> {
        let items = depset_to_list(this)?;
        Ok(heap.alloc(items))
    }
}

#[starlark_module]
pub(crate) fn depset_global(builder: &mut GlobalsBuilder) {
    /// `depset(direct = [], *, order = "default", transitive = [depsets])` — construct a depset. `transitive`
    /// entries MUST be depsets (fail-closed). `order` is one of the four current Starlark order names (the
    /// deprecated aliases are rejected). No merge/type-check algebra beyond this in the wave.
    fn depset<'v>(
        direct: Option<Value<'v>>,
        #[starlark(require = named)] order: Option<String>,
        #[starlark(require = named)] transitive: Option<Value<'v>>,
        heap: Heap<'v>,
    ) -> anyhow::Result<Value<'v>> {
        let order_code = match order.as_deref() {
            None | Some("default") => DepsetOrder::Default,
            Some(name) => DepsetOrder::parse(name)
                .ok_or_else(|| anyhow::anyhow!("depset order '{name}' is not one of default/postorder/topological/preorder"))?,
        }
        .code();
        let direct_vals: Vec<Value<'v>> = match direct {
            None => Vec::new(),
            Some(v) if v.is_none() => Vec::new(),
            Some(v) => ListRef::from_value(v)
                .ok_or_else(|| anyhow::anyhow!("depset direct= must be a list"))?
                .iter()
                .collect(),
        };
        let transitive_vals: Vec<Value<'v>> = match transitive {
            None => Vec::new(),
            Some(v) if v.is_none() => Vec::new(),
            Some(v) => {
                let list = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("depset transitive= must be a list of depsets"))?;
                for item in list.iter() {
                    if DepsetValue::from_value(item).is_none() {
                        return Err(anyhow::anyhow!("depset transitive= entries must be depsets"));
                    }
                }
                list.iter().collect()
            }
        };
        Ok(alloc_depset(heap, order_code, direct_vals, transitive_vals))
    }
}
