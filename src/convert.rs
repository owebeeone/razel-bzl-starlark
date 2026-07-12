use razel_bzl_api::{
    AttrDecl, AttrType, BzlError, BzlModule, BzlValue, Depset, DepsetOrder, FunctionRef, ProviderId,
    ProviderInstance, RuleDef, SelectArm,
};
use starlark::environment::{FrozenModule, Module};
use starlark::values::dict::{AllocDict, DictRef};
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::structs::{AllocStruct, StructRef};
use starlark::values::tuple::{AllocTuple, TupleRef};
use starlark::values::{UnpackValue, Value, ValueLike};
use std::collections::HashMap;

use crate::globals_def::{DeferredMarker, DEFERRED_MARKER_DETAIL_FIELD, DEFERRED_MARKER_KIND_FIELD};
use crate::values::{AttrTypeValue, Provider, ProviderInstanceValueGen, RuleProxy, RuleValue};
use crate::values_depset::{alloc_depset, DepsetValue};
use crate::values_file::{make_file, FileValue};
use crate::values_function::LoadedFunctionValue;
use crate::values_label::{parse_label, LabelValue};
use crate::values::{SelectValue, SelectValueGen, SelectorListValue, SelectorListValueGen};

/// The identity of the module currently being converted — stamped onto a freshly-DEFINED function/struct so
/// its `FunctionRef` names WHERE it is defined + carries the defining module's content digest (T20
/// R-load-codec). `None` in contexts that never hold a function (BUILD/rule attribute values); a function
/// reached there fails closed.
#[derive(Clone, Copy)]
pub(crate) struct ConvertCtx<'a> {
    pub(crate) module: &'a str,
    pub(crate) digest: [u8; 32],
}

/// A generous recursion bound on struct/list nesting during conversion — fail-closed (typed) rather than a
/// stack overflow on a pathological or malicious value. Real `.bzl` structs nest a handful deep.
const MAX_CONVERT_DEPTH: usize = 200;

/// Project a starlark `Value` into the codec-neutral model. `ctx` names the module being converted (so a
/// freshly-defined function/struct is stamped with its defining identity); pass `None` where a function can
/// never legitimately appear (attribute values). Unsupported kinds fail closed.
pub(crate) fn convert(v: Value, ctx: Option<&ConvertCtx>) -> Result<BzlValue, BzlError> {
    convert_rec(v, ctx, 0)
}

fn convert_rec(v: Value, ctx: Option<&ConvertCtx>, depth: usize) -> Result<BzlValue, BzlError> {
    if depth > MAX_CONVERT_DEPTH {
        return Err(BzlError::Eval {
            detail: format!("value nesting exceeds the {MAX_CONVERT_DEPTH}-level conversion bound (recursion guard)"),
        });
    }
    if v.is_none() {
        return Ok(BzlValue::None);
    }
    if let Some(b) = v.unpack_bool() {
        return Ok(BzlValue::Bool(b));
    }
    match i64::unpack_value(v) {
        Ok(Some(i)) => return Ok(BzlValue::Int(i)),
        Ok(None) => {} // not an integer (or a bignum beyond i64) — try other kinds, else fall through
        Err(e) => return Err(BzlError::Eval { detail: e.to_string() }),
    }
    if let Some(s) = v.unpack_str() {
        return Ok(BzlValue::Str(s.to_owned()));
    }
    if let Some(list) = ListRef::from_value(v) {
        let mut out = Vec::with_capacity(list.len());
        for item in list.iter() {
            out.push(convert_rec(item, ctx, depth + 1)?);
        }
        return Ok(BzlValue::List(out));
    }
    // A dict crosses as INSERTION-ordered (key, value) pairs (tag 12); keys/values recurse.
    if let Some(dict) = DictRef::from_value(v) {
        let mut out = Vec::with_capacity(dict.len());
        for (k, val) in dict.iter() {
            out.push((convert_rec(k, ctx, depth + 1)?, convert_rec(val, ctx, depth + 1)?));
        }
        return Ok(BzlValue::Dict(out));
    }
    // A tuple crosses as an ordered element list under its own tag (14) — distinct from a list.
    if let Some(tuple) = TupleRef::from_value(v) {
        let mut out = Vec::with_capacity(tuple.len());
        for item in tuple.iter() {
            out.push(convert_rec(item, ctx, depth + 1)?);
        }
        return Ok(BzlValue::Tuple(out));
    }
    // A rule definition (def-side) or a loaded rule (call-side) projects to BzlValue::Rule. The def-side has
    // no identity yet (the export loop stamps name + bzl); the call-side already carries its origin.
    if let Some(rv) = RuleValue::from_value(v) {
        return Ok(BzlValue::Rule(RuleDef {
            bzl: String::new(),
            name: String::new(),
            attrs: decode_schema(&rv.attrs)?,
            toolchains: rv.toolchains.clone(),
        }));
    }
    if let Some(rp) = v.downcast_ref::<RuleProxy>() {
        return Ok(BzlValue::Rule(RuleDef {
            bzl: rp.bzl.clone(),
            name: rp.kind.clone(),
            attrs: decode_schema(&rp.attrs)?,
            toolchains: rp.toolchains.clone(),
        }));
    }
    if let Some(p) = v.downcast_ref::<Provider>() {
        return Ok(BzlValue::Provider(razel_bzl_api::ProviderDef { id: p.provider_id(), fields: p.fields.clone() }));
    }
    // A File projects to `BzlValue::File` (its exec path) — NOT a bare `Str` (C5). A provider field carrying
    // a File (`RustInfo.rlib`, `DefaultInfo.files` elements) must round-trip as a File across the node
    // boundary so the consuming side's `dep[RustInfo].rlib.path` reads the exec path back; a `Str` would
    // decode to a plain string with no `.path`.
    if let Some(f) = v.downcast_ref::<FileValue>() {
        // MUTANT: project a File to a bare Str (the pre-C5 codec drop) — the consuming side then reconstructs
        // a plain string, so `dep[RustInfo].rlib.path` has no `.path` and the multi-crate chain fails closed.
        if cfg!(feature = "mutant_provider_file_field_stringified") {
            return Ok(BzlValue::Str(f.path.clone()));
        }
        return Ok(BzlValue::File(f.path.clone()));
    }
    // A depset fills the reserved tag-7 seat: project it structurally so `encode_bzl_value` renders it under
    // the pinned frame (additive — nothing else changes).
    if DepsetValue::from_value(v).is_some() {
        return Ok(BzlValue::Depset(convert_to_depset(v, ctx, depth)?));
    }
    // A Label(...) value crosses as its canonical label string (tag 11). The honest fields are re-derived on
    // the live side (`alloc`), so a loaded `CC_TOOLCHAIN_TYPE = Label(…)` round-trips.
    if let Some(l) = v.downcast_ref::<LabelValue>() {
        return Ok(BzlValue::Label(l.display.clone()));
    }
    // A `select({...})` crosses as an UNRESOLVED `BzlValue::Select` (tag 15) — a SINGLE Branch arm. Resolution
    // is analysis, NEVER here (the configuration is unknown at load). The branch VALUES recurse (a select over
    // label lists / string lists / dicts).
    if let Some(sel) = SelectValue::from_value(v) {
        return Ok(BzlValue::Select(vec![convert_select_branch(&sel, ctx, depth)?]));
    }
    // A SelectorList (`[..] + select(..)` / `select(..) + select(..)`) crosses as a MULTI-arm `BzlValue::Select`:
    // each arm is a Concrete value (a plain `+` operand) or a Branch (a nested select), recovered by downcast.
    if let Some(list) = SelectorListValue::from_value(v) {
        let mut arms = Vec::with_capacity(list.arms.len());
        for arm in &list.arms {
            let arm_v = arm.to_value();
            if let Some(br) = SelectValue::from_value(arm_v) {
                arms.push(convert_select_branch(&br, ctx, depth)?);
            } else {
                arms.push(SelectArm::Concrete(convert_rec(arm_v, ctx, depth + 1)?));
            }
        }
        return Ok(BzlValue::Select(arms));
    }
    // An `attr.<type>(...)` schema marker crosses as an AttrDecl (tag 13) — shared attribute dicts (`_common_
    // attrs`) `load()` across modules with their schema intact.
    if let Some(a) = v.downcast_ref::<AttrTypeValue>() {
        return Ok(BzlValue::AttrDecl(AttrDecl {
            code: a.code,
            allow_files: a.allow_files.clone(),
            providers: a.providers.clone(),
            mandatory: a.mandatory,
            default: a.default.clone(),
        }));
    }
    // A LOADED function (a re-export) already carries its codec-neutral identity — recover it VERBATIM (a
    // function re-exported through N modules keeps pointing at its true definer, not the re-exporter). Checked
    // BEFORE the raw-function case (a `LoadedFunctionValue` has starlark type "function").
    if let Some(lf) = v.downcast_ref::<LoadedFunctionValue>() {
        return Ok(BzlValue::FunctionRef(FunctionRef {
            module: lf.module.clone(),
            name: lf.name.clone(),
            defining_digest: lf.digest32().map_err(|e| BzlError::Eval { detail: e.to_string() })?,
        }));
    }
    // A DEFERRED analysis marker (T20 R-load, row 5): `aspect()`/`transition()`/`configuration_field()`. It
    // has no crossable live form, so it rides the tag-9 struct carrier under the reserved sentinel fields
    // (kind + opaque detail); `alloc` re-materializes a fail-closed marker. Checked BEFORE StructRef (a
    // DeferredMarker is a simple value, not a struct, but keep it with the custom-value downcasts).
    if let Some(m) = v.downcast_ref::<DeferredMarker>() {
        // Fields in NAME-SORTED order (detail < kind) — the canonical struct order the codec re-sorts to anyway.
        return Ok(BzlValue::Struct(vec![
            (DEFERRED_MARKER_DETAIL_FIELD.to_owned(), BzlValue::Str(m.detail.clone())),
            (DEFERRED_MARKER_KIND_FIELD.to_owned(), BzlValue::Str(m.kind.clone())),
        ]));
    }
    // A struct(...) — a bag of named fields (T20 R-load-codec, tag 9). Recurse (fields sorted on encode);
    // function-valued fields become FunctionRefs (rust_common's `create_crate_info`).
    if let Some(st) = StructRef::from_value(v) {
        return Ok(BzlValue::Struct(convert_to_struct(st, ctx, depth)?));
    }
    // A freshly-DEFINED Starlark function (T20 R-load-codec, tag 10). Its identity is (module, name) + the
    // defining module's content digest — NEVER the body. Requires a conversion context (the defining module);
    // a function in an attribute value (ctx = None) stays a fail-closed Unsupported.
    if v.get_type() == "function" {
        return match ctx {
            Some(c) => Ok(BzlValue::FunctionRef(FunctionRef {
                module: c.module.to_owned(),
                name: recover_fn_name(v),
                defining_digest: c.digest,
            })),
            None => Err(BzlError::Unsupported {
                what: "function value outside a module-export context (no defining module to reference)".to_owned(),
            }),
        };
    }
    Err(BzlError::Unsupported { what: v.get_type().to_owned() })
}

/// Project one live `select({...})` into a codec-neutral [`SelectArm::Branch`] — its conditions recurse (a
/// select over label lists / string lists / dicts) and are re-sorted canonically (belt over the construction
/// sort). NEVER resolves: the branch values cross verbatim, resolution is analysis.
fn convert_select_branch<'v, V: ValueLike<'v>>(
    sel: &SelectValueGen<V>,
    ctx: Option<&ConvertCtx>,
    depth: usize,
) -> Result<SelectArm, BzlError> {
    let mut conditions: Vec<(String, BzlValue)> = Vec::with_capacity(sel.conditions.len());
    for (label, val) in &sel.conditions {
        conditions.push((label.clone(), convert_rec(val.to_value(), ctx, depth + 1)?));
    }
    conditions.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(SelectArm::Branch { conditions, no_match_error: sel.no_match_error.clone() })
}

/// Recover a Starlark function's own symbol name from its value. A `def`'s `str()` is its `function_name` —
/// which starlark renders as `<module filename>.<symbol>` (`ParametersSpec::collect_signature`, name built at
/// `eval/compiler/def.rs`). The bridge looks a symbol up in the frozen module by its BARE name (identifiers
/// carry no `.`), so take the segment after the last `.`. Defensively strip any `<function …>` wrapper and
/// trailing `(…)` a future starlark rendering might add. Yields e.g. `_create_crate_info` for the private
/// function a struct field points at.
fn recover_fn_name(v: Value) -> String {
    let s = v.to_str();
    let s = s.strip_prefix("<function ").map(|r| r.trim_end_matches('>')).unwrap_or(&s);
    let s = s.split('(').next().unwrap_or(s).trim();
    s.rsplit('.').next().unwrap_or(s).to_owned()
}

/// The type-symbol cache for a depset's `elem` (a DERIVED field, NOT digest content — the §2 frame pins
/// tag/order/direct/transitive only). The first direct element's Starlark type, else the first child's cache.
fn bzl_type_name(v: &BzlValue) -> &'static str {
    match v {
        BzlValue::None => "NoneType",
        BzlValue::Bool(_) => "bool",
        BzlValue::Int(_) => "int",
        BzlValue::Str(_) => "string",
        BzlValue::List(_) => "list",
        BzlValue::Rule(_) => "rule",
        BzlValue::Provider(_) => "provider",
        BzlValue::Depset(_) => "depset",
        BzlValue::File(_) => "File",
        BzlValue::Struct(_) => "struct",
        BzlValue::FunctionRef(_) => "function",
        BzlValue::Label(_) => "Label",
        BzlValue::Dict(_) => "dict",
        BzlValue::AttrDecl(_) => "attr_type",
        BzlValue::Tuple(_) => "tuple",
        BzlValue::Select(_) => "select",
    }
}
fn derive_elem(direct: &[BzlValue], transitive: &[Depset]) -> Option<String> {
    if let Some(first) = direct.first() {
        return Some(bzl_type_name(first).to_owned());
    }
    transitive.first().and_then(|t| t.elem.clone())
}

/// Project a live depset value into the codec-neutral ordered DAG (recursive over the transitive children).
fn convert_to_depset(v: Value, ctx: Option<&ConvertCtx>, depth: usize) -> Result<Depset, BzlError> {
    let ds = DepsetValue::from_value(v).ok_or_else(|| BzlError::Eval { detail: "expected a depset value".into() })?;
    let direct: Vec<BzlValue> =
        ds.direct.iter().map(|e| convert_rec(e.to_value(), ctx, depth + 1)).collect::<Result<_, _>>()?;
    let transitive: Vec<Depset> =
        ds.transitive.iter().map(|t| convert_to_depset(t.to_value(), ctx, depth + 1)).collect::<Result<_, _>>()?;
    let order = DepsetOrder::from_code(ds.order)
        .ok_or_else(|| BzlError::Eval { detail: format!("invalid depset order code {}", ds.order) })?;
    let elem = derive_elem(&direct, &transitive);
    Ok(Depset { order, elem, direct, transitive })
}

/// Project a live `struct(...)` into the codec-neutral field list (T20 R-load-codec, tag 9). Fields are
/// SORTED by name (canonical → the digest is `struct()` kwargs-order-independent); each value recurses
/// (nested structs, function-valued fields → FunctionRefs). `ctx` (the defining module) is threaded so a
/// function field is stamped with the module the struct is BUILT in.
fn convert_to_struct(st: StructRef, ctx: Option<&ConvertCtx>, depth: usize) -> Result<Vec<(String, BzlValue)>, BzlError> {
    let mut fields: Vec<(String, BzlValue)> = Vec::new();
    for (name, value) in st.iter() {
        fields.push((name.as_str().to_owned(), convert_rec(value, ctx, depth + 1)?));
    }
    fields.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(fields)
}

/// Recognize the reserved deferred-marker sentinel struct (row 5) and rebuild the live `DeferredMarker`. A
/// struct is a marker IFF it has EXACTLY the two sentinel string fields (kind + detail) and nothing else — so
/// a real user struct (which never carries `_razel_`-prefixed fields) is never mistaken for one.
fn deferred_marker_from_fields(fields: &[(String, BzlValue)]) -> Option<DeferredMarker> {
    if fields.len() != 2 {
        return None;
    }
    let get = |name: &str| -> Option<String> {
        fields.iter().find(|(n, _)| n == name).and_then(|(_, v)| match v {
            BzlValue::Str(s) => Some(s.clone()),
            _ => None,
        })
    };
    Some(DeferredMarker { kind: get(DEFERRED_MARKER_KIND_FIELD)?, detail: get(DEFERRED_MARKER_DETAIL_FIELD)? })
}

/// Decode a `(name, code)` schema into `(name, AttrType)`, fail-closed on an invalid code.
pub(crate) fn decode_schema(coded: &[(String, u8)]) -> Result<Vec<(String, AttrType)>, BzlError> {
    coded
        .iter()
        .map(|(n, c)| {
            AttrType::from_code(*c)
                .map(|t| (n.clone(), t))
                .ok_or_else(|| BzlError::Eval { detail: format!("invalid attr type code {c}") })
        })
        .collect()
}

/// Allocate a codec-neutral value into a module's heap (inverse of `convert`). Fail-closed (never a silent
/// default): a value kind with no live representation in v1 is a typed error.
pub(crate) fn alloc<'v>(module: &Module<'v>, v: &BzlValue) -> Result<Value<'v>, BzlError> {
    let heap = module.heap();
    Ok(match v {
        BzlValue::None => heap.alloc(NoneType),
        BzlValue::Bool(b) => Value::new_bool(*b),
        BzlValue::Int(i) => heap.alloc(*i),
        BzlValue::Str(s) => heap.alloc(s.as_str()),
        BzlValue::List(items) => {
            let vals: Vec<Value> = items.iter().map(|it| alloc(module, it)).collect::<Result<_, _>>()?;
            heap.alloc(vals)
        }
        // A rule re-materializes as a callable RuleProxy (calling it in a BUILD records a target).
        BzlValue::Rule(rd) => heap.alloc(RuleProxy {
            kind: rd.name.clone(),
            bzl: rd.bzl.clone(),
            attrs: rd.attrs.iter().map(|(n, t)| (n.clone(), t.code())).collect(),
            toolchains: rd.toolchains.clone(),
        }),
        // A provider re-materializes as a callable Provider (constructs instances; keys dep[Provider] lookups).
        // The live value carries the exported NAME; a filled bzl dim (a cross-module identity) has no live
        // representation under the v1 single-module cap — fail closed rather than silently drop the dim.
        BzlValue::Provider(pd) => {
            if pd.id.bzl().is_some() {
                return Err(BzlError::Unsupported {
                    what: format!(
                        "provider '{}' with a cross-module identity (bzl dim) under the v1 single-module cap",
                        pd.id.name()
                    ),
                });
            }
            heap.alloc(Provider { id: pd.id.name().to_owned(), fields: pd.fields.clone(), schemaless: false })
        }
        // Depsets are LIVE now (C2): re-materialize the ordered DAG so a codec round-trip (and a
        // depset-carrying provider/loaded binding) reconstructs the same value under the reserved tag.
        BzlValue::Depset(d) => {
            let direct: Vec<Value> = d.direct.iter().map(|e| alloc(module, e)).collect::<Result<_, _>>()?;
            let transitive: Vec<Value> = d
                .transitive
                .iter()
                .map(|t| alloc(module, &BzlValue::Depset(t.clone())))
                .collect::<Result<_, _>>()?;
            alloc_depset(heap, d.order.code(), direct, transitive)
        }
        // A File re-materializes as a live `FileValue` (C5) — so a dep's `RustInfo.rlib` / `DefaultInfo.files`
        // entry, fed back into the consuming rule impl via `alloc_provider_instance`, is a File with `.path`/
        // `.dirname` intact (the round-trip the codec test asserts).
        BzlValue::File(p) => heap.alloc(make_file(p.clone())),
        // A struct re-materializes as a native starlark struct (T20 R-load-codec); fields recurse (function
        // fields become LoadedFunctions). Fields are already name-sorted from convert; kept as-is. EXCEPTION
        // (row 5): a struct carrying the reserved deferred-marker sentinel fields re-materializes as a
        // fail-closed live `DeferredMarker` (an `aspect()`/`transition()`/`configuration_field()` crossing the
        // load boundary), NOT an inert struct — a driven marker fails closed.
        BzlValue::Struct(fields) => {
            if let Some(m) = deferred_marker_from_fields(fields) {
                heap.alloc(m)
            } else {
                let entries: Vec<(String, Value)> =
                    fields.iter().map(|(n, v)| Ok((n.clone(), alloc(module, v)?))).collect::<Result<_, BzlError>>()?;
                heap.alloc(AllocStruct(entries))
            }
        }
        // A FunctionRef re-materializes as a `LoadedFunction` (T20 R-load-codec): a callable carrying the
        // reference identity; invoking it resolves the real callable through the live-module bridge. The body
        // is NEVER reconstructed here — only the reference.
        BzlValue::FunctionRef(f) => heap.alloc(LoadedFunctionValue {
            module: f.module.clone(),
            name: f.name.clone(),
            digest: f.defining_digest.to_vec(),
        }),
        // A Label re-materializes as a live `LabelValue` — its honest fields re-derived from the canonical
        // string (the inverse of `convert`'s `l.display`).
        BzlValue::Label(s) => {
            let p = parse_label(s);
            heap.alloc(LabelValue {
                package: p.package,
                name: p.name,
                workspace_name: p.workspace_name,
                repo_name: p.repo_name,
                display: p.display,
            })
        }
        // A dict re-materializes as a native starlark dict, insertion order preserved.
        BzlValue::Dict(pairs) => {
            let entries: Vec<(Value, Value)> = pairs
                .iter()
                .map(|(k, val)| Ok((alloc(module, k)?, alloc(module, val)?)))
                .collect::<Result<_, BzlError>>()?;
            heap.alloc(AllocDict(entries))
        }
        // An AttrDecl re-materializes as the live `attr.*` marker (the inverse of the `AttrTypeValue` convert).
        BzlValue::AttrDecl(a) => heap.alloc(AttrTypeValue {
            code: a.code,
            allow_files: a.allow_files.clone(),
            providers: a.providers.clone(),
            mandatory: a.mandatory,
            default: a.default.clone(),
        }),
        // A tuple re-materializes as a native starlark tuple.
        BzlValue::Tuple(items) => {
            let vals: Vec<Value> = items.iter().map(|it| alloc(module, it)).collect::<Result<_, _>>()?;
            heap.alloc(AllocTuple(vals))
        }
        // A Select re-materializes as the live selector (round-trip): a single Branch → a bare `SelectValue`;
        // otherwise a `SelectorList` of a `SelectValue` per Branch + the plain value per Concrete. NEVER
        // resolved here (resolution is analysis); this path exists so a select crossing a BZL_LOAD boundary
        // (a `.bzl` constant / a provider field) round-trips.
        BzlValue::Select(arms) => {
            if let [SelectArm::Branch { conditions, no_match_error }] = arms.as_slice() {
                alloc_select_value(module, conditions, no_match_error)?
            } else {
                let arm_vals: Vec<Value> = arms
                    .iter()
                    .map(|a| match a {
                        SelectArm::Concrete(v) => alloc(module, v),
                        SelectArm::Branch { conditions, no_match_error } => {
                            alloc_select_value(module, conditions, no_match_error)
                        }
                    })
                    .collect::<Result<_, _>>()?;
                heap.alloc(SelectorListValueGen { arms: arm_vals })
            }
        }
    })
}

/// Allocate a live `SelectValue` (one Branch) from codec-neutral conditions — the alloc-side inverse of
/// [`convert_select_branch`]. The branch values recurse through [`alloc`].
fn alloc_select_value<'v>(
    module: &Module<'v>,
    conditions: &[(String, BzlValue)],
    no_match_error: &str,
) -> Result<Value<'v>, BzlError> {
    let conds: Vec<(String, Value<'v>)> =
        conditions.iter().map(|(k, v)| Ok((k.clone(), alloc(module, v)?))).collect::<Result<_, BzlError>>()?;
    Ok(module.heap().alloc(SelectValueGen { conditions: conds, no_match_error: no_match_error.to_owned() }))
}

/// Allocate a codec-neutral `ProviderInstance` (a dep's already-computed provider) as a live value, so a rule
/// impl can read it via `dep[Provider].field`. The live value carries the exported NAME — its identity gate is
/// the CALLER's: the dep path re-keys through `providers_by_id` (ProviderId's derived impls, so a bzl-differing
/// instance never gets here), and the toolchain path checks the dim before allocating.
pub(crate) fn alloc_provider_instance<'v>(module: &Module<'v>, pi: &ProviderInstance) -> Result<Value<'v>, BzlError> {
    let fields: Vec<(String, Value<'v>)> = pi
        .fields
        .iter()
        .map(|(n, bv)| Ok((n.clone(), alloc(module, bv)?)))
        .collect::<Result<_, BzlError>>()?;
    Ok(module.heap().alloc(ProviderInstanceValueGen { provider_id: pi.provider.name().to_owned(), fields }))
}

/// Rebuild a loaded module's bindings into a `FrozenModule` so the `ReturnFileLoader` can serve it.
pub(crate) fn build_frozen(m: &BzlModule) -> Result<FrozenModule, BzlError> {
    Module::with_temp_heap(|module| -> Result<FrozenModule, BzlError> {
        for (name, v) in &m.bindings {
            let val = alloc(&module, v)?;
            module.set(name, val);
        }
        module.freeze().map_err(|e| BzlError::Eval { detail: format!("{e:?}") })
    })
}

/// Scan a module's bindings for live `Provider` declarations, building the identity index that keys the
/// per-dep `{Provider: instance}` dicts. FAIL-CLOSED (lockdown decision H): two DISTINCT declarations
/// sharing one identity are a typed `Eval` error naming the provider — the silent last-wins insert is dead.
/// Aliasing — two names bound to the SAME declaration value — stays legal (one identity, not a collision).
pub(crate) fn index_providers<'v>(module: &Module<'v>, module_name: &str) -> Result<HashMap<ProviderId, Value<'v>>, BzlError> {
    // The RETURNED map keys by each provider's ACTUAL id (a name-less provider's is `""`), so a dep
    // INSTANCE (whose `provider_id` is that same actual id) re-keys against it in `evaluate_rule`. Full
    // export-on-assignment INSTANCE identity (so a name-less provider's instances carry the binding name) is
    // the deferred R5 upgrade — until then the re-keying stays name-based, unchanged from before.
    let mut by_id: HashMap<ProviderId, Value<'v>> = HashMap::new();
    // The dup-check (decision H) uses a COLLISION identity: a NAME-LESS provider (`CrateInfo = provider(doc=…,
    // fields=…)` — the Appendix-A / rules_rust form) takes its identity from the variable it is bound to
    // (export-on-assignment, Bazel), so the seven name-less providers in rules_rust's `providers.bzl` are
    // DISTINCT, not a false collision on the empty name. A named provider keeps its declared name.
    let mut seen: HashMap<ProviderId, Value<'v>> = HashMap::new();
    for n in module.names() {
        if let Some(v) = module.get(n.as_str()) {
            if let Some(p) = Provider::from_value(v) {
                let real_id = p.provider_id();
                let collision_id = if real_id.name().is_empty() {
                    ProviderId::from_name(n.as_str())
                } else {
                    real_id.clone()
                };
                match seen.get(&collision_id) {
                    Some(prev) if prev.ptr_eq(v) => {} // an alias of one declaration — legal
                    Some(_) if cfg!(feature = "mutant_provider_dup_decl_absorbed") => {
                        // MUTANT: restore the pre-lockdown silent last-wins overwrite.
                        seen.insert(collision_id, v);
                    }
                    Some(_) => {
                        return Err(BzlError::Eval {
                            detail: format!(
                                "provider '{}' is declared more than once in {module_name}",
                                collision_id.name()
                            ),
                        })
                    }
                    None => {
                        seen.insert(collision_id, v);
                    }
                }
                by_id.insert(real_id, v);
            }
        }
    }
    Ok(by_id)
}

