use razel_bzl_api::{AttrType, BzlError, BzlModule, BzlValue, ProviderId, ProviderInstance, RuleDef};
use starlark::environment::{FrozenModule, Module};
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{UnpackValue, Value, ValueLike};
use std::collections::HashMap;

use crate::values::{Provider, ProviderInstanceValueGen, RuleProxy, RuleValue};

/// Project a starlark `Value` into the codec-neutral model. Unsupported kinds fail closed.
pub(crate) fn convert(v: Value) -> Result<BzlValue, BzlError> {
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
            out.push(convert(item)?);
        }
        return Ok(BzlValue::List(out));
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
    Err(BzlError::Unsupported { what: v.get_type().to_owned() })
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
            heap.alloc(Provider { id: pd.id.name().to_owned(), fields: pd.fields.clone() })
        }
        // Depsets are value-model-only in v1 (the digest tag is pinned; the live machinery is not built) —
        // materializing one is a typed error, never a silent placeholder (P3).
        BzlValue::Depset(_) => {
            return Err(BzlError::Unsupported { what: "depset (no live depset values in v1)".to_owned() })
        }
    })
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
    let mut by_id: HashMap<ProviderId, Value<'v>> = HashMap::new();
    for n in module.names() {
        if let Some(v) = module.get(n.as_str()) {
            if let Some(p) = Provider::from_value(v) {
                let id = p.provider_id();
                match by_id.get(&id) {
                    Some(prev) if prev.ptr_eq(v) => {} // an alias of one declaration — legal
                    Some(_) if cfg!(feature = "mutant_provider_dup_decl_absorbed") => {
                        // MUTANT: restore the pre-lockdown silent last-wins overwrite.
                        by_id.insert(id, v);
                    }
                    Some(_) => {
                        return Err(BzlError::Eval {
                            detail: format!("provider '{}' is declared more than once in {module_name}", id.name()),
                        })
                    }
                    None => {
                        by_id.insert(id, v);
                    }
                }
            }
        }
    }
    Ok(by_id)
}

