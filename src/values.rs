use allocative::Allocative;
use razel_bzl_api::{AttrType, BzlValue, ProviderId, RuleOrigin, TargetDecl};
use starlark::collections::StarlarkHasher;
use starlark::eval::{Arguments, Evaluator};
use starlark::starlark_complex_value;
use starlark::starlark_simple_value;
use starlark::values::{
    starlark_value, Coerce, Freeze, FreezeResult, Freezer, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable,
    StarlarkValue, Trace, Value, ValueLifetimeless, ValueLike,
};
use std::fmt;

use crate::convert::convert;
use crate::eval::starlark_err;
use crate::globals::TargetRegistry;

// ──────────────── custom Starlark values (all SIMPLE / plain data) ────────────────

// Attr types are carried inside custom Starlark values as a `u8` code, not as the api `AttrType` enum: a
// custom value's fields must satisfy the `StarlarkPagable` (de)serialize bounds (the `pagable` feature), and a
// `u8` does while a foreign enum does not. The code IS `AttrType::code()` (the single source of truth in the
// api); decoding is fail-closed via `AttrType::from_code`.

/// Does an attribute VALUE match its declared type (shape-level)? A scalar attr must get a scalar of the right
/// kind; a list attr must get a list (of strings, for label/string lists). Fail-closed: a mismatch is rejected
/// so analysis never sees a wrong-typed attr (e.g. a non-list where it expects label deps). Full label parsing
/// is deferred — this is the shape gate.
fn attr_value_matches(v: &BzlValue, ty: AttrType) -> bool {
    let all_str = |items: &[BzlValue]| items.iter().all(|i| matches!(i, BzlValue::Str(_)));
    match ty {
        AttrType::Int => matches!(v, BzlValue::Int(_)),
        AttrType::Bool => matches!(v, BzlValue::Bool(_)),
        // a label is written as a string; a plain string attr is a string.
        AttrType::String | AttrType::Label => matches!(v, BzlValue::Str(_)),
        AttrType::LabelList | AttrType::StringList => matches!(v, BzlValue::List(items) if all_str(items)),
    }
}

/// `attr.<type>()` marker — a declared attribute type (as a `u8` code), before binding into a rule's schema.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct AttrTypeValue {
    pub(crate) code: u8,
}
starlark_simple_value!(AttrTypeValue);
impl fmt::Display for AttrTypeValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "attr[{}]", self.code)
    }
}
#[starlark_value(type = "attr_type")]
impl<'v> StarlarkValue<'v> for AttrTypeValue {}

/// A rule definition produced by `rule()`: its implementation function + the attr schema (name-sorted). A
/// COMPLEX value because it holds the live impl (`V`); analysis (`evaluate_rule`) reads `.implementation` and
/// invokes it. Projected to `BzlValue::Rule` on export (impl dropped — a heap value is not codec-neutral; the
/// export loop stamps the identity name + defining `.bzl`).
#[derive(Debug, Trace, Coerce, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct RuleValueGen<V: ValueLifetimeless> {
    pub(crate) implementation: V,
    pub(crate) attrs: Vec<(String, u8)>,
    pub(crate) toolchains: Vec<String>,
}
starlark_complex_value!(pub(crate) RuleValue);
// Manual Freeze (not derived): the `u8` attr-code does not implement starlark's `Freeze`; only the impl
// function needs freezing, the schema + required toolchain types are moved as-is.
impl<'v> Freeze for RuleValueGen<Value<'v>> {
    type Frozen = RuleValueGen<starlark::values::FrozenValue>;
    fn freeze(self, freezer: &Freezer) -> FreezeResult<Self::Frozen> {
        Ok(RuleValueGen {
            implementation: self.implementation.freeze(freezer)?,
            attrs: self.attrs,
            toolchains: self.toolchains,
        })
    }
}
impl<V: ValueLifetimeless> fmt::Display for RuleValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<rule>")
    }
}
#[starlark_value(type = "rule_definition")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for RuleValueGen<V> where Self: ProvidesStaticType<'v> {}

/// A provider TYPE produced by `provider(name, fields=[…])`. SIMPLE value: identity is the declared `id`
/// (a name). Callable — `MyInfo(field = …)` constructs a `ProviderInstanceValue`. Hashable + comparable by id
/// so it can key the per-dep `{Provider: instance}` dict that backs `dep[Provider]`.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct Provider {
    pub(crate) id: String,
    pub(crate) fields: Vec<String>,
}
starlark_simple_value!(Provider);
impl Provider {
    /// This declaration's identity on the ONE funnel: the declared name with `bzl = None` (the v1 sentinel —
    /// the declared name IS the exported name under the single-module cap, lockdown R5). ALL live-value
    /// hashing/equality/keying goes through this + `ProviderId`'s derived impls, never the raw string.
    pub(crate) fn provider_id(&self) -> ProviderId {
        ProviderId::from_name(self.id.clone())
    }
}
impl fmt::Display for Provider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<provider {}>", self.id)
    }
}
#[starlark_value(type = "provider")]
impl<'v> StarlarkValue<'v> for Provider {
    /// `MyInfo(field = …)` — construct a provider instance. Fail-closed on positional args / unknown fields.
    fn invoke(
        &self,
        _me: Value<'v>,
        args: &Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> starlark::Result<Value<'v>> {
        args.no_positional_args(eval.heap())?;
        let named = args.names_map()?;
        let mut fields: Vec<(String, Value<'v>)> = Vec::new();
        for (k, v) in named.iter() {
            let key = k.as_str();
            if !self.fields.iter().any(|f| f == key) && !cfg!(feature = "mutant_provider_skips_field_validation") {
                return Err(starlark_err(format!("provider '{}' has no field '{}'", self.id, key)));
            }
            fields.push((key.to_owned(), *v));
        }
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(eval.heap().alloc(ProviderInstanceValueGen { provider_id: self.id.clone(), fields }))
    }
    fn write_hash(&self, hasher: &mut StarlarkHasher) -> starlark::Result<()> {
        // Identity hash via ProviderId's derived Hash (the C2 funnel) — never the raw name bytes.
        use std::hash::Hash as _;
        self.provider_id().hash(hasher);
        Ok(())
    }
    fn equals(&self, other: Value<'v>) -> starlark::Result<bool> {
        // Identity equality via ProviderId's derived Eq (the C2 funnel) — never a raw name comparison.
        Ok(Provider::from_value(other).is_some_and(|o| o.provider_id() == self.provider_id()))
    }
}

/// A provider INSTANCE (`MyInfo(field = …)`), live in the heap. COMPLEX value: holds the field values (`V`).
/// `inst.field` reads a field; the value is projected to codec-neutral `ProviderInstance` at the boundary.
#[derive(Debug, Trace, Coerce, Freeze, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct ProviderInstanceValueGen<V: ValueLifetimeless> {
    pub(crate) provider_id: String,
    pub(crate) fields: Vec<(String, V)>,
}
starlark_complex_value!(pub(crate) ProviderInstanceValue);
impl<V: ValueLifetimeless> fmt::Display for ProviderInstanceValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{} instance>", self.provider_id)
    }
}
#[starlark_value(type = "provider_instance")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for ProviderInstanceValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    fn get_attr(&self, attribute: &str, _heap: Heap<'v>) -> Option<Value<'v>> {
        self.fields.iter().find(|(n, _)| n == attribute).map(|(_, v)| v.to_value())
    }
    fn dir_attr(&self) -> Vec<String> {
        self.fields.iter().map(|(n, _)| n.clone()).collect()
    }
}

/// A loaded rule, callable in a BUILD file. Calling it instantiates a target carrying the rule's origin
/// (the analysis link). Holds only plain data — `kind` (the rule symbol), `bzl` (defining file), attr schema.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct RuleProxy {
    pub(crate) kind: String,
    pub(crate) bzl: String,
    pub(crate) attrs: Vec<(String, u8)>,
    pub(crate) toolchains: Vec<String>,
}
starlark_simple_value!(RuleProxy);
impl fmt::Display for RuleProxy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<rule {}>", self.kind)
    }
}
#[starlark_value(type = "rule")]
impl<'v> StarlarkValue<'v> for RuleProxy {
    /// `my_rule(name = …, **attrs)` — instantiate a target. Records its rule origin (the analysis link),
    /// validates attrs against the rule's schema, and is fail-closed on dup names / unknown attrs / positionals.
    fn invoke(
        &self,
        _me: Value<'v>,
        args: &Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> starlark::Result<Value<'v>> {
        // Fail-closed, NOT a panic: a rule is callable only where a TargetRegistry is installed (BUILD eval).
        // Called from a .bzl (no registry), this is a typed error, not a process crash.
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<TargetRegistry>())
            .ok_or_else(|| {
                starlark_err(format!("rule '{}' can only be called from a BUILD file, not a .bzl module", self.kind))
            })?;

        args.no_positional_args(eval.heap())?; // rules are called all-named (Bazel) — reject positionals
        let named = args.names_map()?;
        let mut name: Option<String> = None;
        let mut attr_pairs: Vec<(String, BzlValue)> = Vec::new();
        for (k, v) in named.iter() {
            let key = k.as_str();
            if key == "name" {
                let s = v.unpack_str().ok_or_else(|| starlark_err("target 'name' must be a string".into()))?;
                name = Some(s.to_owned());
                continue;
            }
            // attr-schema validation: an attribute not in the rule's schema fails closed.
            let declared = self.attrs.iter().find(|(n, _)| n == key);
            if declared.is_none() && !cfg!(feature = "mutant_rule_skips_attr_validation") {
                return Err(starlark_err(format!("rule '{}' has no attribute '{}'", self.kind, key)));
            }
            let val = convert(*v).map_err(|e| starlark_err(format!("attribute '{key}': {e:?}")))?;
            // attr value-type validation: the value's shape must match the declared type (fail-closed), so
            // analysis never sees a wrong-typed attr (e.g. a non-list where it expects label deps).
            if let Some((_, code)) = declared {
                if let Some(ty) = AttrType::from_code(*code) {
                    if !attr_value_matches(&val, ty) && !cfg!(feature = "mutant_rule_skips_type_validation") {
                        return Err(starlark_err(format!(
                            "attribute '{key}' of rule '{}' expects {ty:?}",
                            self.kind
                        )));
                    }
                }
            }
            attr_pairs.push((key.to_owned(), val));
        }
        let name = name.ok_or_else(|| starlark_err("a rule call requires a 'name'".into()))?;
        attr_pairs.sort_by(|a, b| a.0.cmp(&b.0)); // canonical: name-sorted attrs

        if reg.targets.borrow().iter().any(|t| t.name == name) {
            return Err(starlark_err(format!("duplicate target name '{name}' in package")));
        }
        // The ORIGIN is the analysis link — without it, analysis cannot find the rule's impl.
        let origin = if cfg!(feature = "mutant_rule_drops_origin") {
            None
        } else {
            Some(RuleOrigin { bzl: self.bzl.clone(), name: self.kind.clone() })
        };
        reg.targets.borrow_mut().push(TargetDecl { kind: self.kind.clone(), name, attrs: attr_pairs, origin });
        Ok(Value::new_none())
    }
}

