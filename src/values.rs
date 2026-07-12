use allocative::Allocative;
use razel_bzl_api::{AttrType, BzlValue, ProviderId, RuleOrigin, TargetDecl};
use starlark::collections::StarlarkHasher;
use starlark::eval::{Arguments, Evaluator};
use starlark::starlark_complex_value;
use starlark::starlark_simple_value;
use starlark::values::dict::DictRef;
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
    // A `select(...)` is a CONFIGURABLE value: its shape can't be checked at load (it is unresolved). Bazel
    // accepts a select for any configurable attr; the resolved value's shape is validated post-resolution at
    // analysis. So a Select passes the load-time shape gate for ANY declared type.
    if matches!(v, BzlValue::Select(_)) {
        return true;
    }
    let all_str = |items: &[BzlValue]| items.iter().all(|i| matches!(i, BzlValue::Str(_)));
    match ty {
        AttrType::Int => matches!(v, BzlValue::Int(_)),
        AttrType::Bool => matches!(v, BzlValue::Bool(_)),
        // a label is written as a string; a plain string attr is a string.
        AttrType::String | AttrType::Label => matches!(v, BzlValue::Str(_)),
        // FileList (allow_files) is written like a label/string list — a list of source-path strings.
        AttrType::LabelList | AttrType::StringList | AttrType::FileList => {
            matches!(v, BzlValue::List(items) if all_str(items))
        }
        // Dict attrs (T20 R-load, row 5): a `{...}` value. Shape-level only (a dict) — the key/value-type
        // refinement (string vs label keys, string vs string-list values) is deferred with the attr itself.
        AttrType::StringDict | AttrType::StringListDict | AttrType::LabelKeyedStringDict => {
            matches!(v, BzlValue::Dict(_))
        }
    }
}

/// `attr.<type>()` marker — a declared attribute type (as a `u8` code), before binding into a rule's schema.
/// `allow_files` (C3) carries a `label_list(allow_files=…)`'s accepted extensions: `None` = not a files attr,
/// `Some([])` = allow any file (`allow_files=True`), `Some([".rs"])` = only those extensions. `providers` (C5)
/// carries a `label_list(providers=[P,…])`'s REQUIRED provider names — ENFORCED at analysis (a dep missing a
/// required provider is a typed error). `mandatory` (C5) marks a required attribute (a target omitting it is a
/// typed error). All ride the LIVE marker only — the codec-neutral `RuleDef.attrs` (frozen digest content)
/// stays `(name, AttrType)`.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct AttrTypeValue {
    pub(crate) code: u8,
    pub(crate) allow_files: Option<Vec<String>>,
    pub(crate) providers: Vec<String>,
    pub(crate) mandatory: bool,
    /// `default =` for a scalar STRING attr (P1b, `edition = attr.string(default = "2021")`) — a LIVE-only
    /// channel `evaluate_rule` applies: a target omitting the attr sees this value in `ctx.attr.<name>`
    /// (matching Bazel). `None` = no explicit default (unset → the type's Bazel-implicit zero: `""` for a
    /// string, `[]` for a string_list). Only stored for `attr.string` in this slice (String is pagable; a
    /// general BzlValue default is not — deferred). Not codec-neutral (the exported `RuleDef.attrs` stays
    /// `(name, AttrType)`, so the frozen digest is untouched).
    pub(crate) default: Option<String>,
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
    /// The `allow_files` extensions per files attr (`(name, exts)`; C3) — a LIVE-only channel so
    /// `evaluate_rule` can build `ctx.files.<attr>` and validate source extensions. NOT codec-neutral (the
    /// exported `RuleDef` carries only `AttrType::FileList`, which is what analysis needs to skip these as
    /// dep edges).
    pub(crate) attr_files: Vec<(String, Vec<String>)>,
    /// The REQUIRED provider names per label attr (`(name, [provider…])`; C5, `providers=[P,…]`) — a LIVE-only
    /// channel `evaluate_rule` enforces: a dep missing a required provider is a typed analysis error.
    pub(crate) attr_providers: Vec<(String, Vec<String>)>,
    /// The names of MANDATORY attrs (C5, `mandatory=True`) — a LIVE-only channel `evaluate_rule` enforces: a
    /// target omitting a mandatory attr is a typed analysis error.
    pub(crate) attr_mandatory: Vec<String>,
    /// The explicit STRING defaults per attr (`(name, default)`; P1b, `attr.string(default=…)`) — a LIVE-only
    /// channel `evaluate_rule` applies when a target omits the attr (Bazel's default semantics). Only string
    /// attrs carry an explicit default here; list/scalar attrs fall back to the type's implicit zero.
    pub(crate) attr_string_defaults: Vec<(String, String)>,
}
starlark_complex_value!(pub(crate) RuleValue);
// Manual Freeze (not derived): the `u8` attr-code does not implement starlark's `Freeze`; only the impl
// function needs freezing, the schema + required toolchain types + file-attr map are moved as-is.
impl<'v> Freeze for RuleValueGen<Value<'v>> {
    type Frozen = RuleValueGen<starlark::values::FrozenValue>;
    fn freeze(self, freezer: &Freezer) -> FreezeResult<Self::Frozen> {
        Ok(RuleValueGen {
            implementation: self.implementation.freeze(freezer)?,
            attrs: self.attrs,
            toolchains: self.toolchains,
            attr_files: self.attr_files,
            attr_providers: self.attr_providers,
            attr_mandatory: self.attr_mandatory,
            attr_string_defaults: self.attr_string_defaults,
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
    /// SCHEMALESS (C6): accept ANY field, skipping the declared-field check. `platform_common.ToolchainInfo`
    /// is schemaless in Bazel (`ToolchainInfo(**kwargs)`), so `platform_common.ToolchainInfo(rustc=…)` and any
    /// other toolchain's fields construct without a schema. Plain `provider()` types stay schema-checked.
    pub(crate) schemaless: bool,
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
            if !self.schemaless
                && !self.fields.iter().any(|f| f == key)
                && !cfg!(feature = "mutant_provider_skips_field_validation")
            {
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

/// `platform_common` (C6) — the Bazel `platform_common` namespace global, exposing `ToolchainInfo`. A SIMPLE
/// value; `platform_common.ToolchainInfo` resolves to the schemaless `ToolchainInfo` provider (callable), so a
/// toolchain rule's impl can `return [platform_common.ToolchainInfo(rustc = …)]`. Nothing else is exposed.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct PlatformCommon;
starlark_simple_value!(PlatformCommon);
impl fmt::Display for PlatformCommon {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<platform_common>")
    }
}
#[starlark_value(type = "platform_common")]
impl<'v> StarlarkValue<'v> for PlatformCommon {
    fn get_attr(&self, attribute: &str, heap: Heap<'v>) -> Option<Value<'v>> {
        match attribute {
            "ToolchainInfo" => Some(heap.alloc(crate::globals::toolchain_info_provider())),
            // T20 R-load: `platform_common.TemplateVariableInfo(variables={…})` — schemaless; make-variable
            // expansion is deferred. Additive; the namespace still fails closed on anything else.
            "TemplateVariableInfo" => Some(heap.alloc(crate::globals::template_variable_info_provider())),
            _ => None, // fail closed — platform_common exposes ONLY ToolchainInfo/TemplateVariableInfo in v1
        }
    }
    fn dir_attr(&self) -> Vec<String> {
        vec!["TemplateVariableInfo".to_owned(), "ToolchainInfo".to_owned()]
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
            // COMMON IMPLICIT ATTRS (C7): `visibility` (a list of label-strings, ENFORCED at analysis) and
            // `tags` (a list, stored/ignored) are accepted on EVERY rule — they are not in the rule's own
            // schema but are known-common, so they are NOT the "unknown attr" the validation rejects.
            let is_common = matches!(key, "visibility" | "tags");
            // attr-schema validation: an attribute not in the rule's schema (and not common) fails closed.
            let declared = self.attrs.iter().find(|(n, _)| n == key);
            if declared.is_none() && !is_common && !cfg!(feature = "mutant_rule_skips_attr_validation") {
                return Err(starlark_err(format!("rule '{}' has no attribute '{}'", self.kind, key)));
            }
            let val = convert(*v, None).map_err(|e| starlark_err(format!("attribute '{key}': {e:?}")))?;
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

// ──────────────── select() — the configurable-attribute selector (T20 select) ────────────────
//
// A `select({condition: value, …})` is NEVER resolved during BUILD/.bzl evaluation: it is carried as an
// unresolved [`SelectValue`], crosses the PACKAGE boundary as [`razel_bzl_api::BzlValue::Select`], and is
// resolved at ANALYSIS against the target's configuration (the locus that owns constraint matching). The `+`
// operator on selects/lists builds a [`SelectorListValue`] (Bazel's SelectorList): `["//a"] + select({…})`
// and `select({…}) + select({…})` concatenate — each arm resolved independently, then joined. The branch
// VALUES stay LIVE (converted to codec-neutral form only at `crate::convert`). Kept in `values.rs` (not a new
// module file) because `razel-bzl-starlark`'s member BUILD lists its sources explicitly.

/// A single `select({condition: value, …}, no_match_error = "…")`. `conditions` are (condition-label, live
/// value) pairs, SORTED by label at construction (order-independent for matching → the canonical form matches
/// the tag-15 codec frame). A COMPLEX value (holds live `V` branch values).
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
// Manual Freeze: freeze each live branch value; the label strings + no_match_error move as-is.
impl<'v> Freeze for SelectValueGen<Value<'v>> {
    type Frozen = SelectValueGen<starlark::values::FrozenValue>;
    fn freeze(self, freezer: &Freezer) -> FreezeResult<Self::Frozen> {
        let conditions =
            self.conditions.into_iter().map(|(k, v)| Ok((k, v.freeze(freezer)?))).collect::<FreezeResult<Vec<_>>>()?;
        Ok(SelectValueGen { conditions, no_match_error: self.no_match_error })
    }
}
#[starlark_value(type = "select")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for SelectValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    /// `select(...) + rhs` — Bazel's SelectorList concatenation. `rhs` is a list/tuple/scalar (Concrete arm),
    /// another `select(...)` (Branch arm), or a SelectorList (its arms splice in). NEVER resolves.
    fn add(&self, rhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms = vec![reclone_select(self, heap)];
        splice_arm(&mut arms, rhs);
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
    /// `lhs + select(...)` — the `radd` half (`["//a"] + select({…})`): `lhs` is a Concrete arm prepended.
    fn radd(&self, lhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms = Vec::new();
        splice_arm(&mut arms, lhs);
        arms.push(reclone_select(self, heap));
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
}

/// A `+`-concatenation of select/list arms (Bazel's SelectorList). Each `arm` is EITHER a [`SelectValue`]
/// (Branch) or a plain value (Concrete); the split is recovered by downcast at `crate::convert`. Arms are
/// FLATTENED at construction (a SelectorList arm never nests). A COMPLEX value.
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
    fn freeze(self, freezer: &Freezer) -> FreezeResult<Self::Frozen> {
        let arms = self.arms.into_iter().map(|v| v.freeze(freezer)).collect::<FreezeResult<Vec<_>>>()?;
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
        splice_arm(&mut arms, rhs);
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
    fn radd(&self, lhs: Value<'v>, heap: Heap<'v>) -> Option<starlark::Result<Value<'v>>> {
        let mut arms: Vec<Value<'v>> = Vec::new();
        splice_arm(&mut arms, lhs);
        arms.extend(self.arms.iter().map(|a| a.to_value()));
        Some(Ok(heap.alloc(SelectorListValueGen { arms })))
    }
}

/// Re-materialize a live equivalent of `self` (`add`/`radd` give `&self`, not the `Value` handle); a select is
/// immutable data so a clone is behavior-identical.
fn reclone_select<'v, V: ValueLike<'v>>(s: &SelectValueGen<V>, heap: Heap<'v>) -> Value<'v> {
    heap.alloc(SelectValueGen {
        conditions: s.conditions.iter().map(|(k, v)| (k.clone(), v.to_value())).collect(),
        no_match_error: s.no_match_error.clone(),
    })
}

/// Append `arm` to a SelectorList's arms, FLATTENING a SelectorList operand (a SelectorList never nests) so
/// `convert` sees a flat Concrete/Branch sequence.
fn splice_arm<'v>(arms: &mut Vec<Value<'v>>, arm: Value<'v>) {
    if let Some(list) = SelectorListValue::from_value(arm) {
        for a in &list.arms {
            arms.push(a.to_value());
        }
    } else {
        arms.push(arm); // a SelectValue (Branch) or a plain value (Concrete) — kept verbatim.
    }
}

/// Build a [`SelectValue`] from a `select({...})` dict, canonicalizing the conditions to label-sorted order.
/// Fail-closed on a non-string condition key. The branch values stay LIVE (converted at the boundary).
pub(crate) fn make_select<'v>(dict: DictRef<'v>, no_match_error: String, heap: Heap<'v>) -> anyhow::Result<Value<'v>> {
    let mut conditions: Vec<(String, Value<'v>)> = Vec::with_capacity(dict.len());
    for (k, v) in dict.iter() {
        let key = k.unpack_str().ok_or_else(|| anyhow::anyhow!("select() condition keys must be label strings"))?.to_owned();
        conditions.push((key, v));
    }
    conditions.sort_by(|a, b| a.0.cmp(&b.0)); // canonical label-sorted (order-independent for matching)
    Ok(heap.alloc(SelectValueGen { conditions, no_match_error }))
}

