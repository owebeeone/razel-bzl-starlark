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

use allocative::Allocative;
use razel_bzl_api::{
    ActionTemplate, AttrType, BzlError, BzlEvaluator, BzlModule, BzlValue, DepProviders, Dialect as ApiDialect,
    EvalEnv, LoadKind, PredeclaredEnvId, ProviderId, ProviderInstance, ResolvedToolchain, RuleDef, RuleOrigin,
    RuleResult, StarlarkSemanticsId, TargetDecl, TypeOptions,
};
use starlark::collections::StarlarkHasher;
use starlark::environment::{FrozenModule, GlobalsBuilder, Module};
use starlark::eval::{Arguments, Evaluator, ReturnFileLoader};
use starlark::starlark_complex_value;
use starlark::starlark_module;
use starlark::starlark_simple_value;
use starlark::syntax::{AstModule, Dialect};
use starlark::values::dict::{AllocDict, DictRef};
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::structs::AllocStruct;
use starlark::values::{
    starlark_value, Coerce, Freeze, FreezeResult, Freezer, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable,
    StarlarkValue, Trace, UnpackValue, Value, ValueLifetimeless, ValueLike,
};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;

/// The named, precomputed, digested per-phase environments (lockdown §3).
mod envs;
use envs::{env_build_bzl, env_build_file, PhaseEnv};

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

fn parse(name: &str, source: &str, dialect: &Dialect) -> Result<AstModule, BzlError> {
    AstModule::parse(name, source.to_owned(), dialect).map_err(|e| BzlError::Parse { detail: e.to_string() })
}

/// Select the named phase env an [`EvalEnv`] requests — the kind→env mapping of §1 (key fact A), applied
/// FAIL-CLOSED over what v1 has built: only `(Build{is_prelude:false}, Bzl)` under the single v1 semantics
/// row + v1 TypeOptions sentinel evaluates; every other row is a typed error, never a shared default env.
fn select_bzl_env(env: &EvalEnv) -> Result<&'static PhaseEnv, BzlError> {
    if env.semantics != StarlarkSemanticsId::v1() {
        return Err(BzlError::Unsupported {
            what: "starlark semantics row (v1 registers the single default row — keyed selection with one entry)"
                .to_owned(),
        });
    }
    if env.type_options != TypeOptions::default() {
        return Err(BzlError::Unsupported {
            what: "non-default TypeOptions (the load-time type-check pass is not built in v1)".to_owned(),
        });
    }
    match (env.load_kind, env.dialect) {
        (LoadKind::Build { is_prelude: false }, ApiDialect::Bzl) => Ok(env_build_bzl()),
        (LoadKind::Build { is_prelude: true }, _) => Err(BzlError::Unsupported {
            what: "BUILD prelude evaluation (prelude re-export is not built in v1)".to_owned(),
        }),
        (_, ApiDialect::Scl) => Err(BzlError::Unsupported {
            what: "the .scl environment (EnvScl is not built in v1; .scl is semantics-disabled)".to_owned(),
        }),
        (LoadKind::Builtins, _) | (LoadKind::Bzlmod, _) | (LoadKind::BzlmodBootstrap, _) => {
            Err(BzlError::Unsupported {
                what: format!("the predeclared environment for {:?} (not built in v1)", env.load_kind),
            })
        }
    }
}

fn starlark_err(msg: String) -> starlark::Error {
    starlark::Error::new_other(anyhow::anyhow!(msg))
}

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
struct AttrTypeValue {
    code: u8,
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
struct RuleValueGen<V: ValueLifetimeless> {
    implementation: V,
    attrs: Vec<(String, u8)>,
    toolchains: Vec<String>,
}
starlark_complex_value!(RuleValue);
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
struct Provider {
    id: String,
    fields: Vec<String>,
}
starlark_simple_value!(Provider);
impl Provider {
    /// This declaration's identity on the ONE funnel: the declared name with `bzl = None` (the v1 sentinel —
    /// the declared name IS the exported name under the single-module cap, lockdown R5). ALL live-value
    /// hashing/equality/keying goes through this + `ProviderId`'s derived impls, never the raw string.
    fn provider_id(&self) -> ProviderId {
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
struct ProviderInstanceValueGen<V: ValueLifetimeless> {
    provider_id: String,
    fields: Vec<(String, V)>,
}
starlark_complex_value!(ProviderInstanceValue);
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
struct RuleProxy {
    kind: String,
    bzl: String,
    attrs: Vec<(String, u8)>,
    toolchains: Vec<String>,
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

/// Project a starlark `Value` into the codec-neutral model. Unsupported kinds fail closed.
fn convert(v: Value) -> Result<BzlValue, BzlError> {
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
fn decode_schema(coded: &[(String, u8)]) -> Result<Vec<(String, AttrType)>, BzlError> {
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
fn alloc<'v>(module: &Module<'v>, v: &BzlValue) -> Result<Value<'v>, BzlError> {
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
fn alloc_provider_instance<'v>(module: &Module<'v>, pi: &ProviderInstance) -> Result<Value<'v>, BzlError> {
    let fields: Vec<(String, Value<'v>)> = pi
        .fields
        .iter()
        .map(|(n, bv)| Ok((n.clone(), alloc(module, bv)?)))
        .collect::<Result<_, BzlError>>()?;
    Ok(module.heap().alloc(ProviderInstanceValueGen { provider_id: pi.provider.name().to_owned(), fields }))
}

/// Rebuild a loaded module's bindings into a `FrozenModule` so the `ReturnFileLoader` can serve it.
fn build_frozen(m: &BzlModule) -> Result<FrozenModule, BzlError> {
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
fn index_providers<'v>(module: &Module<'v>, module_name: &str) -> Result<HashMap<ProviderId, Value<'v>>, BzlError> {
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

// ──────────────── globals ────────────────
// The per-phase Globals are NAMED, precomputed and digested in `envs` (lockdown §3) — the ad-hoc
// rebuilt-per-call `bzl_globals()` is gone. The registrar fns below stay here (they own the builtins).

/// Accumulates the actions a rule's impl declares (via `declare_action`). Installed in `eval.extra` during
/// `evaluate_rule` so the builtin (a `fn`, can't capture) records into it; collected into the `RuleResult`.
#[derive(Default, ProvidesStaticType)]
struct ActionRegistry {
    actions: RefCell<Vec<ActionTemplate>>,
}

#[starlark_module]
pub(crate) fn action_global(builder: &mut GlobalsBuilder) {
    /// `declare_action(mnemonic=, argv=[...], outputs=[...], inputs=[...])` — a rule impl declares an action the
    /// EXECUTION phase will run. SPIKE: a placeholder for `ctx.actions.run(...)` (the object-method form is a
    /// fidelity refinement); records an `ActionTemplate`. Fail-closed: callable only inside a rule impl.
    fn declare_action<'v>(
        #[starlark(require = named)] mnemonic: String,
        #[starlark(require = named)] argv: Value<'v>,
        #[starlark(require = named)] outputs: Value<'v>,
        #[starlark(require = named)] inputs: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ActionRegistry>())
            .ok_or_else(|| anyhow::anyhow!("declare_action can only be called inside a rule implementation"))?;
        let str_list = |v: Value<'v>, what: &str| -> anyhow::Result<Vec<String>> {
            let l = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("{what} must be a list of strings"))?;
            l.iter()
                .map(|i| i.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("{what} entries must be strings")))
                .collect()
        };
        let argv = str_list(argv, "argv")?;
        let mut outputs = str_list(outputs, "outputs")?;
        outputs.sort();
        outputs.dedup();
        let mut inputs = match inputs {
            Some(v) => str_list(v, "inputs")?,
            None => Vec::new(),
        };
        inputs.sort();
        inputs.dedup();
        reg.actions.borrow_mut().push(ActionTemplate { mnemonic, argv, env: Vec::new(), inputs, outputs });
        Ok(NoneType)
    }
}

#[starlark_module]
pub(crate) fn rule_global(builder: &mut GlobalsBuilder) {
    /// `rule(implementation = <fn>, attrs = {name: attr.<type>()}, toolchains = ["//type"])` — define a rule.
    /// Records the attr schema + the required toolchain TYPE ids; validates an implementation is present.
    /// Running the impl (+ resolving the toolchains) is analysis.
    fn rule<'v>(
        #[starlark(require = named)] implementation: Value<'v>,
        #[starlark(require = named)] attrs: Option<DictRef<'v>>,
        #[starlark(require = named)] toolchains: Option<Value<'v>>,
    ) -> anyhow::Result<RuleValue<'v>> {
        if implementation.is_none() {
            return Err(anyhow::anyhow!("rule() requires an 'implementation' function"));
        }
        let mut schema: Vec<(String, u8)> = Vec::new();
        if let Some(d) = attrs {
            for (k, v) in d.iter() {
                let key = k
                    .unpack_str()
                    .ok_or_else(|| anyhow::anyhow!("attr name must be a string"))?
                    .to_owned();
                let at = v
                    .downcast_ref::<AttrTypeValue>()
                    .ok_or_else(|| anyhow::anyhow!("attr '{key}' must be an attr.* type"))?;
                schema.push((key, at.code));
            }
        }
        schema.sort_by(|a, b| a.0.cmp(&b.0));
        let mut required: Vec<String> = match toolchains {
            None => Vec::new(),
            Some(v) => {
                let list = ListRef::from_value(v)
                    .ok_or_else(|| anyhow::anyhow!("rule() toolchains must be a list of type strings"))?;
                list.iter()
                    .map(|i| i.unpack_str().map(|s| s.to_owned()).ok_or_else(|| anyhow::anyhow!("toolchain type must be a string")))
                    .collect::<anyhow::Result<Vec<String>>>()?
            }
        };
        required.sort();
        required.dedup();
        Ok(RuleValueGen { implementation, attrs: schema, toolchains: required })
    }
}

#[starlark_module]
pub(crate) fn provider_global(builder: &mut GlobalsBuilder) {
    /// `provider(name, fields = [..])` — declare a provider type. SPIKE: identity is the explicit `name`
    /// (so it is stable across the per-target re-evaluations that the analysis phase performs).
    fn provider<'v>(
        #[starlark(require = pos)] name: String,
        #[starlark(require = named)] fields: Option<Value<'v>>,
    ) -> anyhow::Result<Provider> {
        let field_names = match fields {
            None => Vec::new(),
            Some(v) => {
                let list = ListRef::from_value(v)
                    .ok_or_else(|| anyhow::anyhow!("provider() fields must be a list of strings"))?;
                list.iter()
                    .map(|item| {
                        item.unpack_str()
                            .map(|s| s.to_owned())
                            .ok_or_else(|| anyhow::anyhow!("provider() field names must be strings"))
                    })
                    .collect::<anyhow::Result<Vec<String>>>()?
            }
        };
        Ok(Provider { id: name, fields: field_names })
    }
}

#[starlark_module]
pub(crate) fn attr_namespace(builder: &mut GlobalsBuilder) {
    fn int() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::Int.code() })
    }
    fn string() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::String.code() })
    }
    fn bool() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::Bool.code() })
    }
    fn label() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::Label.code() })
    }
    fn label_list() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::LabelList.code() })
    }
    fn string_list() -> anyhow::Result<AttrTypeValue> {
        Ok(AttrTypeValue { code: AttrType::StringList.code() })
    }
}

/// Accumulates the targets a BUILD file instantiates. Installed in `Evaluator::extra` so the `target()`
/// builtin and a `RuleProxy`'s `invoke` (neither can capture state) can record into it.
#[derive(Default, ProvidesStaticType)]
struct TargetRegistry {
    targets: RefCell<Vec<TargetDecl>>,
}

#[starlark_module]
pub(crate) fn build_globals(builder: &mut GlobalsBuilder) {
    /// `target(kind = ..., name = ..., **attrs)` — record a target instance with NO rule origin (the spike
    /// placeholder; analysis fails closed on it). The `rule()`-defined callable is the real instantiation path.
    fn target<'v>(
        #[starlark(require = named)] kind: String,
        #[starlark(require = named)] name: String,
        #[starlark(kwargs)] attrs: DictRef<'v>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<TargetRegistry>())
            .ok_or_else(|| anyhow::anyhow!("target() can only be called from a BUILD file"))?;
        // A package is keyed by target name: a duplicate is an error, never a silent last-wins.
        let is_dup = reg.targets.borrow().iter().any(|t| t.name == name);
        if is_dup && !cfg!(feature = "mutant_package_allow_dup_names") {
            return Err(anyhow::anyhow!("duplicate target name '{name}' in package"));
        }
        let mut pairs: Vec<(String, BzlValue)> = Vec::new();
        for (k, v) in attrs.iter() {
            let key = k
                .unpack_str()
                .ok_or_else(|| anyhow::anyhow!("attribute name must be a string"))?
                .to_owned();
            let val = convert(v).map_err(|e| anyhow::anyhow!("attribute '{key}': {e:?}"))?;
            pairs.push((key, val));
        }
        pairs.sort_by(|a, b| a.0.cmp(&b.0)); // canonical: name-sorted attrs → order-insensitive value
        reg.targets.borrow_mut().push(TargetDecl { kind, name, attrs: pairs, origin: None });
        Ok(NoneType)
    }
}

impl BzlEvaluator for StarlarkEvaluator {
    fn load_targets(&self, source: &str) -> Result<Vec<String>, BzlError> {
        // Parse-only load SCAN (dep discovery before any evaluation) — the permissive standard dialect is
        // deliberate: it must parse both `.bzl` and BUILD sources; the phase dialect gates real evaluation.
        let ast = parse("<load-scan>", source, &Dialect::Standard)?;
        Ok(ast.loads().into_iter().map(|l| l.module_id.to_owned()).collect())
    }

    fn predeclared_env_id(&self, kind: &LoadKind, dialect: ApiDialect) -> Result<PredeclaredEnvId, BzlError> {
        match (kind, dialect) {
            // BOTH Build{is_prelude:*} kinds SHARE EnvBuildBzl (R1) — the prelude bit is a LoadKind/key
            // bit, never an environment.
            (LoadKind::Build { .. }, ApiDialect::Bzl) => Ok(env_build_bzl().env_id),
            // Rows 3-6 have no built environment in v1 — fail closed, never a defaulted id.
            _ => Err(BzlError::Unsupported {
                what: format!("the predeclared environment for {kind:?}/{dialect:?} (not built in v1)"),
            }),
        }
    }

    fn evaluate(
        &self,
        env: &EvalEnv,
        module_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
    ) -> Result<BzlModule, BzlError> {
        let phase = select_bzl_env(env)?; // the NAMED row-1 env — fail-closed on any unbuilt row
        let ast = parse(module_name, source, &phase.dialect)?;
        // load()ed symbols are usable locally but are NOT re-exported (Bazel semantics) — collect their
        // local names so we can exclude them from this module's exports.
        let loaded_names: HashSet<String> =
            ast.loads().iter().flat_map(|l| l.symbols.keys().map(|k| k.to_string())).collect();
        let globals = &phase.globals; // EnvBuildBzl: standard + rule()/provider()/declare_action + attr

        // Rebuild each load() target as a FrozenModule, then index by target string for the loader.
        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(target, m)| build_frozen(m).map(|fm| (target.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };

        Module::with_temp_heap(|module| -> Result<BzlModule, BzlError> {
            {
                let mut eval = Evaluator::new(&module);
                eval.set_loader(&loader);
                eval.eval_module(ast, globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            // Decision H: a second same-name provider() reaching module scope is fail-closed at declaration
            // (the index result is unused here — the scan IS the collision check; aliasing stays legal).
            index_providers(&module, module_name)?;
            let mut bindings = Vec::new();
            for name in module.names() {
                let n = name.as_str();
                if n.starts_with('_') || loaded_names.contains(n) {
                    continue; // skip private + load()ed symbols; export only this module's own bindings
                }
                if let Some(v) = module.get(n) {
                    let mut bv = convert(v)?;
                    // Stamp a freshly-defined rule's identity (def-side has no origin yet). A re-exported
                    // loaded rule already carries its origin (name non-empty) — leave it.
                    if let BzlValue::Rule(rd) = &mut bv {
                        if rd.name.is_empty() {
                            rd.name = n.to_owned();
                            rd.bzl = module_name.to_owned();
                        }
                    }
                    bindings.push((n.to_owned(), bv));
                }
            }
            bindings.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(BzlModule { bindings })
        })
    }

    fn evaluate_build(
        &self,
        package_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
    ) -> Result<Vec<TargetDecl>, BzlError> {
        // Row 7, `EnvBuildFile`: the NAMED BUILD-file env (standard + the BUILD-only `target()` builtin)
        // under the def-less BUILD dialect — `def`/`lambda` in a BUILD now fail at PARSE (the spike's
        // admitted permissive-dialect gap is closed; separation is environmental, not runtime-only).
        let phase = env_build_file();
        let ast = parse(package_name, source, &phase.dialect)?;
        let globals = &phase.globals;

        // Rebuild each load() target as a FrozenModule, then index by target string for the loader — same
        // mechanism as `evaluate`; the BUILD's `load()`ed constants AND rule callables resolve through this.
        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(target, m)| build_frozen(m).map(|fm| (target.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };

        let registry = TargetRegistry::default();
        Module::with_temp_heap(|module| -> Result<Vec<TargetDecl>, BzlError> {
            {
                let mut eval = Evaluator::new(&module);
                eval.set_loader(&loader);
                eval.extra = Some(&registry); // target() and rule-callables record into this
                eval.eval_module(ast, globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            Ok(registry.targets.borrow().clone())
        })
    }

    fn evaluate_rule(
        &self,
        env: &EvalEnv,
        rule_source: &str,
        rule_module_name: &str,
        rule_name: &str,
        loaded: &[(String, BzlModule)],
        label: &str,
        attrs: &[(String, BzlValue)],
        deps: &[DepProviders],
        toolchains: &[ResolvedToolchain],
    ) -> Result<RuleResult, BzlError> {
        let phase = select_bzl_env(env)?; // the SAME row-1 env the module was loaded in
        let ast = parse(rule_module_name, rule_source, &phase.dialect)?;
        let globals = &phase.globals;

        let frozen: Vec<(String, FrozenModule)> = loaded
            .iter()
            .map(|(t, m)| build_frozen(m).map(|fm| (t.clone(), fm)))
            .collect::<Result<_, _>>()?;
        let map: HashMap<&str, &FrozenModule> = frozen.iter().map(|(t, fm)| (t.as_str(), fm)).collect();
        let loader = ReturnFileLoader { modules: &map };

        let action_registry = ActionRegistry::default();
        Module::with_temp_heap(|module| -> Result<RuleResult, BzlError> {
            let mut eval = Evaluator::new(&module);
            eval.set_loader(&loader);
            eval.extra = Some(&action_registry); // declare_action (during the impl run below) records into this
            // Define the rule, its impl, and any providers (the impl is NOT run yet — it's just a function).
            eval.eval_module(ast, globals).map_err(|e| BzlError::Eval { detail: e.to_string() })?;

            // The rule + its live implementation function (live in THIS heap — no cross-heap frozen value).
            let rule_v = module
                .get(rule_name)
                .ok_or_else(|| BzlError::Eval { detail: format!("rule '{rule_name}' not found in {rule_module_name}") })?;
            let rule = RuleValue::from_value(rule_v)
                .ok_or_else(|| BzlError::Eval { detail: format!("'{rule_name}' is not a rule") })?;
            let impl_fn = rule.implementation.to_value();
            let schema = decode_schema(&rule.attrs)?;

            // Index this eval's live Provider values by identity — these key the per-dep `{Provider: instance}`
            // dicts, matching a dep's (codec-neutral) provider id back to THIS eval's provider object.
            // Fail-closed on a duplicate declaration (decision H — the silent last-wins is dead).
            let providers_by_id = index_providers(&module, rule_module_name)?;

            // Build ctx.attr: scalars alloc directly; label-typed attrs become a list of `{Provider: instance}`
            // dicts (one per dep), so the impl can do `for d in ctx.attr.deps: d[Provider].field`.
            let heap = module.heap();
            let mut attr_fields: Vec<(String, Value)> = Vec::new();
            for (aname, aty) in &schema {
                let aval = attrs.iter().find(|(n, _)| n == aname).map(|(_, v)| v);
                if aty.is_label() {
                    let labels: Vec<String> = if cfg!(feature = "mutant_rule_eval_drops_deps") {
                        // MUTANT: ignore the dependency edges → providers don't propagate (sum is wrong).
                        Vec::new()
                    } else {
                        match aval {
                            Some(BzlValue::List(items)) => items
                                .iter()
                                .filter_map(|i| if let BzlValue::Str(s) = i { Some(s.clone()) } else { None })
                                .collect(),
                            Some(BzlValue::Str(s)) => vec![s.clone()],
                            _ => Vec::new(),
                        }
                    };
                    let mut dep_vals: Vec<Value> = Vec::new();
                    for lbl in &labels {
                        // Fail-closed: a dep label referenced by an attr but NOT supplied in `deps` is a caller
                        // error (a declared dependency went unanalyzed) — never a silently-empty provider set.
                        let providers = match deps.iter().find(|d| &d.label == lbl) {
                            Some(d) => d.providers.as_slice(),
                            None if cfg!(feature = "mutant_rule_eval_absorbs_missing_dep") => &[],
                            None => {
                                return Err(BzlError::Eval {
                                    detail: format!("dependency '{lbl}' is referenced by an attr of '{rule_name}' but no providers were supplied for it"),
                                })
                            }
                        };
                        let mut entries: Vec<(Value, Value)> = Vec::new();
                        for pi in providers {
                            // dep[Provider] re-keying rides ProviderId's derived impls (the C2 funnel): a
                            // same-name identity differing in the bzl dim is a DIFFERENT provider — miss,
                            // fail closed — never fused by raw name.
                            let key = if cfg!(feature = "mutant_provider_compares_raw_name") {
                                // MUTANT: compare the raw name only — the §0.3 leak; a bzl-differing
                                // identity silently fuses with this module's provider.
                                providers_by_id.iter().find(|(k, _)| k.name() == pi.provider.name()).map(|(_, v)| *v)
                            } else {
                                providers_by_id.get(&pi.provider).copied()
                            };
                            let key = key.ok_or_else(|| BzlError::Eval {
                                detail: format!(
                                    "provider '{}' (on dep {lbl}) is not defined in this rule's .bzl",
                                    pi.provider.name()
                                ),
                            })?;
                            entries.push((key, alloc_provider_instance(&module, pi)?));
                        }
                        dep_vals.push(heap.alloc(AllocDict(entries)));
                    }
                    attr_fields.push((aname.clone(), heap.alloc(dep_vals)));
                } else {
                    let v = match aval {
                        Some(bv) => alloc(&module, bv)?,
                        None => Value::new_none(),
                    };
                    attr_fields.push((aname.clone(), v));
                }
            }
            let attr_struct = heap.alloc(AllocStruct(attr_fields));
            // ctx.toolchains: a map {toolchain_type -> toolchain_info} (empty until phase #4 supplies resolved
            // toolchains). A missing type indexes to a fail-closed error (native dict KeyError).
            let mut tc_entries: Vec<(Value, Value)> = Vec::new();
            for t in toolchains {
                // This path bypasses the providers_by_id re-keying (a toolchain_info is injected, not looked
                // up), so the cross-module-identity wall is checked HERE: a filled bzl dim has no live
                // representation under the v1 single-module cap — fail closed, never silently drop the dim.
                if t.info.provider.bzl().is_some() {
                    return Err(BzlError::Unsupported {
                        what: format!(
                            "toolchain_info provider '{}' with a cross-module identity (bzl dim) under the v1 single-module cap",
                            t.info.provider.name()
                        ),
                    });
                }
                tc_entries.push((heap.alloc(t.toolchain_type.as_str()), alloc_provider_instance(&module, &t.info)?));
            }
            let toolchains_dict = heap.alloc(AllocDict(tc_entries));
            let ctx = heap.alloc(AllocStruct([
                ("label".to_string(), heap.alloc(label)),
                ("attr".to_string(), attr_struct),
                ("toolchains".to_string(), toolchains_dict),
            ]));

            // Run the impl, then project the returned provider instances to codec-neutral data.
            let result = eval
                .eval_function(impl_fn, &[ctx], &[])
                .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            let list = ListRef::from_value(result)
                .ok_or_else(|| BzlError::Eval { detail: "a rule impl must return a list of providers".into() })?;
            let mut out = Vec::new();
            for item in list.iter() {
                let piv = ProviderInstanceValue::from_value(item)
                    .ok_or_else(|| BzlError::Eval { detail: "a rule impl must return provider instances".into() })?;
                let mut fields = Vec::new();
                for (n, v) in &piv.fields {
                    fields.push((n.clone(), convert(v.to_value())?));
                }
                out.push(ProviderInstance { provider: ProviderId::from_name(piv.provider_id.clone()), fields });
            }
            // Decision E: a duplicate provider key on the rule's RETURN is fail-closed with Bazel's exact
            // error shape (StarlarkRuleConfiguredTargetUtil.java:273-275) — checked over the insertion-ordered
            // result at the boundary, BEFORE the canonical sort. Never a silent last-wins.
            if cfg!(feature = "mutant_rule_result_merges_dup_provider") {
                // MUTANT: restore silent last-wins — a later instance replaces the earlier one.
                let mut merged: Vec<ProviderInstance> = Vec::new();
                for pi in out {
                    match merged.iter_mut().find(|e| e.provider == pi.provider) {
                        Some(slot) => *slot = pi,
                        None => merged.push(pi),
                    }
                }
                out = merged;
            } else {
                for i in 0..out.len() {
                    if out[..i].iter().any(|e| e.provider == out[i].provider) {
                        return Err(BzlError::Eval {
                            detail: format!(
                                "Multiple conflicting returned providers with key {}",
                                out[i].provider.name()
                            ),
                        });
                    }
                }
            }
            // Canonical order (providers are a by-type set, sorted by ProviderId's derived Ord) so the node
            // value is deterministic → A4 early cutoff.
            out.sort_by(|a, b| a.provider.cmp(&b.provider));
            // actions stay empty until phase #5 wires ctx.actions; the RuleResult shape is reserved now.
            // MUTANT: drop the declared actions → they never reach the execution phase (emission test red).
            let actions = if cfg!(feature = "mutant_rule_eval_drops_actions") {
                Vec::new()
            } else {
                action_registry.actions.borrow().clone()
            };
            Ok(RuleResult { providers: out, actions })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use razel_bzl_api::conformance;

    #[test]
    fn passes_bzl_api_conformance() {
        conformance::supports_basic_bindings(&StarlarkEvaluator::new());
        conformance::parse_error_is_fail_closed(&StarlarkEvaluator::new());
        conformance::supports_load(&StarlarkEvaluator::new());
        conformance::loaded_symbols_not_reexported(&StarlarkEvaluator::new());
        conformance::rejects_unsupported_types(&StarlarkEvaluator::new());
    }

    #[test]
    fn passes_build_eval_conformance() {
        conformance::supports_target_instantiation(&StarlarkEvaluator::new());
        conformance::build_dup_name_is_fail_closed(&StarlarkEvaluator::new());
        conformance::build_uses_loaded_constant(&StarlarkEvaluator::new());
        conformance::build_rejects_unsupported_attr(&StarlarkEvaluator::new());
    }

    #[test]
    fn passes_rule_conformance() {
        conformance::supports_rule_definition(&StarlarkEvaluator::new());
        conformance::build_rule_call_records_origin(&StarlarkEvaluator::new());
        conformance::build_rule_rejects_unknown_attr(&StarlarkEvaluator::new());
        conformance::build_rule_rejects_wrong_attr_type(&StarlarkEvaluator::new());
        conformance::rule_call_outside_build_is_fail_closed(&StarlarkEvaluator::new());
    }

    #[test]
    fn passes_rule_evaluation_conformance() {
        conformance::supports_rule_evaluation(&StarlarkEvaluator::new());
        conformance::rule_eval_missing_provider_is_fail_closed(&StarlarkEvaluator::new());
        conformance::provider_rejects_unknown_field(&StarlarkEvaluator::new());
        conformance::rule_eval_missing_dep_label_is_fail_closed(&StarlarkEvaluator::new());
        conformance::supports_action_declaration(&StarlarkEvaluator::new());
    }

    /// The provider-identity lockdown gates (ADR-0004 / RazelV4ProviderIdentityLockdown §4): opaque identity
    /// comparison (C2), fail-closed duplicate declaration (H), fail-closed duplicate return (E).
    #[test]
    fn passes_provider_identity_conformance() {
        conformance::provider_identity_opaque_comparison(&StarlarkEvaluator::new());
        conformance::provider_dup_declaration_fail_closed(&StarlarkEvaluator::new());
        conformance::rule_result_dup_provider_fail_closed(&StarlarkEvaluator::new());
    }

    // ──────────────── phase-environment lockdown gates (ADR-0003 §4) ────────────────

    /// Gate `build_loaded_and_build_file_not_conflated` (the v1 cut of
    /// `build_loaded_and_bzlmod_loaded_not_conflated`): the two phases that exist today are distinct BOTH
    /// by env identity and by name-set. RED under `mutant_one_globals_all_loadkinds` (the spike's one
    /// bzl_globals() served for every phase).
    #[test]
    fn one_globals_per_phase_not_conflated() {
        conformance::phase_envs_not_conflated(&StarlarkEvaluator::new());
        assert_ne!(
            crate::envs::env_build_bzl().env_id,
            crate::envs::env_build_file().env_id,
            "EnvBuildBzl and EnvBuildFile must have distinct PredeclaredEnvIds (phase separation is keyed)"
        );
    }

    /// Gate `predeclared_env_id_is_canonical` (§4, NEW — the impl side): the SERVED ids equal the api's
    /// canonical derivation from the DECLARED registry tables, are deterministic across evaluators, and
    /// the prelude kind SHARES EnvBuildBzl (R1). RED under `mutant_env_digest_from_heap_iteration` (the
    /// id derived from live `Globals` name enumeration — heap/seam bytes — instead of the registry).
    #[test]
    fn predeclared_env_id_is_canonical() {
        use razel_bzl_api::{derive_predeclared_env_id, EnvTag};
        let e = StarlarkEvaluator::new();
        let build_bzl = e
            .predeclared_env_id(&LoadKind::Build { is_prelude: false }, ApiDialect::Bzl)
            .expect("the row-1 env id is served");
        assert_eq!(
            build_bzl,
            derive_predeclared_env_id(EnvTag::EnvBuildBzl, &crate::envs::entries(crate::envs::ENV_BUILD_BZL_TABLE), None),
            "the served id must be the canonical derivation of the DECLARED registry — never heap bytes"
        );
        assert_eq!(
            crate::envs::env_build_file().env_id,
            derive_predeclared_env_id(EnvTag::EnvBuildFile, &crate::envs::entries(crate::envs::ENV_BUILD_FILE_TABLE), None),
            "the BUILD-file env id must be the canonical derivation of its declared registry"
        );
        assert_eq!(
            e.predeclared_env_id(&LoadKind::Build { is_prelude: true }, ApiDialect::Bzl).unwrap(),
            build_bzl,
            "Build{{is_prelude:true}} SHARES EnvBuildBzl (R1) — prelude-ness is a key bit, not an env"
        );
        assert_eq!(
            StarlarkEvaluator::new().predeclared_env_id(&LoadKind::Build { is_prelude: false }, ApiDialect::Bzl).unwrap(),
            build_bzl,
            "deterministic across evaluator instances"
        );
        // Rows v1 has not built fail closed — never a defaulted id.
        assert!(e.predeclared_env_id(&LoadKind::Bzlmod, ApiDialect::Bzl).is_err());
        assert!(e.predeclared_env_id(&LoadKind::Builtins, ApiDialect::Bzl).is_err());
        assert!(e.predeclared_env_id(&LoadKind::Build { is_prelude: false }, ApiDialect::Scl).is_err());
    }

    /// The per-phase Dialect consts (§3): the BUILD dialect forbids `def` at PARSE (Bazel's BUILD
    /// dialect), closing the spike's permissive-dialect gap; `.bzl` keeps the standard set.
    #[test]
    fn build_dialect_forbids_def_at_parse() {
        assert!(
            matches!(
                StarlarkEvaluator::new().evaluate_build("pkg", "def f():\n    pass\n", &[]),
                Err(BzlError::Parse { .. })
            ),
            "a def in a BUILD file must be a PARSE error under the BUILD dialect (environmental, not runtime)"
        );
        assert!(
            StarlarkEvaluator::new()
                .evaluate(&EvalEnv::default(), "m.bzl", "def _f():\n    return 1\nx = _f()\n", &[])
                .is_ok(),
            ".bzl keeps the standard dialect (def is legal)"
        );
    }

    /// Fail-closed row selection (§3): environments v1 has not built are typed errors at the seam —
    /// an unknown semantics row, non-default TypeOptions, prelude, `.scl`, and the bzlmod kinds.
    #[test]
    fn unbuilt_env_rows_fail_closed() {
        let e = StarlarkEvaluator::new();
        let src = "x = 1\n";
        let with = |f: &dyn Fn(&mut EvalEnv)| {
            let mut env = EvalEnv::default();
            f(&mut env);
            e.evaluate(&env, "m.bzl", src, &[])
        };
        assert!(with(&|_| {}).is_ok(), "the row-1 v1 env evaluates");
        assert!(
            matches!(with(&|env| env.semantics = StarlarkSemanticsId([9; 32])), Err(BzlError::Unsupported { .. })),
            "an unknown semantics row must fail closed (keyed selection with one v1 entry)"
        );
        assert!(
            matches!(
                with(&|env| env.type_options = TypeOptions { use_type_syntax: true, ..Default::default() }),
                Err(BzlError::Unsupported { .. })
            ),
            "non-default TypeOptions must fail closed until the load-time type-check pass exists"
        );
        assert!(
            matches!(
                with(&|env| env.load_kind = LoadKind::Build { is_prelude: true }),
                Err(BzlError::Unsupported { .. })
            ),
            "prelude evaluation (re-export) is not built — fail closed"
        );
        assert!(
            matches!(with(&|env| env.dialect = ApiDialect::Scl), Err(BzlError::Unsupported { .. })),
            ".scl is semantics-disabled in v1 — fail closed"
        );
        for kind in [LoadKind::Builtins, LoadKind::Bzlmod, LoadKind::BzlmodBootstrap] {
            assert!(
                matches!(with(&|env| env.load_kind = kind), Err(BzlError::Unsupported { .. })),
                "{kind:?} has no built environment in v1 — fail closed"
            );
        }
    }
}
