//! `razel-bzl-starlark` — the `BzlEvaluator` impl over `starlark-rust`. Parses/evaluates a `.bzl`'s module
//! body, resolves `load()` against caller-supplied modules (rebuilt as `FrozenModule`s and served via a
//! `ReturnFileLoader`), and projects the exports into the codec-neutral `BzlModule`. The codec-neutral model
//! is what makes early cutoff work; the frozen-module round-trip is lossless for the spike's value kinds
//! (None/Bool/Int (full i64)/Str/List) plus `rule()` definitions (`BzlValue::Rule`).
//!
//! `rule()` machinery (analysis prerequisite, A1): a `.bzl` defines `my_rule = rule(implementation=…, attrs=…)`;
//! the BUILD `load()`s and calls it; calling it records a target carrying the rule's ORIGIN (defining `.bzl` +
//! symbol) — the link the analysis phase follows. The rule's impl is validated but NOT carried in codec-neutral
//! data (a heap-bound Starlark value is not codec-neutral); analysis re-obtains the live impl by re-evaluating
//! the defining `.bzl`. Custom Starlark values here are all SIMPLE (plain data) — no frozen-value-across-nodes.

use allocative::Allocative;
use razel_bzl_api::{AttrType, BzlError, BzlEvaluator, BzlModule, BzlValue, RuleDef, RuleOrigin, TargetDecl};
use starlark::environment::{FrozenModule, Globals, GlobalsBuilder, Module};
use starlark::eval::{Arguments, Evaluator, ReturnFileLoader};
use starlark::starlark_module;
use starlark::starlark_simple_value;
use starlark::syntax::{AstModule, Dialect};
use starlark::values::dict::DictRef;
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{
    starlark_value, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, UnpackValue, Value, ValueLike,
};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;

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

fn parse(name: &str, source: &str) -> Result<AstModule, BzlError> {
    AstModule::parse(name, source.to_owned(), &Dialect::Standard)
        .map_err(|e| BzlError::Parse { detail: e.to_string() })
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

/// A rule definition produced by `rule()`: the attr schema (name-sorted). The impl is validated at `rule()`
/// time but NOT stored (a heap value is not codec-neutral); analysis re-obtains it by re-evaluating the `.bzl`.
/// Projected to `BzlValue::Rule` on export (the export loop stamps the identity name + defining `.bzl`).
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
struct RuleValue {
    attrs: Vec<(String, u8)>,
}
starlark_simple_value!(RuleValue);
impl fmt::Display for RuleValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<rule>")
    }
}
#[starlark_value(type = "rule_definition")]
impl<'v> StarlarkValue<'v> for RuleValue {}

/// A loaded rule, callable in a BUILD file. Calling it instantiates a target carrying the rule's origin
/// (the analysis link). Holds only plain data — `kind` (the rule symbol), `bzl` (defining file), attr schema.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
struct RuleProxy {
    kind: String,
    bzl: String,
    attrs: Vec<(String, u8)>,
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
    if let Some(rv) = v.downcast_ref::<RuleValue>() {
        return Ok(BzlValue::Rule(RuleDef { bzl: String::new(), name: String::new(), attrs: decode_schema(&rv.attrs)? }));
    }
    if let Some(rp) = v.downcast_ref::<RuleProxy>() {
        return Ok(BzlValue::Rule(RuleDef { bzl: rp.bzl.clone(), name: rp.kind.clone(), attrs: decode_schema(&rp.attrs)? }));
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

/// Allocate a codec-neutral value into a module's heap (inverse of `convert`).
fn alloc<'v>(module: &Module<'v>, v: &BzlValue) -> Value<'v> {
    let heap = module.heap();
    match v {
        BzlValue::None => heap.alloc(NoneType),
        BzlValue::Bool(b) => Value::new_bool(*b),
        BzlValue::Int(i) => heap.alloc(*i),
        BzlValue::Str(s) => heap.alloc(s.as_str()),
        BzlValue::List(items) => {
            let vals: Vec<Value> = items.iter().map(|it| alloc(module, it)).collect();
            heap.alloc(vals)
        }
        // A rule re-materializes as a callable RuleProxy (calling it in a BUILD records a target).
        BzlValue::Rule(rd) => heap.alloc(RuleProxy {
            kind: rd.name.clone(),
            bzl: rd.bzl.clone(),
            attrs: rd.attrs.iter().map(|(n, t)| (n.clone(), t.code())).collect(),
        }),
    }
}

/// Rebuild a loaded module's bindings into a `FrozenModule` so the `ReturnFileLoader` can serve it.
fn build_frozen(m: &BzlModule) -> Result<FrozenModule, BzlError> {
    Module::with_temp_heap(|module| -> Result<FrozenModule, BzlError> {
        for (name, v) in &m.bindings {
            let val = alloc(&module, v);
            module.set(name, val);
        }
        module.freeze().map_err(|e| BzlError::Eval { detail: format!("{e:?}") })
    })
}

// ──────────────── globals ────────────────

/// `.bzl`-dialect globals: standard + `rule()` + the `attr` namespace. (BUILD-dialect globals are separate —
/// they expose `target()`, not `rule()`/`attr`, mirroring Bazel.)
fn bzl_globals() -> Globals {
    GlobalsBuilder::standard().with(rule_global).with_namespace("attr", attr_namespace).build()
}

#[starlark_module]
fn rule_global(builder: &mut GlobalsBuilder) {
    /// `rule(implementation = <fn>, attrs = {name: attr.<type>()})` — define a rule. A1 records the attr
    /// schema and validates an implementation is present; running the impl is analysis (ADR-0004).
    fn rule<'v>(
        #[starlark(require = named)] implementation: Value<'v>,
        #[starlark(require = named)] attrs: Option<DictRef<'v>>,
    ) -> anyhow::Result<RuleValue> {
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
        Ok(RuleValue { attrs: schema })
    }
}

#[starlark_module]
fn attr_namespace(builder: &mut GlobalsBuilder) {
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
fn build_globals(builder: &mut GlobalsBuilder) {
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
        let ast = parse("<load-scan>", source)?;
        Ok(ast.loads().into_iter().map(|l| l.module_id.to_owned()).collect())
    }

    fn evaluate(
        &self,
        module_name: &str,
        source: &str,
        loaded: &[(String, BzlModule)],
    ) -> Result<BzlModule, BzlError> {
        let ast = parse(module_name, source)?;
        // load()ed symbols are usable locally but are NOT re-exported (Bazel semantics) — collect their
        // local names so we can exclude them from this module's exports.
        let loaded_names: HashSet<String> =
            ast.loads().iter().flat_map(|l| l.symbols.keys().map(|k| k.to_string())).collect();
        let globals = bzl_globals(); // standard + rule() + attr namespace

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
                eval.eval_module(ast, &globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
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
        let ast = parse(package_name, source)?;
        // Standard globals + the BUILD-only `target()` builtin. (SPIKE: the Standard dialect also permits
        // `def`, which strict Bazel BUILD dialect forbids — a refinement, not a correctness gap here.)
        let globals = GlobalsBuilder::standard().with(build_globals).build();

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
                eval.eval_module(ast, &globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            Ok(registry.targets.borrow().clone())
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
}
