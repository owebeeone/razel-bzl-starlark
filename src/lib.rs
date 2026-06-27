//! `razel-bzl-starlark` — the `BzlEvaluator` impl over `starlark-rust`. Parses/evaluates a `.bzl`'s module
//! body, resolves `load()` against caller-supplied modules (rebuilt as `FrozenModule`s and served via a
//! `ReturnFileLoader`), and projects the exports into the codec-neutral `BzlModule`. The codec-neutral model
//! is what makes early cutoff work; the frozen-module round-trip is lossless for the spike's value kinds
//! (None/Bool/Int (full i64)/Str/List). Provider/struct/function values are an analysis-phase concern (ADR-0004).

use razel_bzl_api::{BzlError, BzlEvaluator, BzlModule, BzlValue, TargetDecl};
use starlark::environment::{FrozenModule, Globals, GlobalsBuilder, Module};
use starlark::eval::{Evaluator, ReturnFileLoader};
use starlark::starlark_module;
use starlark::syntax::{AstModule, Dialect};
use starlark::values::dict::DictRef;
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{ProvidesStaticType, UnpackValue, Value};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

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
    Err(BzlError::Unsupported { what: v.get_type().to_owned() })
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

/// Accumulates the targets a BUILD file instantiates. Installed in `Evaluator::extra` so the `target()`
/// builtin (a `fn`, which cannot capture state) can record into it. Interior mutability because `extra` is a
/// shared reference for the lifetime of the evaluation.
#[derive(Default, ProvidesStaticType)]
struct TargetRegistry {
    targets: RefCell<Vec<TargetDecl>>,
}

#[starlark_module]
fn build_globals(builder: &mut GlobalsBuilder) {
    /// `target(kind = ..., name = ..., **attrs)` — record a target instance (DATA). It does NOT run any rule
    /// logic; running rules (providers/actions) is analysis (ADR-0004). Duplicate names within the package are
    /// rejected fail-closed. Attr values are projected through the codec-neutral model — an unrepresentable
    /// value (e.g. a function) is a loud error, never silently dropped.
    fn target<'v>(
        #[starlark(require = named)] kind: String,
        #[starlark(require = named)] name: String,
        #[starlark(kwargs)] attrs: DictRef<'v>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .expect("BUILD eval must install a TargetRegistry in eval.extra")
            .downcast_ref::<TargetRegistry>()
            .expect("eval.extra must be a TargetRegistry");
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
        reg.targets.borrow_mut().push(TargetDecl { kind, name, attrs: pairs });
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
        let globals = Globals::standard();

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
                    bindings.push((n.to_owned(), convert(v)?));
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
        // mechanism as `evaluate`; the BUILD's `load()`ed constants resolve through this.
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
                eval.extra = Some(&registry); // the `target()` builtin records into this
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
}
