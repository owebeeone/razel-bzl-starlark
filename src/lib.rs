//! `razel-bzl-starlark` — the `BzlEvaluator` impl over `starlark-rust`. Parses/evaluates a `.bzl`'s module
//! body, resolves `load()` against caller-supplied modules (rebuilt as `FrozenModule`s and served via a
//! `ReturnFileLoader`), and projects the exports into the codec-neutral `BzlModule`. The codec-neutral model
//! is what makes early cutoff work; the frozen-module round-trip is lossless for the spike's value kinds
//! (None/Bool/Int (full i64)/Str/List). Provider/struct/function values are an analysis-phase concern (ADR-0004).

use razel_bzl_api::{BzlError, BzlEvaluator, BzlModule, BzlValue};
use starlark::environment::{FrozenModule, Globals, Module};
use starlark::eval::{Evaluator, ReturnFileLoader};
use starlark::syntax::{AstModule, Dialect};
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{UnpackValue, Value};
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
}
