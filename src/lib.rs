//! `razel-bzl-starlark` — the `BzlEvaluator` impl over `starlark-rust`. SPIKE: parse + evaluate a `.bzl`'s
//! module body and project its exported global bindings into the codec-neutral `BzlModule` value model.
//! `load()` resolution, providers, and rule/function values are out of this first cut.

use razel_bzl_api::{BzlError, BzlEvaluator, BzlModule, BzlValue};
use starlark::environment::{Globals, Module};
use starlark::eval::Evaluator;
use starlark::syntax::{AstModule, Dialect};
use starlark::values::list::ListRef;
use starlark::values::Value;

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

/// Project a starlark `Value` into the spike's value model. Unsupported kinds fail closed.
fn convert(v: Value) -> Result<BzlValue, BzlError> {
    if v.is_none() {
        return Ok(BzlValue::None);
    }
    if let Some(b) = v.unpack_bool() {
        return Ok(BzlValue::Bool(b));
    }
    if let Some(i) = v.unpack_i32() {
        return Ok(BzlValue::Int(i as i64));
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

impl BzlEvaluator for StarlarkEvaluator {
    fn evaluate(&self, module_name: &str, source: &str) -> Result<BzlModule, BzlError> {
        let ast = AstModule::parse(module_name, source.to_owned(), &Dialect::Standard)
            .map_err(|e| BzlError::Parse { detail: e.to_string() })?;
        let globals = Globals::standard();
        // The module borrows a heap with a closure-scoped lifetime, so we project Value → BzlValue (owned)
        // INSIDE the closure and only let the owned `BzlModule` escape.
        Module::with_temp_heap(|module| -> Result<BzlModule, BzlError> {
            {
                let mut eval = Evaluator::new(&module);
                eval.eval_module(ast, &globals)
                    .map_err(|e| BzlError::Eval { detail: e.to_string() })?;
            }
            let mut bindings = Vec::new();
            for name in module.names() {
                let n = name.as_str();
                // Leading-underscore bindings are module-private (not exported).
                if n.starts_with('_') {
                    continue;
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
    }
}
