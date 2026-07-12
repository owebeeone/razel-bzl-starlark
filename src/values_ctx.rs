//! `ctx` — the rule-implementation context value (row 9 grows its scalar surface). Previously a native
//! `struct`; now a custom value so it can carry both FIELDS (`ctx.label`/`ctx.attr`/`ctx.actions`/`ctx.files`/
//! `ctx.toolchains` + the row-9 scalars `ctx.var`/`ctx.bin_dir`/`ctx.genfiles_dir`/`ctx.workspace_name`/
//! `ctx.features`/`ctx.disabled_features`/`ctx.configuration`) AND METHODS (`ctx.expand_location`,
//! `ctx.expand_make_variables`). Field access rides `get_attr`; the two expanders ride `get_methods` (starlark
//! resolves a method name before an attribute, so the fields and methods never collide).
//!
//! The scalars are the razel-v1 MINIMAL honest set: `ctx.var["COMPILATION_MODE"]` = "fastbuild" (config-mode
//! threading into the analysis seam is deferred — a single default, never a wrong per-target value);
//! `bin_dir`/`genfiles_dir`.path = "" (razel's exec scheme has NO bazel-out prefix — outputs are
//! `<pkg>/<name>`); `workspace_name` = "" (the main-repo sentinel, matching a Label's `repo_name`);
//! `features`/`disabled_features` = [] (feature flags deferred); `configuration.default_shell_env` = {} (razel
//! never inherits the host env). `expand_location`/`expand_make_variables` are FAIL-CLOSED on any unsupported
//! `$(...)` form (never a silent pass-through — `mutant_expand_location_absorbs_unknown` is exactly that leak).

use allocative::Allocative;
use starlark::environment::{Methods, MethodsBuilder, MethodsStatic};
use starlark::starlark_module;
use starlark::starlark_complex_value;
use starlark::values::dict::DictRef;
use starlark::values::{
    starlark_value, Coerce, Freeze, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Trace,
    Value, ValueLifetimeless, ValueLike,
};
use std::fmt;

/// `ctx.toolchains` — the toolchain context (row 9-adjacent, R-analyze probe-driven). Bazel's `ctx.toolchains`
/// accepts EITHER a `Label` OR a label string as the index (`ctx.toolchains[Label("//rust:toolchain_type")]` in
/// rules_rust; `ctx.toolchains["//rules/rust:toolchain_type"]` in razel's own rust.bzl), so it is NOT a plain
/// dict — it normalizes the key to a canonical label string. `entries` maps the toolchain TYPE label →
/// its `ToolchainInfo` instance. A miss is a Bazel-shaped `Key ... was not found` (KeyError), never a default.
#[derive(Debug, Trace, Coerce, Freeze, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct ToolchainContextValueGen<V: ValueLifetimeless> {
    pub(crate) entries: Vec<(String, V)>,
}
starlark_complex_value!(pub(crate) ToolchainContextValue);
impl<V: ValueLifetimeless> fmt::Display for ToolchainContextValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<toolchain_context>")
    }
}
/// Normalize a `ctx.toolchains` index to its canonical type-label string: a `Label` → its display, a string →
/// itself. Anything else is unindexable (fail-closed).
fn normalize_toolchain_key(index: Value) -> Option<String> {
    if let Some(l) = index.downcast_ref::<crate::values_label::LabelValue>() {
        return Some(l.display.clone());
    }
    index.unpack_str().map(|s| s.to_owned())
}
#[starlark_value(type = "ToolchainContext")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for ToolchainContextValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    fn at(&self, index: Value<'v>, _heap: Heap<'v>) -> starlark::Result<Value<'v>> {
        let key = normalize_toolchain_key(index)
            .ok_or_else(|| crate::eval::starlark_err("ctx.toolchains index must be a Label or a label string".to_owned()))?;
        for (k, info) in &self.entries {
            if *k == key {
                return Ok(info.to_value());
            }
        }
        // Bazel's KeyError shape (`Key `…` was not found`) — a missing MANDATORY toolchain surfaces here.
        Err(crate::eval::starlark_err(format!("Key `{key}` was not found")))
    }
    /// `Label(…) in ctx.toolchains` / `"…" in ctx.toolchains` — rules_rust guards its OPTIONAL cpp toolchain
    /// with a membership test. `other` is the element being tested for membership in `self`.
    fn is_in(&self, other: Value<'v>) -> starlark::Result<bool> {
        match normalize_toolchain_key(other) {
            Some(key) => Ok(self.entries.iter().any(|(k, _)| *k == key)),
            None => Ok(false),
        }
    }
}

/// `ctx` — a bag of named field values + the two expander methods. COMPLEX (holds live field `V`s), mirroring
/// `ProviderInstanceValueGen`'s field-bag shape, plus `get_methods`.
#[derive(Debug, Trace, Coerce, Freeze, ProvidesStaticType, Allocative, NoSerialize, StarlarkPagable)]
#[repr(C)]
pub(crate) struct CtxValueGen<V: ValueLifetimeless> {
    pub(crate) fields: Vec<(String, V)>,
}
starlark_complex_value!(pub(crate) CtxValue);
impl<V: ValueLifetimeless> fmt::Display for CtxValueGen<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<ctx>")
    }
}
#[starlark_value(type = "ctx")]
impl<'v, V: ValueLike<'v>> StarlarkValue<'v> for CtxValueGen<V>
where
    Self: ProvidesStaticType<'v>,
{
    fn get_attr(&self, attribute: &str, _heap: Heap<'v>) -> Option<Value<'v>> {
        self.fields.iter().find(|(n, _)| n == attribute).map(|(_, v)| v.to_value())
    }
    fn dir_attr(&self) -> Vec<String> {
        self.fields.iter().map(|(n, _)| n.clone()).collect()
    }
    fn get_methods() -> Option<&'static Methods> {
        static RES: MethodsStatic = MethodsStatic::new("ctx", ctx_methods);
        Some(RES.methods())
    }
}

/// Read the `var` field of a live `ctx` value as a `(name, value)` map — the make-variable set
/// `expand_make_variables` resolves against. Absent/non-dict → empty.
fn ctx_var_map<'v>(this: Value<'v>) -> Vec<(String, String)> {
    let Some(ctx) = CtxValue::from_value(this) else { return Vec::new() };
    let Some((_, var)) = ctx.fields.iter().find(|(n, _)| n == "var") else { return Vec::new() };
    let Some(dict) = DictRef::from_value(var.to_value()) else { return Vec::new() };
    dict.iter()
        .filter_map(|(k, v)| Some((k.unpack_str()?.to_owned(), v.unpack_str()?.to_owned())))
        .collect()
}

/// Scan `input` for `$(...)` directives, resolving each via `resolve` (which returns the replacement, or `None`
/// for an UNSUPPORTED/unknown directive). `$$` escapes to a literal `$`. A `None` from `resolve` is a
/// FAIL-CLOSED typed error — EXCEPT under `mutant_expand_location_absorbs_unknown`, which ABSORBS the unknown
/// directive by passing it through verbatim (the exact leak the mutant proves). No `$(...)` → the input
/// verbatim. Fail-closed on an unterminated `$(`.
fn expand_directives(input: &str, what: &str, resolve: impl Fn(&str) -> Option<String>) -> anyhow::Result<String> {
    let bytes = input.as_bytes();
    let mut out = String::with_capacity(input.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'$' && i + 1 < bytes.len() && bytes[i + 1] == b'$' {
            out.push('$'); // `$$` → `$`
            i += 2;
            continue;
        }
        if bytes[i] == b'$' && i + 1 < bytes.len() && bytes[i + 1] == b'(' {
            let Some(close) = input[i + 2..].find(')') else {
                anyhow::bail!("{what}: unterminated '$(' in {input:?}");
            };
            let inner = &input[i + 2..i + 2 + close];
            match resolve(inner) {
                Some(rep) => out.push_str(&rep),
                None => {
                    if cfg!(feature = "mutant_expand_location_absorbs_unknown") {
                        // MUTANT: ABSORB the unknown directive — pass `$(inner)` through verbatim instead of
                        // failing closed. `expand_location`/`expand_make_variables` then silently mis-expand.
                        out.push_str(&input[i..i + 3 + close]);
                    } else {
                        anyhow::bail!("{what}: unsupported directive '$({inner})' (fail-closed — not built this wave)");
                    }
                }
            }
            i += 3 + close;
            continue;
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    Ok(out)
}

#[starlark_module]
fn ctx_methods(builder: &mut MethodsBuilder) {
    /// `ctx.expand_location(input, targets=[])` — expand `$(location …)`/`$(execpath …)`/… directives. razel's
    /// MINIMAL honest impl: a string with NO `$(...)` passes through; ANY location directive is FAIL-CLOSED
    /// (resolving a label to its file needs the target-file map, deferred). RED-absorbs under
    /// `mutant_expand_location_absorbs_unknown`.
    fn expand_location<'v>(
        #[starlark(this)] _this: Value<'v>,
        #[starlark(require = pos)] input: String,
        #[starlark(require = pos)] targets: Option<Value<'v>>,
    ) -> anyhow::Result<String> {
        let _ = targets; // razel does not resolve location targets this wave — every directive fails closed.
        expand_directives(&input, "ctx.expand_location", |_| None).map_err(|e| anyhow::anyhow!("{e}"))
    }

    /// `ctx.expand_make_variables(attribute_name, input, additional_substitutions={})` — expand `$(VAR)`
    /// make-variables from `ctx.var` + the additional map. FAIL-CLOSED on an unknown var (or any directive
    /// with a space — a location-style form). RED-absorbs under `mutant_expand_location_absorbs_unknown`.
    fn expand_make_variables<'v>(
        #[starlark(this)] this: Value<'v>,
        #[starlark(require = pos)] _attribute_name: String,
        #[starlark(require = pos)] input: String,
        #[starlark(require = pos)] additional_substitutions: Option<Value<'v>>,
    ) -> anyhow::Result<String> {
        let mut vars = ctx_var_map(this);
        if let Some(extra) = additional_substitutions.and_then(DictRef::from_value) {
            for (k, v) in extra.iter() {
                if let (Some(k), Some(v)) = (k.unpack_str(), v.unpack_str()) {
                    vars.push((k.to_owned(), v.to_owned()));
                }
            }
        }
        expand_directives(&input, "ctx.expand_make_variables", |inner| {
            if inner.contains(char::is_whitespace) {
                return None; // a `$(cmd arg)` form is not a make-variable — fail closed.
            }
            vars.iter().find(|(n, _)| n == inner).map(|(_, v)| v.clone())
        })
        .map_err(|e| anyhow::anyhow!("{e}"))
    }
}

/// Build the row-9 ctx SCALAR fields (appended after label/attr/toolchains/actions/files). `heap`-allocated
/// native sub-structs/dicts/lists; the values are the razel-v1 minimal honest set (see the module doc).
pub(crate) fn ctx_scalar_fields<'v>(heap: Heap<'v>, workspace_name: &str) -> Vec<(String, Value<'v>)> {
    use starlark::values::dict::AllocDict;
    use starlark::values::structs::AllocStruct;
    let var = heap.alloc(AllocDict(vec![("COMPILATION_MODE".to_string(), heap.alloc("fastbuild"))]));
    let bin_dir = heap.alloc(AllocStruct(vec![("path".to_string(), heap.alloc(""))]));
    let genfiles_dir = heap.alloc(AllocStruct(vec![("path".to_string(), heap.alloc(""))]));
    let configuration = heap.alloc(AllocStruct(vec![(
        "default_shell_env".to_string(),
        heap.alloc(AllocDict(Vec::<(Value, Value)>::new())),
    )]));
    vec![
        ("var".to_string(), var),
        ("bin_dir".to_string(), bin_dir),
        ("genfiles_dir".to_string(), genfiles_dir),
        ("workspace_name".to_string(), heap.alloc(workspace_name)),
        ("features".to_string(), heap.alloc(Vec::<Value>::new())),
        ("disabled_features".to_string(), heap.alloc(Vec::<Value>::new())),
        ("configuration".to_string(), configuration),
    ]
}
