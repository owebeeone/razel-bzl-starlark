//! `ctx.actions.args()` — the `Args` builder (C4, GROWN to row 8). Covers Appendix A's `.add(one)`,
//! `.add(flag, value)`, `.add_all(list)` PLUS the full projection surface a real ruleset uses:
//!   * `.add(..., format = "--foo=%s")` — a per-value `%s` template,
//!   * `.add_all(values, *, map_each=, format_each=, before_each=, uniquify=)` — a per-item callable
//!     (`map_each`, run through the live-function machinery), a `%s` template per item, a literal inserted
//!     before each item, and first-wins dedup,
//!   * `.add_joined(values, *, join_with=, format_joined=, format_each=, map_each=, uniquify=)` — the items
//!     resolved (as add_all), JOINED with `join_with`, then the whole rendered through `format_joined`,
//!   * `.use_param_file(...)` / `.set_param_file_format(...)` — ACCEPTED and recorded-not-implemented (razel
//!     inlines every arg; there is no param-file spill in this wave, so the projection stays the frozen inline
//!     argv — an actual spill would be a typed error, but nothing here spills).
//!
//! PROJECTION LAW (unchanged): every method resolves its fragment to exec-path STRINGS EAGERLY and pushes them
//! IN ORDER into the builder's flat `Vec<String>` (the `ActionRegistry` store), which flattens in order into
//! the frozen `ActionTemplate` argv. `map_each`/`format_each`/`add_joined`/`uniquify` are all computed at the
//! call, so nothing about the frozen argv shape or the action key changes — only richer ways to fill it.

use allocative::Allocative;
use starlark::environment::{Methods, MethodsBuilder, MethodsStatic};
use starlark::eval::Evaluator;
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{starlark_value, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Value, ValueLike};
use starlark::{starlark_simple_value, starlark_module};
use std::fmt;

use crate::globals::ActionRegistry;
use crate::values_depset::{depset_to_list, DepsetValue};
use crate::values_file::as_exec_string;

/// An `Args` handle: an index into the `ActionRegistry`'s arg-builder store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct ArgsValue {
    pub(crate) id: usize,
}
starlark_simple_value!(ArgsValue);
impl fmt::Display for ArgsValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Args#{}", self.id)
    }
}
#[starlark_value(type = "Args")]
impl<'v> StarlarkValue<'v> for ArgsValue {
    fn get_methods() -> Option<&'static Methods> {
        static RES: MethodsStatic = MethodsStatic::new("Args", args_methods);
        Some(RES.methods())
    }
}

/// The `ActionRegistry` from `eval.extra` (where the arg-builder store lives) — fail-closed outside a rule impl.
fn registry<'a, 'v>(eval: &'a Evaluator<'v, '_, '_>) -> anyhow::Result<&'a ActionRegistry> {
    eval.extra
        .and_then(|e| e.downcast_ref::<ActionRegistry>())
        .ok_or_else(|| anyhow::anyhow!("Args can only be used inside a rule implementation"))
}

/// The `Args` handle id from the method receiver.
fn args_id(this: Value) -> anyhow::Result<usize> {
    Ok(this.downcast_ref::<ArgsValue>().ok_or_else(|| anyhow::anyhow!("Args method receiver is not Args"))?.id)
}

/// Apply a Bazel `%s` format template (`format`/`format_each`/`format_joined`) to a rendered string. Bazel's
/// Args formats use `%s` as the sole placeholder — every `%s` is replaced by the value (a literal `%` is not
/// otherwise special here). `None` template → the value verbatim.
fn apply_format(template: Option<&str>, s: &str) -> String {
    match template {
        Some(t) => t.replace("%s", s),
        None => s.to_owned(),
    }
}

/// One item → its exec-path string (a `str` is itself, a `File` its `.path`), or `None` for a Starlark `None`
/// (Bazel's map_each may drop an item by returning None).
fn stringify(v: Value) -> anyhow::Result<Option<String>> {
    if v.is_none() {
        return Ok(None);
    }
    Ok(Some(as_exec_string(v).ok_or_else(|| anyhow::anyhow!("Args expected a string or File"))?))
}

/// The result of a `map_each` callable: `None` (drop), a single str/File, or a list of str/File → 0..N strings.
fn map_each_result(r: Value) -> anyhow::Result<Vec<String>> {
    if r.is_none() {
        return Ok(Vec::new());
    }
    if let Some(list) = ListRef::from_value(r) {
        return list
            .iter()
            .map(|e| as_exec_string(e).ok_or_else(|| anyhow::anyhow!("map_each list entries must be strings or Files")))
            .collect();
    }
    Ok(vec![as_exec_string(r).ok_or_else(|| anyhow::anyhow!("map_each must return a string, File, list, or None"))?])
}

/// Get the raw items of an `add_all`/`add_joined` `values` argument — a depset (flattened `.to_list()`, the
/// projection order) or a list. Fail-closed on anything else.
fn raw_items<'v>(values: Value<'v>) -> anyhow::Result<Vec<Value<'v>>> {
    if DepsetValue::from_value(values).is_some() {
        return depset_to_list(values);
    }
    Ok(ListRef::from_value(values)
        .ok_or_else(|| anyhow::anyhow!("Args.add_all/add_joined expects a list or depset"))?
        .iter()
        .collect())
}

/// Resolve `values` to the ordered per-item strings, applying `map_each` (a callable, run through the live
/// evaluator), then `format_each` (a `%s` template), then `uniquify` (first-wins dedup). This is the shared
/// spine of `add_all` and `add_joined`.
fn resolve_items<'v>(
    values: Value<'v>,
    map_each: Option<Value<'v>>,
    format_each: Option<&str>,
    uniquify: bool,
    eval: &mut Evaluator<'v, '_, '_>,
) -> anyhow::Result<Vec<String>> {
    let items = raw_items(values)?;
    let mut out: Vec<String> = Vec::new();
    for item in items {
        let strs = match map_each {
            // MUTANT `mutant_args_map_each_skipped`: DROP the per-item callable → the raw item is stringified
            // instead of transformed, so the projected argv is wrong (a template mismatch test goes red).
            Some(f) if !cfg!(feature = "mutant_args_map_each_skipped") => {
                let r = eval
                    .eval_function(f, &[item], &[])
                    .map_err(|e| anyhow::anyhow!("Args.map_each callable failed: {e}"))?;
                map_each_result(r)?
            }
            _ => stringify(item)?.into_iter().collect(),
        };
        for s in strs {
            out.push(apply_format(format_each, &s));
        }
    }
    if uniquify {
        let mut seen: Vec<String> = Vec::with_capacity(out.len());
        out.retain(|s| {
            if seen.iter().any(|p| p == s) {
                false
            } else {
                seen.push(s.clone());
                true
            }
        });
    }
    Ok(out)
}

fn unpack_str_opt(v: Option<Value>) -> Option<String> {
    v.and_then(|x| x.unpack_str().map(|s| s.to_owned()))
}

#[starlark_module]
fn args_methods(builder: &mut MethodsBuilder) {
    /// `args.add(value, *, format=None)` or `args.add(arg_name, value, *, format=None)` — append one or two
    /// positional strings (a `File` contributes its `.path`). `format` is a `%s` template applied to the VALUE
    /// (the second positional if given, else the first).
    fn add<'v>(
        #[starlark(this)] this: Value<'v>,
        #[starlark(require = pos)] first: Value<'v>,
        #[starlark(require = pos)] second: Option<Value<'v>>,
        #[starlark(require = named)] format: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let id = args_id(this)?;
        let fmt = unpack_str_opt(format);
        let first = as_exec_string(first).ok_or_else(|| anyhow::anyhow!("Args.add expects a string or File"))?;
        let reg = registry(eval)?;
        let mut b = reg.arg_builders.borrow_mut();
        match second {
            None => b[id].push(apply_format(fmt.as_deref(), &first)),
            Some(s) => {
                let s = as_exec_string(s).ok_or_else(|| anyhow::anyhow!("Args.add's second arg must be a string or File"))?;
                b[id].push(first); // the literal flag (never formatted)
                b[id].push(apply_format(fmt.as_deref(), &s));
            }
        }
        Ok(NoneType)
    }

    /// `args.add_all(values, *, map_each=None, format_each=None, before_each=None, uniquify=False)` — append
    /// every element, each stringified (str is itself, File is `.path`). Ordering IS the projection order (a
    /// depset flattens via `.to_list()`). `map_each` (a callable) transforms each item; `format_each` is a
    /// `%s` template; `before_each` is a literal inserted before each item's string(s); `uniquify` dedups
    /// first-wins (AFTER map_each/format_each, BEFORE before_each — Bazel's order).
    fn add_all<'v>(
        #[starlark(this)] this: Value<'v>,
        #[starlark(require = pos)] values: Value<'v>,
        #[starlark(require = named)] map_each: Option<Value<'v>>,
        #[starlark(require = named)] format_each: Option<Value<'v>>,
        #[starlark(require = named)] before_each: Option<Value<'v>>,
        #[starlark(require = named)] uniquify: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let id = args_id(this)?;
        let fe = unpack_str_opt(format_each);
        let be = unpack_str_opt(before_each);
        let uniq = uniquify.and_then(|v| v.unpack_bool()).unwrap_or(false);
        let items = resolve_items(values, map_each, fe.as_deref(), uniq, eval)?;
        let reg = registry(eval)?;
        let mut b = reg.arg_builders.borrow_mut();
        for s in items {
            if let Some(be) = &be {
                b[id].push(be.clone());
            }
            b[id].push(s);
        }
        Ok(NoneType)
    }

    /// `args.add_joined(values, *, join_with="", format_joined=None, format_each=None, map_each=None,
    /// uniquify=False)` — resolve the items (as add_all), JOIN them with `join_with`, render the join through
    /// `format_joined` (a `%s` template), and push the ONE resulting string. An empty item set pushes nothing.
    fn add_joined<'v>(
        #[starlark(this)] this: Value<'v>,
        #[starlark(require = pos)] values: Value<'v>,
        #[starlark(require = named)] join_with: Option<Value<'v>>,
        #[starlark(require = named)] format_joined: Option<Value<'v>>,
        #[starlark(require = named)] format_each: Option<Value<'v>>,
        #[starlark(require = named)] map_each: Option<Value<'v>>,
        #[starlark(require = named)] uniquify: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let id = args_id(this)?;
        let fe = unpack_str_opt(format_each);
        let fj = unpack_str_opt(format_joined);
        let jw = unpack_str_opt(join_with).unwrap_or_default();
        let uniq = uniquify.and_then(|v| v.unpack_bool()).unwrap_or(false);
        let items = resolve_items(values, map_each, fe.as_deref(), uniq, eval)?;
        if items.is_empty() {
            return Ok(NoneType); // Bazel omits add_joined entirely for an empty set (no empty string pushed).
        }
        let joined = items.join(&jw);
        registry(eval)?.arg_builders.borrow_mut()[id].push(apply_format(fj.as_deref(), &joined));
        Ok(NoneType)
    }

    /// `args.use_param_file(param_file_arg, *, use_always=False)` — ACCEPTED, recorded-not-implemented. razel
    /// INLINES every arg (no param-file spill in this wave), so the projection stays the frozen inline argv.
    /// Returns None (Bazel's return). A genuine spill need is deferred; nothing here spills, so no typed error
    /// fires. Chainable-void (returns None like Bazel).
    fn use_param_file<'v>(
        #[starlark(this)] _this: Value<'v>,
        #[starlark(require = pos)] _param_file_arg: Value<'v>,
        #[starlark(require = named)] use_always: Option<Value<'v>>,
    ) -> anyhow::Result<NoneType> {
        let _ = use_always; // razel inlines; the flag does not change the (inline) projection this wave.
        Ok(NoneType)
    }

    /// `args.set_param_file_format(format)` — ACCEPTED, recorded-not-implemented (razel inlines; no param file
    /// is written). Returns None.
    fn set_param_file_format<'v>(
        #[starlark(this)] _this: Value<'v>,
        #[starlark(require = pos)] _format: Value<'v>,
    ) -> anyhow::Result<NoneType> {
        Ok(NoneType)
    }
}
