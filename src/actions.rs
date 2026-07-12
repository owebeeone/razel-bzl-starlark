//! `ctx.actions` — the C4 action surface that replaces the `declare_action`/`write_file` globals (deleted,
//! D5 — single dialect). `.declare_file(name)` (an output File under the target's package exec dir),
//! `.run(...)` (a spawn action), `.write(output, content)` (a content-write action), `.args()` (an Args
//! builder).
//!
//! PROJECTION LAW (frozen): `.run(...)` and `.write(...)` project into the SAME 8-dim `ActionTemplate` the
//! deleted globals produced — `argv = [executable path] + flattened arguments` (Args flatten in order),
//! inputs/outputs are exec-path STRINGS (a File → its `.path`) sorted+deduped exactly as before, env is
//! name-sorted, mnemonic verbatim. The frozen `ActionKey` and the action-identity tests do not notice the
//! surface swap.
//!
//! INTERIM leniency (blessed for this wave — the depset/RustInfo flip is C5): `run`'s `inputs`/`outputs` and
//! `write`'s `output` accept exec-path STRINGS as well as Files/depsets, because the still-flat `DefaultInfo`
//! deps and the razel-internal genrule/action fixtures pass strings. The real `rust.bzl` uses File outputs
//! (Bazel-faithful); the string tolerance is what lets the mixed dialect stay green until C5.

use allocative::Allocative;
use razel_bzl_api::ActionTemplate;
use starlark::environment::{Methods, MethodsBuilder, MethodsStatic};
use starlark::eval::Evaluator;
use starlark::values::dict::DictRef;
use starlark::values::list::ListRef;
use starlark::values::none::NoneType;
use starlark::values::{starlark_value, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Value, ValueLike};
use starlark::{starlark_simple_value, starlark_module};
use std::fmt;

use crate::globals::ActionRegistry;
use crate::values_args::ArgsValue;
use crate::values_depset::{depset_to_list, DepsetValue};
use crate::values_file::{as_exec_string, make_file, FileValue};

/// `ctx.actions` — carries the target's package exec dir (byte-identical to the old `_pkg`), so
/// `declare_file(name)` places an output exactly where the string-built outputs landed.
#[derive(Debug, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct ActionsValue {
    pub(crate) exec_dir: String,
}
starlark_simple_value!(ActionsValue);
impl fmt::Display for ActionsValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ctx.actions")
    }
}
#[starlark_value(type = "ctx.actions")]
impl<'v> StarlarkValue<'v> for ActionsValue {
    fn get_methods() -> Option<&'static Methods> {
        static RES: MethodsStatic = MethodsStatic::new("ctx.actions", actions_methods);
        Some(RES.methods())
    }
}

/// Flatten a value into exec-path strings for the `inputs` slot: a depset (flattened via `.to_list()`), or a
/// list of Files/strings. Fail-closed on anything else.
fn collect_inputs(v: Value) -> anyhow::Result<Vec<String>> {
    if DepsetValue::from_value(v).is_some() {
        let items = depset_to_list(v)?;
        return items
            .into_iter()
            .map(|e| as_exec_string(e).ok_or_else(|| anyhow::anyhow!("action input depset entries must be Files or strings")))
            .collect();
    }
    let list = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("action inputs must be a depset or a list of Files/strings"))?;
    list.iter()
        .map(|e| as_exec_string(e).ok_or_else(|| anyhow::anyhow!("action input entries must be Files or strings")))
        .collect()
}

/// A list of Files/strings → exec-path strings (for `outputs`).
fn collect_paths(v: Value, what: &str) -> anyhow::Result<Vec<String>> {
    let list = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("{what} must be a list of Files/strings"))?;
    list.iter()
        .map(|e| as_exec_string(e).ok_or_else(|| anyhow::anyhow!("{what} entries must be Files or strings")))
        .collect()
}

/// `arguments = [str | File | Args, …]` → the flattened argv tail, IN ORDER. An `Args` contributes its
/// accumulated fragment (looked up in the registry's builder store by id); a str/File contributes one string.
fn flatten_arguments(v: Value, builders: &[Vec<String>]) -> anyhow::Result<Vec<String>> {
    let list = ListRef::from_value(v).ok_or_else(|| anyhow::anyhow!("run arguments must be a list"))?;
    let mut out = Vec::new();
    for item in list.iter() {
        if let Some(args) = item.downcast_ref::<ArgsValue>() {
            let frag = builders.get(args.id).ok_or_else(|| anyhow::anyhow!("Args handle {} is unknown", args.id))?;
            out.extend(frag.iter().cloned());
        } else if let Some(s) = as_exec_string(item) {
            out.push(s);
        } else {
            return Err(anyhow::anyhow!("run arguments entries must be strings, Files, or Args objects"));
        }
    }
    Ok(out)
}

#[starlark_module]
fn actions_methods(builder: &mut MethodsBuilder) {
    /// `ctx.actions.args()` — a fresh Args builder (a new fragment slot in the registry, returned as a handle).
    fn args<'v>(
        #[starlark(this)] _this: Value<'v>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<ArgsValue> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ActionRegistry>())
            .ok_or_else(|| anyhow::anyhow!("ctx.actions.args can only be called inside a rule implementation"))?;
        let mut b = reg.arg_builders.borrow_mut();
        b.push(Vec::new());
        Ok(ArgsValue { id: b.len() - 1 })
    }

    /// `ctx.actions.declare_file(name)` — an output File at `<package exec dir>/<name>` (exactly where the
    /// old string-built outputs landed → output exec paths stay byte-identical).
    fn declare_file<'v>(
        #[starlark(this)] this: Value<'v>,
        #[starlark(require = pos)] name: String,
    ) -> anyhow::Result<FileValue> {
        let actions = this.downcast_ref::<ActionsValue>().ok_or_else(|| anyhow::anyhow!("declare_file receiver is not ctx.actions"))?;
        // MUTANT: ignore the package exec dir → the File lands at the bare name, not `<pkg>/<name>`, so
        // staging/emit paths (and thus action identity) are wrong.
        let path = if cfg!(feature = "mutant_declare_file_ignores_package") {
            name
        } else {
            format!("{}/{}", actions.exec_dir, name)
        };
        Ok(make_file(path))
    }

    /// `ctx.actions.run(executable=, arguments=, inputs=, outputs=, mnemonic=, env=, progress_message=,
    /// use_default_shell_env=)` — a spawn action. Projects to the frozen 8-dim ActionTemplate (see the
    /// PROJECTION LAW above). `progress_message`/`use_default_shell_env` are accepted; razel's env is always
    /// the declared map (no host inheritance), so they do not enter the template.
    fn run<'v>(
        #[starlark(this)] _this: Value<'v>,
        #[starlark(require = named)] executable: Value<'v>,
        #[starlark(require = named)] arguments: Option<Value<'v>>,
        #[starlark(require = named)] inputs: Option<Value<'v>>,
        #[starlark(require = named)] outputs: Value<'v>,
        #[starlark(require = named)] mnemonic: String,
        #[starlark(require = named)] env: Option<DictRef<'v>>,
        #[starlark(require = named)] progress_message: Option<String>,
        #[starlark(require = named)] use_default_shell_env: Option<Value<'v>>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let _ = (progress_message, use_default_shell_env); // accepted, not part of the template
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ActionRegistry>())
            .ok_or_else(|| anyhow::anyhow!("ctx.actions.run can only be called inside a rule implementation"))?;
        let exe = as_exec_string(executable).ok_or_else(|| anyhow::anyhow!("run executable must be a string or File"))?;
        let mut argv = vec![exe];
        // MUTANT: drop the flattened arguments → argv is just the executable, so the spawn is wrong.
        if !cfg!(feature = "mutant_ctx_actions_run_drops_arguments") {
            if let Some(a) = arguments {
                let builders = reg.arg_builders.borrow();
                argv.extend(flatten_arguments(a, &builders)?);
            }
        }
        let mut outputs = collect_paths(outputs, "run outputs")?;
        outputs.sort();
        outputs.dedup();
        let mut inputs = match inputs {
            Some(v) => collect_inputs(v)?,
            None => Vec::new(),
        };
        inputs.sort();
        inputs.dedup();
        let mut env_pairs: Vec<(String, String)> = Vec::new();
        if let Some(d) = env {
            for (k, v) in d.iter() {
                let name = k.unpack_str().ok_or_else(|| anyhow::anyhow!("env names must be strings"))?;
                let val = v.unpack_str().ok_or_else(|| anyhow::anyhow!("env values must be strings"))?;
                env_pairs.push((name.to_owned(), val.to_owned()));
            }
            env_pairs.sort_by(|a, b| a.0.cmp(&b.0));
        }
        reg.actions.borrow_mut().push(ActionTemplate { mnemonic, argv, env: env_pairs, inputs, outputs });
        Ok(NoneType)
    }

    /// `ctx.actions.write(output=, content=)` — a no-subprocess content-write action. Projects to the shared
    /// WriteFile convention (`mnemonic="WriteFile"`, `argv=["write_file", content]`, one output) — byte-
    /// identical to the deleted `write_file` global, so `razel-exec-api`'s `WriteStrategy` still emits it.
    fn write<'v>(
        #[starlark(this)] _this: Value<'v>,
        #[starlark(require = named)] output: Value<'v>,
        #[starlark(require = named)] content: String,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ActionRegistry>())
            .ok_or_else(|| anyhow::anyhow!("ctx.actions.write can only be called inside a rule implementation"))?;
        let out = as_exec_string(output).ok_or_else(|| anyhow::anyhow!("write output must be a File or string"))?;
        reg.actions.borrow_mut().push(ActionTemplate {
            mnemonic: "WriteFile".to_string(),
            argv: vec!["write_file".to_string(), content],
            env: Vec::new(),
            inputs: Vec::new(),
            outputs: vec![out],
        });
        Ok(NoneType)
    }
}
