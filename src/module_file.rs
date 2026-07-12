//! MODULE.bazel evaluation (D6, C6) — the reserved Bzlmod evaluation, filled. razel reads the workspace's
//! declaration surface (module name, `register_toolchains`, `new_local_repository` external roots) from the
//! SAME file real Bazel reads. Evaluated in a FAIL-CLOSED module-dialect env exposing ONLY `module()`,
//! `register_toolchains()`, `use_repo_rule()` (the last returns a callable that records repo declarations):
//! an unknown MODULE-specific name (e.g. `rule`) is a name-resolution error, never silently ignored.
//!
//! Pure w.r.t. the filesystem: the caller supplies the source bytes; the result is a codec-neutral
//! [`ModuleFileValue`] the composition root maps into `ExternalRepos` + the registered-toolchain set.

use allocative::Allocative;
use razel_bzl_api::{BzlError, ModuleFileValue, RepoDecl};
use starlark::environment::{GlobalsBuilder, Module};
use starlark::eval::{Arguments, Evaluator};
use starlark::starlark_module;
use starlark::values::list_or_tuple::UnpackListOrTuple;
use starlark::values::{starlark_value, NoSerialize, ProvidesStaticType, StarlarkValue, Value};
use starlark::{starlark_simple_value, values::none::NoneType};
use std::cell::RefCell;
use std::fmt;
use std::sync::OnceLock;

use crate::eval::starlark_err;

/// Accumulates MODULE.bazel declarations. Installed in `eval.extra` so the module builtins (which can't
/// capture) and the `new_local_repository` callable record into it.
#[derive(Default, ProvidesStaticType)]
pub(crate) struct ModuleRegistry {
    pub(crate) module_name: RefCell<String>,
    pub(crate) toolchains: RefCell<Vec<String>>,
    pub(crate) repos: RefCell<Vec<RepoDecl>>,
}

/// The value `use_repo_rule(...)` returns — a callable that records a `new_local_repository(...)` declaration.
/// Immutable handle (the mutable list lives in the `ModuleRegistry`); v1 supports the `new_local_repository`
/// repo rule only (its `name`/`path`/`build_file` are the external-source-root vocabulary).
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, Allocative)]
pub(crate) struct RepoRuleValue {
    /// The repo-rule symbol requested (`new_local_repository`) — recorded for the error message; only that
    /// one is supported in v1 (a different rule name fails closed when CALLED).
    pub(crate) rule: String,
}
starlark_simple_value!(RepoRuleValue);
impl fmt::Display for RepoRuleValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<repo_rule {}>", self.rule)
    }
}
#[starlark_value(type = "repo_rule")]
impl<'v> StarlarkValue<'v> for RepoRuleValue {
    fn invoke(&self, _me: Value<'v>, args: &Arguments<'v, '_>, eval: &mut Evaluator<'v, '_, '_>) -> starlark::Result<Value<'v>> {
        if self.rule != "new_local_repository" {
            return Err(starlark_err(format!("unsupported repo rule '{}' (v1 supports new_local_repository only)", self.rule)));
        }
        args.no_positional_args(eval.heap())?;
        let named = args.names_map()?;
        let mut name = None;
        let mut path = None;
        let mut build_file = None;
        for (k, v) in named.iter() {
            let val = v.unpack_str().ok_or_else(|| starlark_err(format!("new_local_repository '{}' must be a string", k.as_str())))?.to_owned();
            match k.as_str() {
                "name" => name = Some(val),
                "path" => path = Some(val),
                "build_file" => build_file = Some(val),
                other => return Err(starlark_err(format!("new_local_repository has no attribute '{other}'"))),
            }
        }
        let reg = eval
            .extra
            .and_then(|e| e.downcast_ref::<ModuleRegistry>())
            .ok_or_else(|| starlark_err("new_local_repository can only be called from MODULE.bazel".into()))?;
        let decl = RepoDecl {
            name: name.ok_or_else(|| starlark_err("new_local_repository requires 'name'".into()))?,
            path: path.ok_or_else(|| starlark_err("new_local_repository requires 'path'".into()))?,
            // OPTIONAL (T20 R1): a repo that ships its own BUILD/.bzl files (rules_rust) omits `build_file`;
            // only a BUILD-less repo (taut-shape) supplies the main-repo overlay label.
            build_file,
        };
        reg.repos.borrow_mut().push(decl);
        Ok(Value::new_none())
    }
}

#[starlark_module]
fn module_globals(builder: &mut GlobalsBuilder) {
    /// `module(name = …, version = …)` — record the module name (version accepted, not stored).
    fn module<'v>(
        #[starlark(require = named)] name: String,
        #[starlark(require = named)] version: Option<String>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let _ = version;
        let reg = eval.extra.and_then(|e| e.downcast_ref::<ModuleRegistry>()).ok_or_else(|| anyhow::anyhow!("module() only in MODULE.bazel"))?;
        *reg.module_name.borrow_mut() = name;
        Ok(NoneType)
    }

    /// `register_toolchains("//a", "//b", …)` — record the toolchain labels (positional varargs).
    fn register_toolchains<'v>(
        #[starlark(args)] labels: UnpackListOrTuple<String>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> anyhow::Result<NoneType> {
        let reg = eval.extra.and_then(|e| e.downcast_ref::<ModuleRegistry>()).ok_or_else(|| anyhow::anyhow!("register_toolchains() only in MODULE.bazel"))?;
        reg.toolchains.borrow_mut().extend(labels.items);
        Ok(NoneType)
    }

    /// `use_repo_rule(bzl, rule)` — return a callable that records `new_local_repository(...)` declarations.
    fn use_repo_rule<'v>(
        #[starlark(require = pos)] bzl: String,
        #[starlark(require = pos)] rule: String,
    ) -> anyhow::Result<RepoRuleValue> {
        let _ = bzl; // the defining .bzl label — v1 supports the well-known new_local_repository rule by name
        Ok(RepoRuleValue { rule })
    }
}

fn module_globals_built() -> &'static starlark::environment::Globals {
    static G: OnceLock<starlark::environment::Globals> = OnceLock::new();
    G.get_or_init(|| GlobalsBuilder::standard().with(module_globals).build())
}

/// Evaluate MODULE.bazel to its codec-neutral declarations. FAIL-CLOSED: a `.bzl`-only builtin (`rule`,
/// `provider`, …) is undefined here → a name-resolution error, never silently ignored.
pub(crate) fn evaluate_module_file(source: &str) -> Result<ModuleFileValue, BzlError> {
    let ast = starlark::syntax::AstModule::parse("MODULE.bazel", source.to_owned(), &starlark::syntax::Dialect::Standard)
        .map_err(|e| BzlError::Parse { detail: e.to_string() })?;
    let registry = ModuleRegistry::default();
    Module::with_temp_heap(|module| -> Result<ModuleFileValue, BzlError> {
        {
            let mut eval = Evaluator::new(&module);
            eval.extra = Some(&registry);
            eval.eval_module(ast, module_globals_built()).map_err(|e| BzlError::Eval { detail: e.to_string() })?;
        }
        Ok(ModuleFileValue {
            module_name: registry.module_name.borrow().clone(),
            registered_toolchains: registry.toolchains.borrow().clone(),
            repos: registry.repos.borrow().clone(),
        })
    })
}

#[cfg(test)]
mod tests {
    use super::evaluate_module_file;
    use razel_bzl_api::RepoDecl;

    /// D6: the real razel-dev MODULE.bazel shape parses to its module name, registered toolchain labels, and
    /// `new_local_repository` external-source-root declarations — the ONE declaration surface razel + Bazel
    /// share. `use_repo_rule` returns a callable that records the repo.
    #[test]
    fn parses_module_name_toolchains_and_repos() {
        let src = "module(name = \"razel\", version = \"0.0.1\")\n\
register_toolchains(\"//rules/rust:host_rust\")\n\
new_local_repository = use_repo_rule(\n\
\x20   \"@bazel_tools//tools/build_defs/repo:local.bzl\",\n\
\x20   \"new_local_repository\",\n\
)\n\
new_local_repository(\n\
\x20   name = \"taut-shape\",\n\
\x20   path = \"../taut-dev/taut-shape-rs/crates/taut-shape\",\n\
\x20   build_file = \"//overlays/taut-shape:BUILD.bazel\",\n\
)\n";
        let m = evaluate_module_file(src).expect("MODULE.bazel evaluates");
        assert_eq!(m.module_name, "razel");
        assert_eq!(m.registered_toolchains, vec!["//rules/rust:host_rust".to_string()]);
        assert_eq!(
            m.repos,
            vec![RepoDecl {
                name: "taut-shape".into(),
                path: "../taut-dev/taut-shape-rs/crates/taut-shape".into(),
                build_file: Some("//overlays/taut-shape:BUILD.bazel".into()),
            }]
        );
    }

    /// T20 R1: `build_file` is OPTIONAL — a repo that ships its OWN BUILD/.bzl files (a real Bazel module,
    /// e.g. rules_rust) declares `new_local_repository(name, path)` with NO overlay. The parse records
    /// `build_file = None` (mount AS-IS), never fails closed for the missing overlay.
    #[test]
    fn own_build_repo_omits_build_file() {
        let src = "new_local_repository = use_repo_rule(\"@bazel_tools//tools/build_defs/repo:local.bzl\", \"new_local_repository\")\n\
new_local_repository(\n\
\x20   name = \"rules_rust\",\n\
\x20   path = \"third-party/rules_rust\",\n\
)\n";
        let m = evaluate_module_file(src).expect("MODULE.bazel with an own-BUILD repo evaluates");
        assert_eq!(
            m.repos,
            vec![RepoDecl { name: "rules_rust".into(), path: "third-party/rules_rust".into(), build_file: None }],
            "an own-BUILD repo records build_file = None (read its own BUILDs AS-IS)"
        );
    }

    /// FAIL-CLOSED: a `.bzl`-only builtin (`rule`) is undefined in the MODULE dialect — a typed error, never
    /// silently ignored (the reserved Bzlmod env exposes ONLY module/register_toolchains/use_repo_rule).
    #[test]
    fn bzl_builtins_are_undefined_in_module_dialect() {
        assert!(evaluate_module_file("x = rule(implementation = 1)\n").is_err(), "rule() must be undefined in MODULE.bazel");
        assert!(evaluate_module_file("x = provider()\n").is_err(), "provider() must be undefined in MODULE.bazel");
    }
}
