//! `Label` — the C1 value that replaces the `ctx.label` string. A Bazel `Label` is an OBJECT with
//! `.package`/`.name`/`.workspace_name`/`.repo_name` fields and, crucially, NO string methods (`.split` is
//! an error — a Label is not a string). The rust ruleset's old `_pkg`/`_name` string surgery dies against
//! this (C1); the exec-path composition it did now lives in Rust (`LabelParts::exec_dir`, byte-identical to
//! the old `_pkg`), consumed by `ctx.files`/`ctx.actions.declare_file`.

use allocative::Allocative;
use starlark::collections::StarlarkHasher;
use starlark::starlark_simple_value;
use starlark::values::{starlark_value, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Value};
use std::fmt;

/// The parsed pieces of a target label string (`//pkg:name` or `@repo//pkg:name`). `exec_dir` is the razel
/// exec-path package directory — BYTE-IDENTICAL to the old `rust.bzl` `_pkg`: internal `//pkg:name` → `pkg`;
/// external `@repo//:name` → `external/repo`; external `@repo//sub:name` → `external/repo/sub`. That two-space
/// split (honest label fields vs the exec prefix) is razel's D1 rule; the Label carries ONLY real-Bazel
/// fields so `rust.bzl` stays executable by real Bazel later.
pub(crate) struct LabelParts {
    pub(crate) package: String,
    pub(crate) name: String,
    pub(crate) repo_name: String,
    pub(crate) workspace_name: String,
    pub(crate) exec_dir: String,
    pub(crate) display: String,
}

/// Parse a `render_label`-produced label string into honest fields + the exec-path prefix. Total (a malformed
/// string degrades to best-effort splits) — analysis only ever hands us the two canonical forms.
pub(crate) fn parse_label(label: &str) -> LabelParts {
    if let Some(rest) = label.strip_prefix('@') {
        // `@repo//pkg:name` — external. `.package` is HONEST (root package ⇒ ""), the repo rides `.repo_name`;
        // the exec prefix is `external/<repo>[/<pkg>]` (Bazel's own `external/` convention — the D1 exec side).
        let (repo, after) = rest.split_once("//").unwrap_or((rest, ""));
        let (pkg, name) = after.split_once(':').unwrap_or((after, ""));
        let exec_dir = if pkg.is_empty() {
            format!("external/{repo}")
        } else {
            format!("external/{repo}/{pkg}")
        };
        LabelParts {
            package: pkg.to_string(),
            name: name.to_string(),
            repo_name: repo.to_string(),
            workspace_name: repo.to_string(),
            exec_dir,
            display: label.to_string(),
        }
    } else {
        // `//pkg:name` — the main repo. `.repo_name`/`.workspace_name` are the "" sentinel; exec dir == package.
        let body = label.strip_prefix("//").unwrap_or(label);
        let (pkg, name) = body.split_once(':').unwrap_or((body, ""));
        LabelParts {
            package: pkg.to_string(),
            name: name.to_string(),
            repo_name: String::new(),
            workspace_name: String::new(),
            exec_dir: pkg.to_string(),
            display: label.to_string(),
        }
    }
}

/// `ctx.label` — a Label object. Fields only (`.package`/`.name`/`.workspace_name`/`.repo_name`); NO string
/// methods, so `ctx.label.split(":")` is a typed attribute error (the C1 point: a Label is not a string).
/// `str(label)` / `"%s" % label` render the canonical label text (Display), so progress/fail messages work.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct LabelValue {
    pub(crate) package: String,
    pub(crate) name: String,
    pub(crate) workspace_name: String,
    pub(crate) repo_name: String,
    pub(crate) display: String,
}
starlark_simple_value!(LabelValue);
impl fmt::Display for LabelValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display)
    }
}
#[starlark_value(type = "Label")]
impl<'v> StarlarkValue<'v> for LabelValue {
    fn get_attr(&self, attribute: &str, heap: Heap<'v>) -> Option<Value<'v>> {
        match attribute {
            "package" => Some(heap.alloc(self.package.as_str())),
            "name" => Some(heap.alloc(self.name.as_str())),
            "workspace_name" => Some(heap.alloc(self.workspace_name.as_str())),
            "repo_name" => Some(heap.alloc(self.repo_name.as_str())),
            _ => None, // NO string methods, no other fields — fail closed (a Label is not a string).
        }
    }
    fn dir_attr(&self) -> Vec<String> {
        vec!["name".to_owned(), "package".to_owned(), "repo_name".to_owned(), "workspace_name".to_owned()]
    }
    fn equals(&self, other: Value<'v>) -> starlark::Result<bool> {
        Ok(LabelValue::from_value(other).is_some_and(|o| o == self))
    }
    fn write_hash(&self, hasher: &mut StarlarkHasher) -> starlark::Result<()> {
        use std::hash::Hash as _;
        self.display.hash(hasher);
        Ok(())
    }
}
