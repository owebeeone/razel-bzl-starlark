//! `File` — the C3 value for action inputs/outputs. Exec-root-relative `.path` (razel's existing exec-path
//! scheme, e.g. `razel-wire-cbor/librazel_wire_cbor.rlib`, `external/taut-shape/src/lib.rs`), plus `.dirname`
//! and `.basename` (Bazel's File fields). NO string methods — a File is not a string. Produced by
//! `ctx.actions.declare_file` (outputs) and `ctx.files.<attr>` (sources); projected to its `.path` string in
//! the frozen ActionTemplate, so the surface swap is invisible to the action key.

use allocative::Allocative;
use starlark::collections::StarlarkHasher;
use starlark::starlark_simple_value;
use starlark::values::{starlark_value, Heap, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Value, ValueLike};
use std::fmt;

/// Project a starlark value to its exec-path string for an action template: a plain `str` is itself, a
/// `File` is its `.path`. Returns `None` for anything else (the caller fails closed). This is the ONE place
/// the interim mixed dialect (File objects for srcs/outputs, exec-path strings for the still-flat deps and
/// the razel-internal genrule fixtures) collapses into the frozen template's string exec-paths.
pub(crate) fn as_exec_string(v: Value) -> Option<String> {
    if let Some(s) = v.unpack_str() {
        return Some(s.to_owned());
    }
    v.downcast_ref::<FileValue>().map(|f| f.path.clone())
}

/// Build a `File` from an exec-root-relative path. `dirname` = everything before the last `/` (Bazel: the
/// path minus the final component, no trailing slash; "" for a top-level file); `basename` = the final
/// component.
pub(crate) fn make_file(path: String) -> FileValue {
    let (dirname, basename) = match path.rfind('/') {
        Some(i) => (path[..i].to_string(), path[i + 1..].to_string()),
        None => (String::new(), path.clone()),
    };
    FileValue { path, dirname, basename }
}

/// `File` value. Fields `.path`/`.dirname`/`.basename`; no methods. Comparable/hashable by `.path` so a
/// depset of Files dedups on identity.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct FileValue {
    pub(crate) path: String,
    pub(crate) dirname: String,
    pub(crate) basename: String,
}
starlark_simple_value!(FileValue);
impl fmt::Display for FileValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path)
    }
}
#[starlark_value(type = "File")]
impl<'v> StarlarkValue<'v> for FileValue {
    fn get_attr(&self, attribute: &str, heap: Heap<'v>) -> Option<Value<'v>> {
        match attribute {
            "path" => Some(heap.alloc(self.path.as_str())),
            "dirname" => Some(heap.alloc(self.dirname.as_str())),
            "basename" => Some(heap.alloc(self.basename.as_str())),
            _ => None, // NO string methods (`.split` is an error) — fail closed.
        }
    }
    fn dir_attr(&self) -> Vec<String> {
        vec!["basename".to_owned(), "dirname".to_owned(), "path".to_owned()]
    }
    fn equals(&self, other: Value<'v>) -> starlark::Result<bool> {
        Ok(FileValue::from_value(other).is_some_and(|o| o.path == self.path))
    }
    fn write_hash(&self, hasher: &mut StarlarkHasher) -> starlark::Result<()> {
        use std::hash::Hash as _;
        self.path.hash(hasher);
        Ok(())
    }
}
