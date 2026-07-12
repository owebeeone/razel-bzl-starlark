//! `LoadedFunction` — the live alloc form of a `BzlValue::FunctionRef` (T20 R-load-codec, digest tag 10).
//!
//! A function exported by a `.bzl` crosses the `BZL_LOAD` boundary as a codec-neutral `FunctionRef`
//! (`module`, `name`, `defining_digest`) — never a body. When a consuming module `load()`s it, `alloc`
//! re-materializes it as THIS value: a callable that carries the reference identity and, when INVOKED,
//! resolves the real callable through the live-module bridge (`crate::bridge`) — the defining module's cached
//! frozen live module, keyed by `(module, defining_digest)`. Re-converting a `LoadedFunction` (a re-export)
//! recovers its `FunctionRef` verbatim (lossless identity, incl. cross-module), so a function re-exported
//! through N modules keeps pointing at its true definer.
//!
//! FAIL-CLOSED: an invoke whose defining module is not in the bridge cache, or whose symbol the cached module
//! does not export, is a typed error naming BOTH the module and the symbol — never a silent no-op.

use allocative::Allocative;
use starlark::collections::StarlarkHasher;
use starlark::eval::{Arguments, Evaluator};
use starlark::starlark_simple_value;
use starlark::values::{
    starlark_value, NoSerialize, ProvidesStaticType, StarlarkPagable, StarlarkValue, Value,
};
use std::fmt;

use crate::bridge::{BridgeCtx, ModuleBridge};
use crate::eval::starlark_err;
use crate::globals::{ActionRegistry, TargetRegistry};

/// Resolve the live-module bridge from `eval.extra`: it is a `BridgeCtx` during a module load (`evaluate`),
/// rides the `ActionRegistry` during rule evaluation (`evaluate_rule`), or rides the `TargetRegistry` during
/// BUILD-file evaluation (T20 select — a BUILD calls a loaded macro / `triple_to_constraint_set(...)`). The one
/// `eval.extra` slot carries the bridge alongside whichever registry the phase installs. `None` if no bridge
/// was installed for this evaluation.
fn bridge_of<'a>(eval: &'a Evaluator) -> Option<&'a ModuleBridge> {
    let e = eval.extra?;
    if let Some(b) = e.downcast_ref::<BridgeCtx>() {
        return Some(&b.bridge);
    }
    if let Some(r) = e.downcast_ref::<ActionRegistry>() {
        return r.bridge.as_ref();
    }
    e.downcast_ref::<TargetRegistry>().and_then(|r| r.bridge.as_ref())
}

/// A loaded function reference, live in the heap. Plain data — the defining module path, the exported symbol
/// name, and the defining module's 32-byte content digest (stored as bytes so it satisfies the pagable
/// (de)serialize bounds). The real callable is NOT held; it is resolved on invoke through the bridge.
#[derive(Debug, Clone, PartialEq, Eq, ProvidesStaticType, NoSerialize, StarlarkPagable, Allocative)]
pub(crate) struct LoadedFunctionValue {
    pub(crate) module: String,
    pub(crate) name: String,
    pub(crate) digest: Vec<u8>,
}
starlark_simple_value!(LoadedFunctionValue);

impl LoadedFunctionValue {
    /// The defining digest as the fixed 32-byte array (the bridge key dimension). Fail-closed if the stored
    /// bytes are not exactly 32 (a corrupt ref — never guessed).
    pub(crate) fn digest32(&self) -> anyhow::Result<[u8; 32]> {
        <[u8; 32]>::try_from(self.digest.as_slice())
            .map_err(|_| anyhow::anyhow!("loaded function '{}' has a malformed defining digest", self.name))
    }
}

impl fmt::Display for LoadedFunctionValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<function {} (loaded from {})>", self.name, self.module)
    }
}

#[starlark_value(type = "function")]
impl<'v> StarlarkValue<'v> for LoadedFunctionValue {
    /// Call the loaded function: resolve the real callable through the live-module bridge (the defining
    /// module's cached frozen module) and forward the arguments. Fail-closed at every step.
    fn invoke(
        &self,
        _me: Value<'v>,
        args: &Arguments<'v, '_>,
        eval: &mut Evaluator<'v, '_, '_>,
    ) -> starlark::Result<Value<'v>> {
        let bridge = bridge_of(eval).ok_or_else(|| {
            starlark_err(format!(
                "loaded function '{}' (from '{}') cannot be called here: the live-module bridge is not installed in this evaluation",
                self.name, self.module
            ))
        })?;
        let digest = self.digest32().map_err(|e| starlark_err(e.to_string()))?;
        let frozen = bridge.get(&self.module, &digest).ok_or_else(|| {
            starlark_err(format!(
                "loaded function '{}': its defining module '{}' is not in the live-module bridge cache (was it evaluated?)",
                self.name, self.module
            ))
        })?;
        // `get_any_visibility` (NOT `get_option`): a struct field can reference a PRIVATE `_`-prefixed
        // top-level function (rules_rust's `rust_common.create_crate_info` → the private `_create_crate_info`),
        // which the visibility-filtered getters hide. The bridge resolves by the symbol's real binding name.
        let (owned, _vis) = frozen.get_any_visibility(&self.name).map_err(|_| {
            starlark_err(format!("module '{}' does not define a symbol '{}'", self.module, self.name))
        })?;
        // Collect the forwarded arguments (`positions`/`names_map` fold *args/**kwargs, so a
        // `create_crate_info(**kwargs)` call forwards its keywords intact).
        let pos: Vec<Value<'v>> = args.positions(eval.heap())?.collect();
        let names = args.names_map()?;
        let named: Vec<(&str, Value<'v>)> = names.iter().map(|(k, v)| (k.as_str(), *v)).collect();
        // Anchor the defining module's frozen heap into THIS evaluation's frozen heap (add_reference) so the
        // frozen callable stays valid, then forward through the standard invocation path. The raw
        // `FrozenValue` coerces to the evaluation's value lifetime (frozen values are immortal).
        eval.frozen_heap().add_reference(frozen.frozen_heap());
        let callable = owned
            .value()
            .unpack_frozen()
            .ok_or_else(|| starlark_err(format!("loaded symbol '{}' from '{}' is not frozen", self.name, self.module)))?
            .to_value();
        eval.eval_function(callable, &pos, &named)
    }

    fn write_hash(&self, hasher: &mut StarlarkHasher) -> starlark::Result<()> {
        use std::hash::Hash as _;
        self.module.hash(hasher);
        self.name.hash(hasher);
        self.digest.hash(hasher);
        Ok(())
    }
}
