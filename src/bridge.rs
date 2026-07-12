//! The LIVE-MODULE BRIDGE (T20 R-load-codec, `RazelRulesRustCompatPlan.md` §R-load).
//!
//! A `.bzl` that exports a FUNCTION (`triple.bzl` → `get_host_triple`) or a STRUCT with function-valued fields
//! (`common.bzl` → `rust_common = struct(create_crate_info = _create_crate_info, …)`) crosses the `BZL_LOAD`
//! node boundary as a codec-neutral `BzlValue` (tag 10 / tag 9). The codec carries the function's IDENTITY
//! (`module`, `name`, `defining_digest`) but NEVER its body — Bazel itself never serializes Starlark functions
//! (Skyframe holds live modules). So when a sibling module `load()`s and CALLS such a function, razel must
//! re-materialize the LIVE callable. This module is the bridge: a per-evaluator cache of the frozen live
//! module keyed by `(module path, defining_digest)`, populated when each module is evaluated and read when a
//! `LoadedFunction` (the tag-10 alloc form) is invoked.
//!
//! INVALIDATION SOUNDNESS: the cache key includes `defining_digest` = a content hash of the defining module
//! (its source ⊕ the digests of the modules it loads). A body change re-fingerprints the whole defining
//! module → its `FunctionRef`s re-fingerprint → every dependent's `BZL_LOAD` value changes → dependents
//! re-evaluate (module-content-level early cutoff, the SAME granularity as Bazel). The defining module's
//! sources are already graph deps of the consumer via the existing `load()` edges, so a cache keyed by this
//! digest never serves a stale module: a fresh digest is a fresh key.

use razel_bzl_api::{encode_bzl_value, BzlModule};
use starlark::environment::FrozenModule;
use starlark::values::ProvidesStaticType;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// A stable, dependency-free 32-byte content hash — the SAME algorithm as `razel_core::Digest::of` (FNV-1a
/// accumulation + a splitmix64 avalanche expansion), vendored here because the seam wall forbids
/// `razel-bzl-starlark → razel-core`. Deterministic across runs; a single-byte change diffuses across the
/// whole digest. Used ONLY to compute a `FunctionRef.defining_digest` (a fresh tag-10 field, not a frozen
/// golden), so mirroring rather than sharing the impl is safe.
pub(crate) fn content_hash32(bytes: &[u8]) -> [u8; 32] {
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= *b as u64;
        h = h.wrapping_mul(PRIME);
    }
    h ^= bytes.len() as u64;
    h = h.wrapping_mul(PRIME);
    let mut out = [0u8; 32];
    let mut x = h;
    for chunk in out.chunks_mut(8) {
        x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        chunk.copy_from_slice(&z.to_le_bytes());
    }
    out
}

/// The defining-module content digest for a module being evaluated: its SOURCE bytes ⊕ (per `load()` dep, in
/// order) the dep's load target string ⊕ the canonical encoding of the dep's exported bindings. Folding the
/// loaded deps in makes the digest TRANSITIVELY source-sensitive: if a loaded module changes (even one whose
/// function this module merely re-exports), this module's digest changes too — so early cutoff is sound
/// through re-exports, not just direct edits. Mirrors Bazel's transitive-source digest basis.
pub(crate) fn defining_digest(source: &str, loaded: &[(String, BzlModule)]) -> [u8; 32] {
    let mut buf: Vec<u8> = Vec::with_capacity(source.len() + 64);
    buf.extend_from_slice(source.as_bytes());
    for (target, module) in loaded {
        buf.extend_from_slice(&(target.len() as u64).to_be_bytes());
        buf.extend_from_slice(target.as_bytes());
        for (name, value) in &module.bindings {
            buf.extend_from_slice(&(name.len() as u64).to_be_bytes());
            buf.extend_from_slice(name.as_bytes());
            encode_bzl_value(value, &mut buf);
        }
    }
    content_hash32(&buf)
}

/// The per-evaluator live-module cache: `(module path, defining_digest) → the frozen live module`. Cloneable
/// (an `Arc` handle) so it can be shared into `BridgeCtx` for the invoke path AND kept on the evaluator for
/// population. `FrozenModule` is `Dupe` (two `Arc`s) and `Send + Sync`, so the cache is cheaply shared and
/// thread-safe (the engine may evaluate nodes concurrently).
#[derive(Clone, Default)]
pub(crate) struct ModuleBridge {
    cache: Arc<Mutex<HashMap<(String, [u8; 32]), FrozenModule>>>,
}

impl ModuleBridge {
    /// Cache a freshly-evaluated module's frozen form under its identity. Overwrites on a digest match
    /// (idempotent: the same digest ⇒ the same content). The MUTANT keys by PATH ONLY and is insert-if-absent,
    /// so a re-evaluation with a CHANGED digest is ignored → the stale module is served (the re-evaluation
    /// gate goes red).
    pub(crate) fn insert(&self, module: &str, digest: [u8; 32], frozen: FrozenModule) {
        let mut c = self.cache.lock().expect("module-bridge cache poisoned");
        if cfg!(feature = "mutant_live_module_cache_ignores_digest") {
            // MUTANT: drop the digest from the key AND refuse to refresh → a content change never re-caches.
            c.entry((module.to_owned(), [0u8; 32])).or_insert(frozen);
        } else {
            c.insert((module.to_owned(), digest), frozen);
        }
    }

    /// Look up a cached module by its `(path, defining_digest)` identity. The MUTANT drops the digest from the
    /// lookup key, so it serves whatever module was FIRST cached at that path regardless of the requested
    /// content digest (stale).
    pub(crate) fn get(&self, module: &str, digest: &[u8; 32]) -> Option<FrozenModule> {
        let c = self.cache.lock().expect("module-bridge cache poisoned");
        let key = if cfg!(feature = "mutant_live_module_cache_ignores_digest") {
            (module.to_owned(), [0u8; 32])
        } else {
            (module.to_owned(), *digest)
        };
        c.get(&key).cloned()
    }
}

/// The `eval.extra` context that carries the module bridge into a running evaluation, so a `LoadedFunction`'s
/// `invoke` (a capture-less starlark method) can reach the cache. Set during `evaluate` (module load — where
/// a `.bzl` may call a loaded function at load time). A `ProvidesStaticType` newtype over the cheap `Arc`
/// handle.
#[derive(ProvidesStaticType)]
pub(crate) struct BridgeCtx {
    pub(crate) bridge: ModuleBridge,
}
