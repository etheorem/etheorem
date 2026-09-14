import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Proofs.Merkle.OfShape

/-!
# `SizzLean.Proofs.Merkle.CachedSSZ`: the box roots like the spec

The cache layer's contract, proved: a fresh cached box roots to the
spec root.

    (CachedSSZ.ofValue H v).hashTreeRoot.1 = SSZType.hashTreeRoot H r.shape (r.toRepr v)

The statement names `Cache.CachedSSZ.hashTreeRoot` on the left and
`Spec.SSZType.hashTreeRoot` on the right, so the coverage report's
`cached-tree` row grades it; the `BasicSupported r.shape` gate is
what passes the shape to `ofShape_root` and `ofShape_coherent`
(`Proofs/Merkle/OfShape.lean`). No hashing runs: the proof is
symbolic in `Hasher.combine`, so no FFI-equivalence axiom enters.
Scope: the pure path only. Hash-consing (`consing := true`,
`FastBox`, `Node.consTree`) is a runtime optimisation and out of
proof scope; `SizzLeanTests/HashConsCoherence.lean` stays as the
evidence for consing boxes.

The serialize row is the one-line rfl per flavour
(`t.serialize = SSZ.serialize t.view`), and the uncached box's root
is rfl after unfolding the two wrappers.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SizzLean.Proofs.Merkle

open SizzLean.Spec
open SizzLean.Cache.MerkleTree (Node zeroLeaf merkleRootWithCache_fst)

/-- Serializing a cached box is serializing its view. -/
theorem treeBacked_serialize_eq (H : Type) [Hasher H] {T : Type} [SSZRepr T]
    (t : SizzLean.Cache.TreeBacked H T) :
    t.serialize = SSZ.serialize t.view := rfl

/-- Serializing a cached box is serializing its view, through the
`CachedSSZ` alias. -/
theorem cachedSSZ_serialize_eq (H : Type) [Hasher H] {T : Type} [SSZRepr T]
    (t : SizzLean.Cache.CachedSSZ H T) :
    t.serialize = SSZ.serialize t.view := rfl

/-- Serializing a `Box` is serializing the wrapped view: the
cached arm goes through `TreeBacked.serialize`, the uncached arm
calls the spec directly. -/
theorem box_serialize_eq (H : Type) [Hasher H] {T : Type} [SSZRepr T]
    (b : SizzLean.Cache.SSZ.Box H T) :
    b.serialize = SSZ.serialize b.view := by
  cases b with
  | cached t => exact treeBacked_serialize_eq H t
  | uncached t => rfl

/-- A fresh cached box roots to the spec root. The `BasicSupported
r.shape` gate is consumed by `ofShape_root` and `ofShape_coherent`
(`Proofs/Merkle/OfShape.lean`), and that gate is what the coverage
report's `cached-tree` row grades. The pending overlay is empty and
the tree base is the fresh `Node.ofShape` build, so the read is
`merkleRootWithCache` of a coherent tree. -/
theorem cachedSSZ_hashTreeRoot_ofValue (H : Type) [Hasher H] {T : Type}
    [r : SSZRepr T] (h_sup : SSZType.BasicSupported r.shape) (v : T) :
    (SizzLean.Cache.CachedSSZ.ofValue H v).hashTreeRoot.1
      = SSZType.hashTreeRoot H r.shape (r.toRepr v) := by
  have hcoh : (Node.ofShape H r.shape (r.toRepr v)).Coherent H :=
    ofShape_coherent H h_sup _
  have hroot : (Node.ofShape H r.shape (r.toRepr v)).root H
      = SSZType.hashTreeRoot H r.shape (r.toRepr v) :=
    ofShape_root H h_sup _
  show (SizzLean.Cache.CachedSSZ.hashTreeRoot
    (SizzLean.Cache.CachedSSZ.ofValue H v)).1 = _
  simp only [SizzLean.Cache.CachedSSZ.hashTreeRoot,
    SizzLean.Cache.TreeBacked.hashTreeRootCached,
    SizzLean.Cache.CachedSSZ.ofValue, SizzLean.Cache.TreeBacked.ofValue]
  show (Node.merkleRootWithCache H
    (Node.ofShape H r.shape (r.toRepr v))).1 = _
  rw [merkleRootWithCache_fst hcoh]
  exact hroot

/-- A fresh box in the uncached flavour roots to the spec root:
the wrapper runs the spec directly. -/
theorem uncachedSSZ_hashTreeRoot_ofValue (H : Type) [Hasher H] {T : Type}
    [r : SSZRepr T] (v : T) :
    (SizzLean.Cache.UncachedSSZ.ofValue H v).hashTreeRoot
      = SSZType.hashTreeRoot H r.shape (r.toRepr v) := by
  show SizzLean.Cache.UncachedSSZ.hashTreeRoot
    (SizzLean.Cache.UncachedSSZ.ofValue H v) = _
  rfl

/-- A fresh `Box` roots to the spec root in the cached flavour. -/
theorem box_hashTreeRoot_cached (H : Type) [Hasher H] {T : Type}
    [r : SSZRepr T] (h_sup : SSZType.BasicSupported r.shape) (v : T) :
    (SizzLean.Cache.SSZ.Box.hashTreeRoot
      (.cached (SizzLean.Cache.CachedSSZ.ofValue H v))).1
      = SSZType.hashTreeRoot H r.shape (r.toRepr v) := by
  show _ = _
  exact cachedSSZ_hashTreeRoot_ofValue H h_sup v

/-- A fresh `Box` roots to the spec root in the uncached flavour. -/
theorem box_hashTreeRoot_uncached (H : Type) [Hasher H] {T : Type}
    [r : SSZRepr T] (v : T) :
    (SizzLean.Cache.SSZ.Box.hashTreeRoot
      (.uncached (SizzLean.Cache.UncachedSSZ.ofValue H v))).1
      = SSZType.hashTreeRoot H r.shape (r.toRepr v) :=
  uncachedSSZ_hashTreeRoot_ofValue H v

end SizzLean.Proofs.Merkle
