import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Cache.MerkleTree.Zero

/-!
# `SizzLean.Proofs.Merkle.Coherent`: the coherence invariant

`Node.root` is the structural Merkle root: it reads no cache slot
and combines the children's structural roots bottom-up. `Coherent`
says every *filled* cache slot agrees with the structural root of
its node. The invariant is exactly what makes the cached root
(`merkleRootWithCache`) equal the structural one, and what the
builders preserve (`Proofs/Merkle/Build.lean`), so a tree the
builders made caches to the root the spec's merkleizer computes.

All four theorems go by induction on the tree, with the coherence
derivation cased at each pair node. A slot some other code
filled with an arbitrary byte string is incoherent, so the
statements carry `n.Coherent H` as a hypothesis.

Lean idiom, annotated once: every `Hasher.combine` here takes the
explicit `(H := H)`. `Hasher`'s parameter is a phantom tag the
method's types do not mention, so instance synthesis cannot recover
it from the value arguments. Proof order:
`merkleRootWithCache_fst` needs nothing but the derivation;
`walked_root_eq_fst` says the walked pair is self-consistent;
`snd_coherent` needs `walked_root_eq_fst` to line the filled slot
up with the `pair_some` shape; `snd_root` needs `fst` and
`walked_root_eq_fst`; `rootOf_eq_root` needs nothing but the
derivation, because a filled slot is what `rootOf` returns.
-/

set_option autoImplicit false

/-! The two declarations below extend the cache-side `Node`
namespace from a proof module so call sites keep projection
notation (`n.root H`, `n.Coherent H`); the names live in
`SizzLean.Cache.MerkleTree` even though this file sits under
`Proofs/`. -/

namespace SizzLean.Cache.MerkleTree

/-- The structural root: reads no cache slot. Declared inside
`SizzLean.Cache.MerkleTree` for the dot notation; see the section
note above. -/
def Node.root (H : Type) [SizzLean.Hasher H] : Node → ByteArray
  | .leaf b => b
  | .pair l r _ => SizzLean.Hasher.combine (H := H) (Node.root H l) (Node.root H r)

/-- Every filled cache slot agrees with the structural root.
Declared inside `SizzLean.Cache.MerkleTree` for the dot notation;
see the section note above. -/
inductive Node.Coherent (H : Type) [SizzLean.Hasher H] : Node → Prop
  | leaf (b : ByteArray) : Node.Coherent H (.leaf b)
  | pair_none {l r : Node} :
      Node.Coherent H l → Node.Coherent H r → Node.Coherent H (.pair l r none)
  | pair_some {l r : Node} :
      Node.Coherent H l → Node.Coherent H r →
      Node.Coherent H (.pair l r (some (SizzLean.Hasher.combine (H := H) (Node.root H l) (Node.root H r))))

/-- The cached walk returns the structural root. Coherence is what
makes the returned slot agree with the structural combine. -/
theorem merkleRootWithCache_fst {H : Type} [SizzLean.Hasher H] :
    ∀ {n : Node}, n.Coherent H → (n.merkleRootWithCache H).1 = n.root H := by
  intro n
  induction n with
  | leaf b => intro _; rfl
  | pair l r slot ihl ihr =>
      intro hc
      cases slot with
      | none =>
          cases hc with
          | pair_none hl hr =>
              simp only [Node.merkleRootWithCache, Node.root]
              rw [ihl hl, ihr hr]
      | some root =>
          cases hc with
          | pair_some hl hr => rfl

/-- The walked pair is self-consistent: the second component's
structural root is the returned root. This is what lets
`snd_coherent` name the slot `pair_some` expects. -/
theorem walked_root_eq_fst {H : Type} [SizzLean.Hasher H] :
    ∀ {n : Node}, n.Coherent H →
      ((n.merkleRootWithCache H).2).root H = (n.merkleRootWithCache H).1 := by
  intro n
  induction n with
  | leaf b => intro _; rfl
  | pair l r slot ihl ihr =>
      intro hc
      cases slot with
      | none =>
          cases hc with
          | pair_none hl hr =>
              simp only [Node.merkleRootWithCache, Node.root]
              rw [ihl hl, ihr hr]
      | some _ =>
          cases hc with
          | pair_some _ _ => rfl

/-- The tree the cached walk returns is coherent. The walk fills
every slot it crosses, and coherence of the input lines the filled
slot up with the `pair_some` shape. -/
theorem merkleRootWithCache_snd_coherent {H : Type} [SizzLean.Hasher H] :
    ∀ {n : Node}, n.Coherent H → (n.merkleRootWithCache H).2.Coherent H := by
  intro n
  induction n with
  | leaf b => intro _; exact Node.Coherent.leaf b
  | pair l r slot ihl ihr =>
      intro hc
      cases slot with
      | none =>
          cases hc with
          | pair_none hl hr =>
              simp only [Node.merkleRootWithCache]
              rw [← walked_root_eq_fst hl, ← walked_root_eq_fst hr]
              exact Node.Coherent.pair_some (ihl hl) (ihr hr)
      | some _ =>
          cases hc with
          | pair_some hl hr => exact Node.Coherent.pair_some hl hr

/-- The tree the cached walk returns has the same structural root:
its children are the walked children, whose structural roots the
`walked_root_eq_fst` self-consistency turns into the returned
roots, which `merkleRootWithCache_fst` turns into the children's
structural roots. -/
theorem merkleRootWithCache_snd_root {H : Type} [SizzLean.Hasher H] :
    ∀ {n : Node}, n.Coherent H → ((n.merkleRootWithCache H).2).root H = n.root H := by
  intro n
  induction n with
  | leaf b => intro _; rfl
  | pair l r slot ihl ihr =>
      intro hc
      cases slot with
      | some _ => cases hc with | pair_some hl hr => rfl
      | none =>
          cases hc with
          | pair_none hl hr =>
              simp only [Node.merkleRootWithCache, Node.root]
              rw [walked_root_eq_fst hl, walked_root_eq_fst hr,
                merkleRootWithCache_fst hl, merkleRootWithCache_fst hr]

/-- A coherent tree's `rootOf` is its structural root: the cheap
root lookup never disagrees with the structural walk. -/
theorem rootOf_eq_root {H : Type} [SizzLean.Hasher H] :
    ∀ {n : Node}, n.Coherent H → n.rootOf H = n.root H := by
  intro n
  induction n with
  | leaf b => intro _; rfl
  | pair l r slot ihl ihr =>
      intro hc
      cases slot with
      | none =>
          cases hc with
          | pair_none hl hr =>
              simp only [Node.rootOf, Node.root]
              rw [ihl hl, ihr hr]
      | some _ =>
          cases hc with
          | pair_some hl hr => rfl

end SizzLean.Cache.MerkleTree
