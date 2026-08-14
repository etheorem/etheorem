import SizzLean
import LeanHazmatSha256

/-!
# `SizzLeanTests.ZeroHashDepth`: the zero-hash tower past its table

The zero-hashes tower is a recurrence, `Z[0] = 32·0x00` and
`Z[d+1] = combine Z[d] Z[d]`, materialised as a table for the depths
merkleization actually visits. Two tables exist: the spec-side
`Spec.ZERO_HASHES_SPEC` and the cache-side memo behind
`Cache.MerkleTree.zeroHashAt`. Both hold 100 entries, matching
`merkle_minimal.py`'s `zerohashes`.

Past 100 the spec raises `IndexError`; both of ours continue the
recurrence instead, because merkleization has no error channel to
report into (a `ByteArray` in, a `ByteArray` out, through every
`SSZRepr` instance). What this file pins is that *continuing* is what
they do. The alternative a total function invites is a clamped
stand-in, which is what these tables held before, and it splits the
two Merkle paths apart at the depth the table ends: `merkleize`
short-circuits an empty chunk list through one table lookup, while
`Node.ofLeaves` keeps building `pair` nodes to whatever depth it is
handed, so a clamp makes them disagree at 65 while agreeing at 64.

No SSZ type reaches these depths. `MAX_LENGTH = 2^32` caps a real
tree near depth 34, and the deepest consensus cap,
`VALIDATOR_REGISTRY_LIMIT = 2^40`, reaches 40. The pins below use
synthetic caps to reach past the table on purpose, since the
boundary is exactly where a reintroduced clamp would hide.

`native_decide` throughout: the roots are FFI-`Sha256` bytes, so the
kernel cannot reduce them (CLAUDE.md, case 2). Each call adds one
`Lean.ofReduceBool` axiom.
-/

set_option autoImplicit false

namespace SizzLeanTests.ZeroHashDepth

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache.MerkleTree

/-! ## The recurrence continues past the table

`zeroHashAt` reads the memo below 100 and recomputes above it, so the
two ranges are two different code paths meeting at 100. These pin the
join: each side of the boundary is the `combine` of the entry below
it, which is the whole content of the recurrence. -/

/-- The last memoised entry. Inside the table, so this pins the memo
itself against the recurrence rather than the fallback. -/
example :
    zeroHashAt Sha256 99 =
      Hasher.combine (H := Sha256) (zeroHashAt Sha256 98) (zeroHashAt Sha256 98) := by
  native_decide

/-- The first entry past the table: computed, not looked up, and it
still extends the memoised entry below it. A clamp to the deepest
entry would make this equal `zeroHashAt Sha256 99`; a `zero32`
fallback would make it the all-zero chunk. -/
example :
    zeroHashAt Sha256 100 =
      Hasher.combine (H := Sha256) (zeroHashAt Sha256 99) (zeroHashAt Sha256 99) := by
  native_decide

/-- One level further, so the fallback is exercised on both operands
rather than only on the result. -/
example :
    zeroHashAt Sha256 101 =
      Hasher.combine (H := Sha256) (zeroHashAt Sha256 100) (zeroHashAt Sha256 100) := by
  native_decide

/-- Neither fallback value: not the shallowest entry (the `zero32`
this replaced), and not the deepest memoised one (the clamp its
docstring used to claim). -/
example : (zeroHashAt Sha256 100 == zeroHashAt Sha256 0) = false := by native_decide

example : (zeroHashAt Sha256 100 == zeroHashAt Sha256 99) = false := by native_decide

/-! ## The two Merkle paths agree past the table

`Spec.hashTreeRoot` of an empty `List[T, cap]` merkleizes an empty
chunk list at `chunkDepth cap`, which is the single table lookup, and
mixes in the length. `Node.ofLeaves` at the same depth builds the
tree. Below the table these agreed already; the rows here are the
ones a clamp used to break. -/

/-- The zero root at a given depth, built the long way: an empty leaf
list padded out to `depth` by `Node.ofLeaves`. -/
private def treeZeroRoot (depth : Nat) : ByteArray :=
  (Node.ofLeaves Sha256 [] depth).merkleRoot Sha256

/-- The same root the spec side computes, as the body root of an
empty composite-element list whose cap needs `depth` levels. Stated
against `merkleize`'s empty-list arm through the public
`SSZType.hashTreeRoot`, so the pin runs the shipped path. -/
private def specZeroBodyRoot (cap : Nat) : ByteArray :=
  SizzLean.Spec.SSZType.hashTreeRoot Sha256
    (.list (.vector (.uintN 8) 32) cap) ⟨#[], by simp⟩

/-- Depth 34 (`cap = 2^34`): inside the table, the case that agreed
even with the clamp in place. Present so a regression that moves the
boundary shows up as a *changed* row rather than a new one. The
mix-in of a zero length is `combine bodyRoot (32·0x00)`. -/
example :
    specZeroBodyRoot (2 ^ 34) =
      Hasher.combine (H := Sha256) (treeZeroRoot 34) (Spec.natToChunk 0) := by
  native_decide

/-- Depth 101 (`cap = 2^101`): past the table on both sides. This is
the row the clamp got wrong, `merkleize` returning a table stand-in
while `Node.ofLeaves` built the real depth-101 zero subtree. -/
example :
    specZeroBodyRoot (2 ^ 101) =
      Hasher.combine (H := Sha256) (treeZeroRoot 101) (Spec.natToChunk 0) := by
  native_decide

end SizzLeanTests.ZeroHashDepth
