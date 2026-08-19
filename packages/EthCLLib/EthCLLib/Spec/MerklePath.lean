/-!
# `EthCLLib.Spec.MerklePath`: the path-routing convention

Which side the walk mixes a sibling in on at each level of a Merkle path. The
spec's branch walk routes by this, and so do the honest openers in
`EthCLLib.Proofs.MerkleOpening`. The pyspec spells the same bit
`index // (2**i) % 2`.

Level `i` reads bit `i` of `index`. A set bit puts the opened node on the right,
so its sibling goes on the left.

The convention belongs to `is_valid_merkle_branch`, which is a consensus-spec
function rather than an SSZ-document one. It therefore lives framework-side, and
SizzLean never sees it. A leaf module with no imports, so any layer can take it.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- Merkle path routing at level `i`: `true` when `index` has bit `i` set. The
opened node then sits in the right subtree at that level, and the walk mixes the
sibling in on the left.

`computeMerkleBranchRoot` and the honest openers both route by this one
definition, so the shipped check and the proofs agree by definition. -/
def routeRight (index i : Nat) : Bool := (index >>> i) &&& 1 == 1

/-! The two spellings, `(index >>> i) &&& 1 == 1` here against the pyspec's
`index // (2**i) % 2`, are equal but not syntactically equal. The theorem below
is the only thing that ties our spelling to the spec's, so keep it even when no
proof needs it to typecheck.

The convention is worth pinning because inverting it is root-preserving on a
shape-symmetric perfect tree. The walk opens the mirror leaf, mixes the sibling
in on the mirror side, and reconstructs an identical root. Round-trip proofs
therefore stay green under an inverted convention. Asymmetric shapes do notice. -/
theorem routeRight_eq_div_mod (index i : Nat) :
    routeRight index i = (index / 2 ^ i % 2 == 1) := by
  show ((index >>> i) &&& 1 == 1) = (index / 2 ^ i % 2 == 1)
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

end EthCLLib.Spec
