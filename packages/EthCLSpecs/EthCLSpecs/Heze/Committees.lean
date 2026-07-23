import EthCLSpecs.Fulu.Constants

/-!
# `EthCLSpecs.Heze.Committees`: the FOCIL inclusion-list committee resampling helper

EIP-7805 (FOCIL) adds one beacon-state accessor, `get_inclusion_list_committee`
(`consensus-specs/specs/heze/beacon-chain.md:95-110`), which samples a fixed-size committee from the
slot's beacon committees. That accessor lives in `Heze/ForkChoice.lean`, next to its sole caller
`get_inclusion_list_transactions`: it throws the fork-choice reject on the spec's degenerate
empty-committee read (`indices[i % 0]` raises `ZeroDivisionError`), so it belongs in the
store-throwing monad rather than among the pure state accessors. This file holds the one piece
factored out of it: `cyclicSample`, the wrap-around index fill, kept here so its arithmetic is
unit-checkable by the `#guard`s below without building a whole `BeaconState`.
-/

set_option autoImplicit false

open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

/-- The cyclic resampling `get_inclusion_list_committee` uses to fill its fixed-length
result: element `i` is `xs[i % xs.size]`, wrapping back to the front once `i` passes the end
of the concatenated committees (the spec's `indices[i % len(indices)]`,
`consensus-specs/specs/heze/beacon-chain.md:108-110`). Factored out of the accessor so the
wrap-around index arithmetic is unit-checkable below without building a whole `BeaconState`.
`xs.getD … default` is total via `[Inhabited α]`; the sole caller (`getInclusionListCommittee`
in `Heze/ForkChoice.lean`) asserts `indices.size != 0` before reaching here, so on every path
`xs` is non-empty, `i % xs.size < xs.size`, and `getD` always returns a real element. -/
def cyclicSample {α : Type} [Inhabited α] (xs : Array α) (n : Nat) : Vector α n :=
  Vector.ofFn (fun i : Fin n => xs.getD (i.val % xs.size) default)

-- Pins for the cyclic resampling, expected values computed by hand from the Python
-- comprehension `[indices[i % len(indices)] for i in range(n)]`. First: a size-3 source over
-- n = 8 wraps as i % 3 = 0,1,2,0,1,2,0,1. Second: a size-2 source over the real
-- `INCLUSION_LIST_COMMITTEE_SIZE` (= 16) alternates 0,1,…; the 16-element result also pins
-- the constant, since a different size would change the list length and fail the `=`.
#guard (cyclicSample (#[10, 20, 30] : Array UInt64) 8).toList
  = [10, 20, 30, 10, 20, 30, 10, 20]
#guard (cyclicSample (#[7, 8] : Array UInt64) Const.inclusionListCommitteeSize).toList
  = [7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8]

end EthCLSpecs.Heze
