import EthCLSpecs.Heze.Constants

/-!
# `EthCLSpecs.Heze.Committees`: the FOCIL inclusion-list committee resampling helper

EIP-7805 (FOCIL) adds one beacon-state accessor, `get_inclusion_list_committee`
(`consensus-specs/specs/heze/beacon-chain.md:264-277`), which samples a fixed-size committee from the
slot's beacon committees. That accessor lives in `Heze/ForkChoice.lean`, next to its sole caller
`get_inclusion_list_transactions`: it throws the fork-choice reject on the spec's degenerate
empty-committee read (`indices[i % 0]` raises `ZeroDivisionError`), so it belongs in the
store-throwing monad. This file holds the one piece
factored out of it: `cyclicSample`, the wrap-around index fill, kept here so its arithmetic is
unit-checkable without building a whole `BeaconState`. The `#guard`s that check it live in
`EthCLSpecs.Tests.HezeCommitteesPins`.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

/-- The cyclic resampling `get_inclusion_list_committee` uses to fill its fixed-length
result: `[indices[index % len(indices)] for index in range(n)]`
(`consensus-specs/specs/heze/beacon-chain.md:274-276`), wrapping back to the front once
`index` passes the end of the concatenated committees. Factored out of the accessor so the
wrap-around index arithmetic is unit-checkable without building a whole `BeaconState`
(`EthCLSpecs.Tests.HezeCommitteesPins`).

`index` and `len(indices)` are plain `int`s, so the position is the plain kind's `%`
(`SPEC_ARITHMETIC.md` §4.2). On an empty `xs` the first position raises `ZeroDivisionError`,
the `.zeroDivision` cause, which no reference wrapper catches. With `n = 0` the comprehension
is empty and nothing raises. The read `indices[position]` goes through `getAt`, which raises
`IndexError` where Python does; after a nonzero `%` the position is in range, so the read
cannot reject. The positions form in ascending order, so the first fault is Python's. -/
def cyclicSample {α : Type} (xs : Array α) (n : Nat) :
    Except StateTransitionError (Vector α n) :=
  Vector.ofFnM fun i : Fin n => do
    let position ← ((i.val : CLInt) % len xs : Checked CLInt)
    liftErr (getAt xs position)

end EthCLSpecs.Heze
