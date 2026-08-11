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
unit-checkable without building a whole `BeaconState`. The `#guard`s that check it live in
`EthCLSpecs.Tests.HezeCommitteesPins`.
-/

set_option autoImplicit false

open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

/-- The cyclic resampling `get_inclusion_list_committee` uses to fill its fixed-length
result: element `i` is `xs[i % xs.size]`, wrapping back to the front once `i` passes the end
of the concatenated committees (the spec's `indices[i % len(indices)]`,
`consensus-specs/specs/heze/beacon-chain.md:108-110`). Factored out of the accessor so the
wrap-around index arithmetic is unit-checkable without building a whole `BeaconState`
(`EthCLSpecs.Tests.HezeCommitteesPins`).
`xs.getD … default` is total via `[Inhabited α]`; the sole caller (`getInclusionListCommittee`
in `Heze/ForkChoice.lean`) rejects an empty committee before reaching here, so on every path
`xs` is non-empty, `i % xs.size < xs.size`, and `getD` always returns a real element. That
guard is an `.arithmetic` throw, not an `assert`: the spec's `i % len(indices)` raises
`ZeroDivisionError` on an empty committee, an uncaught fault the reference runner propagates
rather than catching, so it can never be a vector's expected rejection. -/
def cyclicSample {α : Type} [Inhabited α] (xs : Array α) (n : Nat) : Vector α n :=
  Vector.ofFn (fun i : Fin n => xs.getD (i.val % xs.size) default)

end EthCLSpecs.Heze
