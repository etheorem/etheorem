import EthCLSpecs.Heze.EpochProcessing

/-!
# `EthCLSpecs.Heze.Committees`: the EIP-7805 (FOCIL) inclusion-list committee accessor

Heze inherits `Committees` from Fulu verbatim; this file adds the one new committee accessor
EIP-7805 (FOCIL) introduces. `get_inclusion_list_committee` (the "Beacon state accessors" section,
`consensus-specs/specs/heze/beacon-chain.md:95-110`) samples a fixed-size committee from the
slot's beacon committees. It leans on accessors inherited over `Heze.State` in `EpochProcessing`
(`getBeaconCommittee`, `getCommitteeCountPerSlot`, `computeEpochAtSlot`). FOCIL adds no state
transition, so this is a pure accessor rather than a transition step.

`get_inclusion_list_committee` is reached from the `on_execution_payload_envelope` vectors (via
`get_inclusion_list_transactions`) but against an empty store, so the Python is the oracle. The
accessor mirrors it branch-for-branch, and the build-enforced `#guard`s below pin the load-bearing
cyclic resampling to values worked out by hand from the spec's list comprehension.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

/-- The cyclic resampling `get_inclusion_list_committee` uses to fill its fixed-length
result: element `i` is `xs[i % xs.size]`, wrapping back to the front once `i` passes the end
of the concatenated committees (the spec's `indices[i % len(indices)]`,
`consensus-specs/specs/heze/beacon-chain.md:108-110`). Factored out of the accessor so the
wrap-around index arithmetic is unit-checkable below without building a whole `BeaconState`.
`xs.getD … default` is total via `[Inhabited α]`; on the spec path `xs` is the non-empty committee
concatenation, so `i % xs.size < xs.size` and `getD` always returns a real element. The `default`
fallback covers only the unreachable empty-`xs` case (a state a real beacon chain never reaches),
which `getD` returns silently rather than panicking to stderr as `xs[…]!` would. -/
private def cyclicSample {α : Type} [Inhabited α] (xs : Array α) (n : Nat) : Vector α n :=
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

-- `state_section` is the framework's header macro (`SPEC_AUTHORING_MODEL.md` §4): it opens
-- the section and emits the `variable` line, `[Preset]` / `[Config]` / `[HasherTag]` /
-- `[CryptoBackend]` plus the `StateTransition` monad variable and its constraints, which the
-- `forkdef`s below take implicitly (`EthCLLib.Spec.Header`).
state_section

/-- `get_inclusion_list_committee(state, slot)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:95-110`): concatenate every beacon committee for
`slot` in committee-index order, then take the first `INCLUSION_LIST_COMMITTEE_SIZE` members
cyclically. Mirrors the Python branch-for-branch: `epoch = compute_epoch_at_slot(slot)`, the
`range(committees_per_slot)` accumulation that `extend`s each `get_beacon_committee`, and the
`indices[i % len(indices)]` `Vector` fill (here `cyclicSample`). `get_beacon_committee` takes
a `Nat` committee index in this framework, so the loop counter `i` is passed directly; the
Python `CommitteeIndex(i)` wrapper is the same value. The degenerate empty-committee read is
total here where the Python would raise; `cyclicSample` above carries the mechanics. -/
forkdef getInclusionListCommittee (state : State) (slot : Slot) :
    Vector ValidatorIndex Const.inclusionListCommitteeSize :=
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let indices := (Array.range committeesPerSlot).foldl
    (fun acc i => acc ++ getBeaconCommittee state slot i) (#[] : Array ValidatorIndex)
  cyclicSample indices Const.inclusionListCommitteeSize

end

end EthCLSpecs.Heze
