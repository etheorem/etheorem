import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.Focil`: the EIP-7805 (FOCIL) beacon-chain helpers

The two helpers Heze's `beacon-chain.md` adds for fork-choice-enforced inclusion lists.
`get_inclusion_list_committee` (the "Beacon state accessors" section,
`consensus-specs/specs/heze/beacon-chain.md:95-110`) samples a fixed-size committee from the
slot's beacon committees; `is_valid_inclusion_list_signature` (the "Predicates" section,
`consensus-specs/specs/heze/beacon-chain.md:76-87`) checks a `SignedInclusionList`'s BLS
signature under `DOMAIN_INCLUSION_LIST_COMMITTEE`. Both lean on accessors inherited verbatim
over `Heze.State` in `EpochProcessing` (`getBeaconCommittee`, `getCommitteeCountPerSlot`,
`getDomain`, `computeEpochAtSlot`). FOCIL adds no state transition, so these are a pure
accessor and a predicate rather than transition steps.

`get_inclusion_list_committee` is reached from the `on_execution_payload_envelope` vectors (via
`get_inclusion_list_transactions`) but against an empty store; `is_valid_inclusion_list_signature`
has no caller or vector. So the Python is the oracle for both. Each helper mirrors it
branch-for-branch, and the build-enforced `#guard`s below pin the load-bearing cyclic
resampling to values worked out by hand from the spec's list comprehension. `blsVerify` is
the residual trust boundary (the `[CryptoBackend]` seam), as for every other signature
predicate; no pure assertion pins it.
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

state_section

/-- `get_inclusion_list_committee(state, slot)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:95-110`): concatenate every beacon committee for
`slot` in committee-index order, then take the first `INCLUSION_LIST_COMMITTEE_SIZE` members
cyclically. Mirrors the Python branch-for-branch: `epoch = compute_epoch_at_slot(slot)`, the
`range(committees_per_slot)` accumulation that `extend`s each `get_beacon_committee`, and the
`indices[i % len(indices)]` `Vector` fill (here `cyclicSample`). `get_beacon_committee` takes
a `Nat` committee index in this framework, so the loop counter `i` is passed directly; the
Python `CommitteeIndex(i)` wrapper is the same value. The degenerate empty-committee case the
Python would hit with a `ZeroDivisionError` (`len(indices) == 0`) is instead a total read here
(`i % 0 = i`, default element), a state a real beacon chain never reaches. -/
forkdef getInclusionListCommittee (state : State) (slot : Slot) :
    Vector ValidatorIndex Const.inclusionListCommitteeSize :=
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let indices := (Array.range committeesPerSlot).foldl
    (fun acc i => acc ++ getBeaconCommittee state slot i) (#[] : Array ValidatorIndex)
  cyclicSample indices Const.inclusionListCommitteeSize

/-- `is_valid_inclusion_list_signature(state, signed_inclusion_list)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:76-87`): the `InclusionList` carries a valid BLS
signature by its committee member's key under `DOMAIN_INCLUSION_LIST_COMMITTEE` at the
message's epoch. Mirrors the Python step-for-step: read `message`, the validator `pubkey` at
`validator_index`, the domain, `compute_signing_root(message, domain)`, then `bls.Verify`.
`blsVerify` is the residual trust boundary (the `[CryptoBackend]` seam): no pure assertion
pins it, the same treatment Gloas gives `verify_execution_payload_bid_signature` and the
builder-deposit signature predicate. It has no in-model caller by design. The spec's sole
consumer is the p2p `inclusion_list` gossip `[REJECT]` (`p2p-interface.md:100`), and EthCLSpecs
models the state-transition and fork-choice layers, not p2p gossip (`networking` is out of the
conformance scope). `on_inclusion_list` carries no signature check of its own
(`fork-choice.md:256-267`), so the fork-choice path mirrors the spec faithfully. Kept as the
beacon-chain surface for spec-completeness. -/
forkdef isValidInclusionListSignature (state : State) (signed : SignedInclusionList) : Bool :=
  let message := signed.message
  let index := message.validatorIndex
  let vs := sszGet state validators
  -- `validator_index` arrives off the wire, so bound it: the spec's `state.validators[index]`
  -- raises `IndexError` for an out-of-range index, rejecting the list. Reject explicitly rather
  -- than reading the `Inhabited` default (zero-pubkey) validator through `[…]!`.
  if index.toNat < vs.size then
    let pubkey := (vs[index.toNat]!).pubkey
    let domain := getDomain state Const.domainInclusionListCommittee (computeEpochAtSlot message.slot)
    blsVerifySigned pubkey message domain signed.signature
  else
    false

end

end EthCLSpecs.Heze
