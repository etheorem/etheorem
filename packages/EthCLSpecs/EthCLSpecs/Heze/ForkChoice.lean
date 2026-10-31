import EthCLSpecs.Heze.Transition
import EthCLSpecs.Heze.Committees
import EthCLSpecs.Heze.Signing
import EthCLLib.Spec.FiniteMap
import EthCLLib.Spec.Engine

/-!
# `EthCLSpecs.Heze.ForkChoice`: the ePBS node-based fork choice with EIP-7805 (FOCIL)

Heze inherits the whole node-based fork choice of Gloas's ePBS (EIP-7732) and adds the
EIP-7805 FOCIL layer on top (`consensus-specs/specs/heze/fork-choice.md`). `ForkChoiceNode` /
`LatestMessage` are `inherit`ed unchanged (`inherit` replays an ancestor fork's captured
declaration in this namespace; the inheritance mechanism is `SPEC_AUTHORING_MODEL.md` §8).
The three node smart constructors and the `deriving` lines are plain declarations in Gloas,
which the capture does not cover, so they are restated here. The `Store` is re-declared as a
fresh `forkstruct` (the framework's fork-aware `structure` form, capturable for a later
fork's `inherit`) instead of an `inherit`, to carry the two `[New in Heze:EIP7805]` fields:
`payloadInclusionListSatisfaction` and the folded-in `inclusionListStore`. The spec keeps a
separate process-lifetime `InclusionListStore`; this framework's fork choice threads one
`Store` value through the generic `StoreTransition` monad, so the inclusion-list store is
folded into it (the `InclusionListStore` declaration below carries the full rationale). Most
handlers are inherited verbatim; the FOCIL touch points are re-declared here:

* `get_forkchoice_store` seeds the two new store fields empty;
* `is_payload_inclusion_list_satisfied` / `record_payload_inclusion_list_satisfaction` /
  `get_inclusion_list_due_ms` / `is_inclusion_list_satisfied` are the new helpers;
* `should_extend_payload` gains the inclusion-list gate;
* `on_execution_payload_envelope` records satisfaction before storing the payload;
* `on_inclusion_list` is the new wire handler.

The inclusion-list store and its helpers (`consensus-specs/specs/heze/inclusion-list.md`) sit
here too: `process_inclusion_list`, `get_inclusion_list_transactions`, `get_inclusion_list_bits`,
and `is_inclusion_list_bits_inclusive`, keyed by `(slot, dependent_root)` at v1.7.0-beta.4.

EIP-7805 also extends `PayloadAttributes` with `inclusion_list_transactions` and threads it
through `notify_forkchoice_updated` (`heze/fork-choice.md:77-84`). Both belong to the
production-side Engine-API surface, the calls a proposer drives to build its own payload.
That surface sits outside the modeled state-transition and fork-choice scope, the boundary
every fork keeps, so both stay unmodeled here. Only the consumption side is modeled:
`is_inclusion_list_satisfied`, through the `[ExecutionEngine]` seam (one of the injection
seams, `FRAMEWORK_ARCHITECTURE.md` §1; defined in `EthCLLib.Spec.Engine`) that
`record_payload_inclusion_list_satisfaction` calls to judge a revealed payload.

Vector coverage is partial, and the split matters. The `on_execution_payload_envelope`
fork_choice vectors do drive `onExecutionPayloadEnvelope` and `shouldExtendPayload`, but only
on the empty-inclusion-list, always-satisfied path they share with Gloas. The FOCIL-specific
behavior (the discriminating satisfaction gate and `on_inclusion_list`) has no vector; the
pinned spec text (`consensus-specs` at tag `v1.7.0-beta.4`) is its oracle
(`IMPLEMENTATION_NOTES.md`, "Heze diff", is the catalogue). Each override mirrors its Python
branch-for-branch, and the build-enforced pins fix the inclusion-list logic's expected
outcomes at build time: kernel `#guard`s where the outcome is hash-free, `native_decide`
examples where a hash-tree-root must be computed. Those live in
`EthCLSpecs.Tests.HezeForkChoicePins`, not here, so the shipped fork body carries none of
their evaluation.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Heze

inherit ForkChoiceNode
deriving instance BEq, Inhabited for ForkChoiceNode

inherit LatestMessage
deriving instance Inhabited for LatestMessage

/-- `InclusionListEntry` (`consensus-specs/specs/heze/inclusion-list.md:33-35`, new at
v1.7.0-beta.4): a stored signed inclusion list and whether it arrived before the
`INCLUSION_LIST_DUE_BPS` deadline in its own slot. -/
forkstruct InclusionListEntry where
  signedInclusionList : SignedInclusionList
  timely              : Bool

/-- `InclusionListStore` (`consensus-specs/specs/heze/inclusion-list.md:42-44`): the
fork-choice node's view of the inclusion lists it has seen. The two fields, both keyed by
`(slot, dependent_root)`, the slot and the shuffling dependent root its committee was drawn
under:

* `inclusionLists`: the stored entries, one per validator (the spec's
  `defaultdict[tuple[Slot, Root], dict[ValidatorIndex, InclusionListEntry]]`);
* `equivocators`: the validators caught publishing two different lists for the key.

v1.7.0-beta.4 keys by `(slot, dependent_root)` and stores one entry per validator, with its
timeliness inside the entry. alpha.12 keyed by the committee's root, stored lists by their own
root, and kept the timeliness in a separate map.

A `forkstruct` rather than a bare `structure`, so a later fork can `inherit` it, and so it
carries the auto `[Preset]` / `[HasherTag]` uniformly with the containers it nests.

This declaration is the canonical home of the fold-in rationale. The spec keeps
`InclusionListStore` as a process-lifetime singleton reached through
`get_inclusion_list_store()`. This framework's fork choice threads one `Store` value through
the generic `StoreTransition` monad (`SPEC_AUTHORING_MODEL.md` §4), with no ambient mutable
singleton to hang the spec's store off, so the store is modeled as a `Store` field instead
and moves with the rest of the state. Behavior is identical. It is fork-choice state, so it
lives here, next to the handlers that drive it. -/
forkstruct InclusionListStore (map : MapKind) [HasherTag] where
  inclusionLists : map (Slot × Root) (map ValidatorIndex InclusionListEntry)
  equivocators   : map (Slot × Root) (Array ValidatorIndex)

section

variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

-- The store-transition monad, minus `MonadStateOf`: the committee helper below threads the
-- state explicitly rather than through `get`, so it needs only `Monad` plus the store reject
-- to throw. Leaving `MonadStateOf` off lets the vectorless pins run it in plain
-- `Except StoreTransitionError`, with no dummy `Store` to `.run` over. A concrete fork-choice
-- monad (the one `fork_choice_section` opens below) still satisfies these two, so the store
-- handlers bind it with `←` unchanged.
variable {StoreTransition : Type → Type} [Monad StoreTransition]
variable [MonadExceptOf StoreTransitionError StoreTransition]

/-- The empty `InclusionListStore`: no stored lists, no equivocators. `getForkchoiceStore`
seeds the folded-in `Store` field with it. The spec has no counterpart line: there the store
is the lazily-created `get_inclusion_list_store()` singleton (see the `InclusionListStore`
docstring above for the fold-in). Every pin below also builds from it, so the all-empty
literal lives in one place. -/
def InclusionListStore.empty : InclusionListStore map :=
  { inclusionLists := FcMap.empty, equivocators := FcMap.empty }

/-- `process_inclusion_list(store, signed_inclusion_list, timely)`
(`consensus-specs/specs/heze/inclusion-list.md:64-85`): file a newly received inclusion list,
or record an equivocation. Pure here (returns the updated `InclusionListStore`); the spec
mutates in place. The two branches mirror the Python:

* the validator already has an entry for this key → if its stored list differs from the new
  one, add the validator to `equivocators[key]` (a set, so a repeat adds nothing); either way
  the list is ignored;
* otherwise → store the signed list and its timeliness under `(key, validator_index)`.

The spec's `defaultdict` reads create an empty entry on a miss. Nothing observes that entry
(every read of a missing key gets the same empty value), so the lookups default instead. -/
forkdef processInclusionList (store : InclusionListStore map) (signed : SignedInclusionList)
    (timely : Bool) : InclusionListStore map :=
  let inclusionList := signed.message
  let validatorIndex := inclusionList.validatorIndex
  let key := (inclusionList.slot, inclusionList.dependentRoot)
  let entries := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
  match FcMap.lookup entries validatorIndex with
  | some storedEntry =>
    -- Mark the validator as an equivocator if it published a different inclusion list.
    let equivs := FcMap.lookupD store.equivocators key
    if storedEntry.signedInclusionList.message != inclusionList && !equivs.contains validatorIndex then
      { store with equivocators := FcMap.insert store.equivocators key (equivs.push validatorIndex) }
    else store
  | none =>
    -- Store the signed inclusion list and its timeliness.
    let entry : InclusionListEntry := { signedInclusionList := signed, timely }
    { store with inclusionLists := FcMap.insert store.inclusionLists key (FcMap.insert entries validatorIndex entry) }

/-- The stored entries for one key, as `(validator_index, entry)` pairs: the spec's
`inclusion_lists[key].items()`. The map's fold order stands in for the dict's insertion order;
no caller depends on it (`get_inclusion_list_transactions` deduplicates into a set, and
`get_inclusion_list_bits` tests membership). A miss is the `defaultdict`'s empty dict. -/
def inclusionListItems (store : InclusionListStore map) (slot : Slot) (dependentRoot : Root) :
    Array (ValidatorIndex × InclusionListEntry) :=
  FcMap.fold (fun acc validatorIndex entry => acc.push (validatorIndex, entry)) #[]
    ((FcMap.lookup store.inclusionLists (slot, dependentRoot)).getD FcMap.empty)

/-- Whether an item counts toward `get_inclusion_list_transactions` / `get_inclusion_list_bits`:
its validator is not an equivocator for the key, and, when only timely lists count, its list
arrived on time. Both spec loops skip an item on exactly these two `continue`s. -/
def isCountedInclusionList (equivocators : Array ValidatorIndex) (onlyTimely : Bool)
    (item : ValidatorIndex × InclusionListEntry) : Bool :=
  !equivocators.contains item.1 && (!onlyTimely || item.2.timely)

/-- The items both spec loops keep for one key: `inclusionListItems` filtered by
`isCountedInclusionList` against the key's equivocators. Stated once, since
`get_inclusion_list_transactions` and `get_inclusion_list_bits` run the same filter. -/
def countedInclusionLists (store : InclusionListStore map) (slot : Slot) (dependentRoot : Root)
    (onlyTimely : Bool) : Array (ValidatorIndex × InclusionListEntry) :=
  let equivocators := FcMap.lookupD store.equivocators (slot, dependentRoot)
  (inclusionListItems store slot dependentRoot).filter (isCountedInclusionList equivocators onlyTimely)

/-- `get_inclusion_list_transactions(store, slot, dependent_root, only_timely=True)`
(`consensus-specs/specs/heze/inclusion-list.md:101-121`): the unique transactions from every
non-equivocating inclusion list stored for `(slot, dependent_root)`, optionally restricted to
the timely ones. Pure: at v1.7.0-beta.4 each entry carries its own timeliness, so the alpha.12
raising timeliness read is gone. The counted lists' transactions are concatenated in item
order (the spec's `transactions.extend(...)`), then deduplicated. The dedup keeps each
transaction's first occurrence (`arrayUnion`): the spec's `list(set(transactions))` keeps each
transaction once and calls the order irrelevant, so a deterministic representative lets
`#guard` pin the result. -/
forkdef getInclusionListTransactions (store : InclusionListStore map) (slot : Slot)
    (dependentRoot : Root) (onlyTimely : Bool := true) : Array Transaction :=
  let transactions := (countedInclusionLists store slot dependentRoot onlyTimely).flatMap
    (fun item => item.2.signedInclusionList.message.transactions.toArray)
  arrayUnion #[] transactions

/-- `get_inclusion_list_bits(store, committee, slot, dependent_root, only_timely=True)`
(`consensus-specs/specs/heze/inclusion-list.md:127-150`): a bit per committee member, set when
that member has a counted inclusion list for `(slot, dependent_root)`. The proposer and builder
duties call it to fill `inclusion_list_bits`; no modeled path does. Pure. -/
forkdef getInclusionListBits (store : InclusionListStore map)
    (committee : Vector ValidatorIndex Const.inclusionListCommitteeSize) (slot : Slot)
    (dependentRoot : Root) (onlyTimely : Bool := true) :
    Bitvector Const.inclusionListCommitteeSize :=
  let validatorIndices := (countedInclusionLists store slot dependentRoot onlyTimely).map (·.1)
  (List.range Const.inclusionListCommitteeSize).foldl
    (fun bits i => bitSet bits i (validatorIndices.contains (vget committee i))) default

/-- `is_inclusion_list_bits_inclusive(store, committee, slot, dependent_root,
inclusion_list_bits, only_timely=True)` (`consensus-specs/specs/heze/inclusion-list.md:156-171`):
whether `inclusionListBits` sets every bit the local view sets, that is, the bits are a
superset of `get_inclusion_list_bits`. The p2p bid rules call it; no modeled path does. Pure. -/
forkdef isInclusionListBitsInclusive (store : InclusionListStore map)
    (committee : Vector ValidatorIndex Const.inclusionListCommitteeSize) (slot : Slot)
    (dependentRoot : Root) (inclusionListBits : Bitvector Const.inclusionListCommitteeSize)
    (onlyTimely : Bool := true) : Bool :=
  let localInclusionListBits := getInclusionListBits store committee slot dependentRoot onlyTimely
  (List.range Const.inclusionListCommitteeSize).all fun i =>
    !(bitGet localInclusionListBits i && !bitGet inclusionListBits i)

/-- `get_inclusion_list_committee(state, slot)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:264-277`): concatenate every beacon committee for
`slot` in committee-index order, then take the first `INCLUSION_LIST_COMMITTEE_SIZE` members
cyclically (`cyclicSample`, in `Heze/Committees.lean`). Relocated from the beacon-state accessors
into this store-throwing block beside its caller `on_inclusion_list`: the spec's
`indices[i % len(indices)]` raises `ZeroDivisionError` when the slot has no committee members.
That is an uncaught fault (the reference runner catches only `AssertionError` / `IndexError`), so
the empty case throws `.transition (.arithmetic …)` (an `uncaughtFault`, not an expected rejection)
rather than a caught `.assert`, matching how `balanceAfterWithdrawals` models the sibling `uint64`
fault, and rather than silently sampling a `default`. `state` stays an explicit parameter (the
accessor reads `state`, not the store). -/
forkdef getInclusionListCommittee (state : State) (slot : Slot) :
    StoreTransition (Vector ValidatorIndex Const.inclusionListCommitteeSize) := do
  let epoch := computeEpochAtSlot slot
  let committeesPerSlot := getCommitteeCountPerSlot state epoch
  let indices := (Array.range committeesPerSlot).foldl
    (fun acc i => acc ++ getBeaconCommittee state slot i) (#[] : Array ValidatorIndex)
  if indices.size == 0 then
    throwArithmetic "get_inclusion_list_committee: indices[i % len(indices)] on an empty committee"
  pure (cyclicSample indices Const.inclusionListCommitteeSize)

end

/-- The Heze fork-choice store: the Gloas store plus the EIP-7805 fields. Re-declared as a
`forkstruct` rather than an `inherit Store`, so the two `[New in Heze:EIP7805]` fields can be added.
`payloadInclusionListSatisfaction` tracks, per beacon-block root, whether the revealed payload
satisfied the inclusion-list constraints (`consensus-specs/specs/heze/fork-choice.md:133`);
`inclusionListStore` folds in the spec's separate `InclusionListStore` (see the module docstring).
The seventeen Gloas fields are restated verbatim. -/
forkstruct Store (map : MapKind) [HasherTag] where
  timeMs                        : UInt64
  genesisTimeMs                 : UInt64
  justifiedCheckpoint           : Checkpoint
  finalizedCheckpoint           : Checkpoint
  unrealizedJustifiedCheckpoint : Checkpoint
  unrealizedFinalizedCheckpoint : Checkpoint
  proposerBoostRoot             : Root
  equivocatingIndices           : Array ValidatorIndex
  blocks                        : map Root BeaconBlock
  blockStates                   : map Root State
  blockTimeliness               : map Root (Array Bool)
  checkpointStates              : map Checkpoint State
  latestMessages                : map ValidatorIndex LatestMessage
  unrealizedJustifications      : map Root Checkpoint
  payloads                      : map Root ExecutionPayloadEnvelope
  payloadTimelinessVote         : map Root (Array (Option Bool))
  payloadDataAvailabilityVote   : map Root (Array (Option Bool))
  -- [New in Heze:EIP7805] (consensus-specs/specs/heze/fork-choice.md:133)
  payloadInclusionListSatisfaction : map Root Bool
  -- [New in Heze:EIP7805] the spec's standalone `InclusionListStore`, folded in here as a field
  inclusionListStore            : InclusionListStore map

fork_choice_section map

/-- A PENDING node at `root`: the undecided block, before either payload realisation is
committed. -/
def ForkChoiceNode.pending (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusPending }

/-- An EMPTY node at `root`: the realisation in which the block's payload is absent. -/
def ForkChoiceNode.empty (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusEmpty }

/-- A FULL node at `root`: the realisation in which the block's payload is present. -/
def ForkChoiceNode.full (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusFull }

inherit fcZeroRoot
inherit getSlotsSinceGenesis
inherit getCurrentSlot
inherit getCurrentStoreEpoch
inherit getTimeIntoSlotMs
inherit bpsDeadlineMs
inherit getParentPayloadStatus
inherit isParentNodeFull
inherit getAncestor
inherit isAncestor
inherit getCheckpointBlock
inherit getSupportedNode
inherit computeShufflingLookaheadStartSlot computeShufflingDependentSlot
inherit getShufflingDependentRoot
inherit isPayloadVerified
inherit voteCount
inherit payloadTimeliness
inherit payloadDataAvailability
inherit isPreviousSlotPayloadDecision

/-- `is_payload_inclusion_list_satisfied(store, root)`
(`consensus-specs/specs/heze/fork-choice.md:207-220`): whether the payload for `root`
satisfied the inclusion-list constraints and is locally available. The spec opens with
`assert root in store.payload_inclusion_list_satisfaction`; the predicate throws that `assert`
on a missing key (`StoreTransition Bool`), matching the spec's reject. The assert is unreachable
on the spec path, because `onExecutionPayloadEnvelope` always writes `payloads` and the
satisfaction entry together; the INVARIANT note there is the canonical statement of that
argument. -/
forkdef isPayloadInclusionListSatisfied (store : Store map) (root : Root) : StoreTransition Bool := do
  -- The spec opens with `assert root in store.payload_inclusion_list_satisfaction`; that fires
  -- (rejecting) even when the payload is unverified, so it precedes the verified check. The
  -- later `[root]` read is then over a present key, so assert and read fuse into one
  -- `getOrAssert` (an `.assert` reject on a miss).
  let satisfied ← FcMap.getOrAssert store.payloadInclusionListSatisfaction root
    "root in store.payload_inclusion_list_satisfaction"
  if !isPayloadVerified store root then pure false
  else pure satisfied

/-- `should_extend_payload(store, root)` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:229-244`): the Gloas body with the one new
inclusion-list gate. After the `is_payload_verified` check, a payload that fails the
inclusion-list constraints is not extended (`heze/fork-choice.md:234-235`). The rest is Gloas verbatim.
-/
forkdef shouldExtendPayload (store : Store map) (root : Root) : StoreTransition Bool := do
  -- Mirrors the Gloas body plus the inclusion-list gate: the spec opens with
  -- `assert store.blocks[root].slot + 1 == get_current_slot(store)`.
  let rootBlock ← FcMap.getOrThrow store.blocks root
  let currentSlot ← getCurrentSlot store
  let nextSlot ← checkedAdd rootBlock.slot 1 "should_extend_payload: blocks[root].slot + 1"
  assert (nextSlot == currentSlot)
  if !isPayloadVerified store root then pure false
  -- [New in Heze:EIP7805] do not extend a payload that fails the inclusion-list constraints
  else if !(← isPayloadInclusionListSatisfied store root) then pure false
  else
    let proposerRoot := store.proposerBoostRoot
    let payloadIsTimely ← payloadTimeliness store root true
    let payloadDataIsAvailable ← payloadDataAvailability store root true
    if (payloadIsTimely && payloadDataIsAvailable) || proposerRoot == fcZeroRoot then
      pure true
    else
      let pb ← FcMap.getOrThrow store.blocks proposerRoot
      -- Python's final `or` short-circuits: `is_parent_node_full` (whose
      -- `store.blocks[pb.parent_root]` read throws) never runs when
      -- `pb.parent_root != root` already decides the disjunction (Gloas parity).
      if pb.parentRoot != root then pure true
      else isParentNodeFull store pb

inherit getPayloadStatusTiebreaker
inherit calculateCommitteeFraction computeProposerScore
inherit getProposerScore
inherit getAttestationScore
inherit isHeadWeak
inherit isParentStrong
inherit shouldApplyProposerBoost
inherit getWeight
inherit getVotingSource
inherit getNodeChildren
inherit filterNodeTree
inherit getFilteredNodeTree
inherit getHead
inherit isValidDependentRoot
inherit updateCheckpoints
inherit updateUnrealizedCheckpoints
inherit computePulledUpTip
inherit onTickPerSlot
inherit onTick
inherit recordBlockTimeliness
inherit updateProposerBoostRoot
inherit recordPtcVotes
inherit onPayloadAttestationMessage
inherit notifyPtcMessages
inherit onBlock

-- Three answers on this fork's paths belong to something outside the vector: the EL's
-- `is_inclusion_list_satisfied` (`heze/fork-choice.md:54-62`) and
-- `verify_and_notify_new_payload`, plus `is_data_available`'s sidecar retrieval. All three
-- enter through the framework seams in `EthCLLib.Spec.Engine`, which is where the
-- optimistic-mock rationale lives, instantiated at Heze's payload / transaction / request
-- types. Scoped to the declarations that need them; at file scope the binders would ride on
-- every later declaration, most of which never reach the execution layer.
section EngineSeam
variable [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] [DataAvailability]

-- Inherited inside the section: Gloas's bodies read the seams, so the replay needs the same
-- binders in scope that the originals were written under.
inherit verifyAndNotifyNewPayload
inherit isDataAvailable
inherit verifyExecutionPayloadEnvelope

/-- `is_inclusion_list_satisfied(execution_payload, inclusion_list_transactions)`
(`consensus-specs/specs/heze/fork-choice.md:54-62`): the `ExecutionEngine` predicate deciding
whether a payload includes the required inclusion-list transactions. Its answer is
EL-implementation-defined (the Engine API answers it against an external EL), so it reads the
`[ExecutionEngine]` seam rather than a fixed value; the default and the trust boundary are
documented on `EthCLLib.Spec.ExecutionEngine`. -/
forkdef isInclusionListSatisfied (payload : ExecutionPayload) (ilTxs : Array Transaction) : Bool :=
  -- Named type arguments: the class parameters are implicit on the projection, and `Requests`
  -- appears in no argument of this method, so it cannot be recovered from the call.
  ExecutionEngine.isInclusionListSatisfied (Payload := ExecutionPayload) (Tx := Transaction)
    (Requests := ExecutionRequests) payload ilTxs

/-- `record_payload_inclusion_list_satisfaction(store, root, payload, execution_engine)`
(`consensus-specs/specs/heze/fork-choice.md:187-201`): record whether `payload` satisfies the
inclusion-list constraints for `root`. Pure here (returns the updated store); the spec mutates
in place. The required transactions are the timely ones stored for the previous slot
(`store.blocks[root].slot - 1`) under the shuffling dependent root `root`'s chain fixes for that
slot's epoch. `get_inclusion_list_store()` is `store.inclusionListStore`, and the EL answer comes
from `isInclusionListSatisfied`, which reads the `[ExecutionEngine]` seam (the spec's
`execution_engine` argument, modeled injectably).

v1.7.0-beta.4 drops the `state` argument: the slot comes from the block in the store and the
committee key from the dependent root, where alpha.12 recomputed the committee from the state.
Throwing: `store.blocks[root]` raises on a miss, the `slot - 1` is a `uint64` subtraction that
raises on a slot-0 block (an uncaught fault, so `checkedSub`), and the dependent-root walk
reads the store. -/
forkdef recordPayloadInclusionListSatisfaction (store : Store map) (root : Root)
    (payload : ExecutionPayload) : StoreTransition (Store map) := do
  let block ← FcMap.getOrThrow store.blocks root
  let slot ← checkedSub block.slot 1 "record_payload_inclusion_list_satisfaction: store.blocks[root].slot - 1"
  let dependentRoot ← getShufflingDependentRoot store root (computeEpochAtSlot slot)
  let ilTxs := getInclusionListTransactions store.inclusionListStore slot dependentRoot (onlyTimely := true)
  let satisfied := isInclusionListSatisfied payload ilTxs
  pure { store with
      payloadInclusionListSatisfaction := FcMap.insert store.payloadInclusionListSatisfaction root satisfied }

/-- `on_execution_payload_envelope` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:317-344`): the Gloas body with one added step,
`record_payload_inclusion_list_satisfaction` is called on the verified envelope *before* the
payload is stored, so `should_extend_payload` can later read the recorded answer. `state` is the
pre-verify `block_states[root]`, as in the spec; the warm state from
`verify_execution_payload_envelope` is kept only for `blockStates`. -/
forkdef onExecutionPayloadEnvelope (signedEnv : SignedExecutionPayloadEnvelope) : StoreTransition Unit := do
  let store ← get
  let envelope := signedEnv.message
  let state ← FcMap.getOrAssert store.blockStates envelope.beaconBlockRoot
    "envelope.beacon_block_root in store.block_states"
  -- `assert is_data_available(envelope.beacon_block_root)`, inherited from Gloas at the same
  -- position.
  assert (isDataAvailable envelope.beaconBlockRoot)

  match verifyExecutionPayloadEnvelope state signedEnv with
  | .error e => throw e
  | .ok warm =>
    -- [New in Heze:EIP7805] record whether the payload satisfies the inclusion-list constraints
    let store ← recordPayloadInclusionListSatisfaction store envelope.beaconBlockRoot envelope.payload
    -- INVARIANT: `payloads[root]` and `payloadInclusionListSatisfaction[root]` are written
    -- together here (the satisfaction key via `recordPayloadInclusionListSatisfaction` just
    -- above). Keep it that way: `isPayloadInclusionListSatisfied` opens with the spec's
    -- `assert root in store.payload_inclusion_list_satisfaction` (a throwing `getOrAssert`),
    -- and this pairing is what keeps that reject unreachable for any verified `root`
    -- (present in `payloads`).
    set { store with
      blockStates := FcMap.insert store.blockStates envelope.beaconBlockRoot warm,
      payloads := FcMap.insert store.payloads envelope.beaconBlockRoot envelope }

end EngineSeam

inherit storeTargetCheckpointState
inherit validateOnAttestation
inherit updateLatestMessages
inherit onAttestation
inherit onAttesterSlashing

/-- `get_forkchoice_store(anchor_state, anchor_block)` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:139-166`): the Gloas anchor store with the two
`[New in Heze:EIP7805]` fields seeded empty: `payloadInclusionListSatisfaction` as an empty
map and `inclusionListStore` as the empty `InclusionListStore` (no spec counterpart; the spec's
store is a process-lifetime singleton, folded into `Store` here, see the `InclusionListStore`
docstring). The rest is Gloas verbatim: the millisecond clock, the anchor's two PTC vote arrays
of `[None] * PTC_SIZE`, and the opening `assert anchor_block.state_root ==
hash_tree_root(anchor_state)`, so the seed is a throwing `Except StoreTransitionError` action
rather than a total store literal. `pinAnchorRejects` locks the reject branch. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) :
    Except StoreTransitionError (Store map) := do
  -- `anchor_block.state_root == hash_tree_root(anchor_state)`: the boxed state hashes
  -- through `stateRoot` (the cached-tree path), not `htr` (which wants a bare `SSZRepr`).
  assert (anchorBlock.stateRoot == bytesToRoot (stateRoot anchorState).1)
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }
  let genesisTimeMs := secondsToMilliseconds (sszGet anchorState genesisTime)
  let timeMs ← liftErr (computeTimeAtSlotMs genesisTimeMs (sszGet anchorState slot))
  let emptyVotes : Array (Option Bool) := Array.replicate Const.ptcSize none
  pure
    { timeMs := timeMs
      genesisTimeMs := genesisTimeMs
      justifiedCheckpoint := cp, finalizedCheckpoint := cp
      unrealizedJustifiedCheckpoint := cp, unrealizedFinalizedCheckpoint := cp
      proposerBoostRoot := fcZeroRoot
      equivocatingIndices := #[]
      blocks := FcMap.insert FcMap.empty anchorRoot anchorBlock
      blockStates := FcMap.insert FcMap.empty anchorRoot anchorState
      blockTimeliness := FcMap.insert FcMap.empty anchorRoot #[true, true]
      checkpointStates := FcMap.insert FcMap.empty cp anchorState
      latestMessages := FcMap.empty
      unrealizedJustifications := FcMap.insert FcMap.empty anchorRoot cp
      payloads := FcMap.empty
      payloadTimelinessVote := FcMap.insert FcMap.empty anchorRoot emptyVotes
      payloadDataAvailabilityVote := FcMap.insert FcMap.empty anchorRoot emptyVotes
      -- [New in Heze:EIP7805] seeded empty in lockstep with `payloads` above (the INVARIANT
      -- note in `onExecutionPayloadEnvelope`: the two maps are always written together).
      payloadInclusionListSatisfaction := FcMap.empty
      inclusionListStore := InclusionListStore.empty }

/-- `get_inclusion_list_due_ms()` (`consensus-specs/specs/heze/fork-choice.md:250-251`):
`get_slot_component_duration_ms(INCLUSION_LIST_DUE_BPS)`. `bpsDeadlineMs` (inherited from Gloas)
IS `get_slot_component_duration_ms`. A fork-choice deadline helper leaning on that inherited
fork-choice function, so it lives here with the rest of the fork-choice layer. -/
forkdef getInclusionListDueMs : UInt64 := bpsDeadlineMs Const.inclusionListDueBps

/-- `on_inclusion_list(store, signed_inclusion_list)` (the wire handler,
`consensus-specs/specs/heze/fork-choice.md:264-311`): validate a received inclusion list, judge
its timeliness, and hand it to `process_inclusion_list`. `get_inclusion_list_store()` is
`store.inclusionListStore`.

v1.7.0-beta.4 adds the checks, in this order: the slot lies in the retention window (at most
`MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS` slots back); the transactions are non-empty, each one
non-empty, and within `MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST` in total; the dependent block
is known, sits at or before the shuffling dependent slot, and is a possible dependent block
(`is_valid_dependent_root`); the validator is in the inclusion-list committee, computed from the
dependent block's state advanced to the lookahead start; and the signature verifies. A list is
timely only in its own slot, before the deadline. alpha.12 ran none of the checks and judged
timeliness against the time into the current slot alone.

The state advance and the signature check are state-machine steps, so they cross the bridge
(`runNestedStateTransition` / `evalNestedStateTransition`) and a reject arrives wrapped as
`.transition`. Python's `and` short-circuits, so the time into the slot is read only for a list
in the current slot. -/
forkdef onInclusionList (signed : SignedInclusionList) : StoreTransition Unit := do
  let store ← get
  let inclusionList := signed.message
  let currentSlot ← getCurrentSlot store

  -- The slot must be within the retention window.
  assert (inclusionList.slot ≤ currentSlot)
  let windowEnd ← checkedAdd inclusionList.slot Const.minSlotsForInclusionListsRequests
    "on_inclusion_list: inclusion_list.slot + MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS"
  assert (windowEnd ≥ currentSlot)

  -- The transactions must be non-empty, each non-empty, and within the byte cap. The spec sums
  -- the lengths as a Python `int`, which cannot overflow, so the sum is over `Nat`.
  let transactions := inclusionList.transactions.toArray
  let transactionsSize : Nat := transactions.foldl (fun acc tx => acc + tx.size) 0
  assert (transactionsSize > 0)
  assert (transactionsSize ≤ Const.maxTransactionsBytesPerInclusionList.toNat)
  assert (transactions.all (·.size > 0))

  -- The dependent block must be known, no later than the shuffling dependent slot, and a
  -- possible dependent block for the committee lookahead.
  assert (FcMap.contains store.blocks inclusionList.dependentRoot)
  assert (FcMap.contains store.blockStates inclusionList.dependentRoot)
  let epoch := computeEpochAtSlot inclusionList.slot
  let dependentSlot := computeShufflingDependentSlot epoch
  let dependentBlock ← FcMap.getOrThrow store.blocks inclusionList.dependentRoot
  assert (dependentBlock.slot ≤ dependentSlot)
  assert (← isValidDependentRoot store inclusionList.dependentRoot dependentSlot)

  -- The validator must be in the inclusion-list committee, computed on a copy of the dependent
  -- block's state advanced to the lookahead start.
  let dependentState ← FcMap.getOrThrow store.blockStates inclusionList.dependentRoot
  let lookaheadStartSlot := computeShufflingLookaheadStartSlot epoch
  let state ←
    if (sszGet dependentState slot) < lookaheadStartSlot then
      runNestedStateTransition dependentState (processSlots lookaheadStartSlot)
    else pure dependentState
  let committee ← getInclusionListCommittee state inclusionList.slot
  assert (committee.toArray.contains inclusionList.validatorIndex)

  -- The signature must verify.
  assert (← evalNestedStateTransition state (isValidInclusionListSignature state signed))

  -- Timely only in its own slot, before the deadline.
  let isTimely ←
    if inclusionList.slot == currentSlot then
      pure (decide ((← getTimeIntoSlotMs store) < getInclusionListDueMs))
    else pure false
  set { store with
    inclusionListStore := processInclusionList store.inclusionListStore signed isTimely }

end

end EthCLSpecs.Heze
