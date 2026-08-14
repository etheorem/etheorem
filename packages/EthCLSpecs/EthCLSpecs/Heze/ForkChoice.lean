import EthCLSpecs.Heze.Transition
import EthCLSpecs.Gloas.ForkChoice
import EthCLSpecs.Heze.Committees
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
`Store` value through the generic `StoreTransition` monad, so the inclusion-list store rides
inside it (the `InclusionListStore` declaration below carries the full rationale). Most
handlers are inherited verbatim; the FOCIL touch points are re-declared here:

* `get_forkchoice_store` seeds the two new store fields empty;
* `is_payload_inclusion_list_satisfied` / `record_payload_inclusion_list_satisfaction` /
  `get_inclusion_list_due_ms` / `is_inclusion_list_satisfied` are the new helpers;
* `should_extend_payload` gains the inclusion-list gate;
* `on_execution_payload_envelope` records satisfaction before storing the payload;
* `on_inclusion_list` is the new wire handler.

EIP-7805 also extends `PayloadAttributes` with `inclusion_list_transactions` and threads it
through `notify_forkchoice_updated` (`heze/fork-choice.md:65-104`). Both belong to the
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
pinned spec text (`consensus-specs` at tag `v1.7.0-alpha.11`) is its oracle
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
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

inherit ForkChoiceNode
deriving instance BEq, Inhabited for ForkChoiceNode

inherit LatestMessage
deriving instance Inhabited for LatestMessage

/-- `InclusionListStore` (`consensus-specs/specs/heze/inclusion-list.md:28-38`): the
fork-choice node's view of the inclusion lists it has seen. The three fields:

* `inclusionLists`: every stored `InclusionList`, keyed first by its committee root, then by
  the list's own hash-tree root (the spec's `DefaultDict[Root, Dict[Root, InclusionList]]`);
* `inclusionListTimeliness`: per stored-list root, whether the list arrived before the
  `INCLUSION_LIST_DUE_BPS` deadline;
* `equivocators`: per committee root, the validators caught publishing two different lists.

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
  inclusionLists          : map Root (map Root InclusionList)
  inclusionListTimeliness : map Root Bool
  equivocators            : map Root (Array ValidatorIndex)

section

variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

-- The store-transition monad, minus `MonadStateOf`: the inclusion-list helpers below thread the
-- (sub-)store explicitly rather than through `get`, so they need only `Monad` plus the store
-- reject to throw (`FcMap.getOrThrow`'s `missingKey`). Leaving `MonadStateOf` off lets the
-- vectorless pins run them in plain `Except StoreTransitionError`, with no dummy `Store` to
-- `.run` over. A concrete fork-choice monad (the one `fork_choice_section` opens below) still
-- satisfies these two, so the store handlers bind these helpers with `←` unchanged.
variable {StoreTransition : Type → Type} [Monad StoreTransition]
variable [MonadExceptOf StoreTransitionError StoreTransition]

/-- The empty `InclusionListStore`: no stored lists, no timeliness, no equivocators.
`getForkchoiceStore` seeds the folded-in `Store` field with it. The spec has no counterpart
line: there the store is the lazily-created `get_inclusion_list_store()` singleton (see the
`InclusionListStore` docstring above for the fold-in). Every pin below also builds from it,
so the all-empty literal lives in one place. -/
def InclusionListStore.empty : InclusionListStore map :=
  { inclusionLists := FcMap.empty, inclusionListTimeliness := FcMap.empty, equivocators := FcMap.empty }

/-- The inner comprehension of `get_inclusion_list_transactions`
(`consensus-specs/specs/heze/inclusion-list.md:105-114`): over the inclusion lists stored for
one committee key, keep those from non-equivocating validators (and, when `onlyTimely`, only
the timely ones), gather their transactions, and deduplicate.

Factored out of the accessor so the equivocator / timeliness / dedup logic is unit-checkable
without building a `BeaconState` for the committee key, the same reason `cyclicSample` is
factored out in `Committees`. The dedup keeps each transaction's first occurrence
(`arrayUnion`): the spec's `list(set(transactions))` keeps each transaction once and calls
the order irrelevant, so a deterministic representative lets `#guard` pin the result.
`inclusion_list_timeliness` is a plain `Dict` in the spec (`inclusion-list.md:34`), so
`timeliness[ilRoot]` raises `KeyError` on a miss: `FcMap.getOrThrow` (→ `missingKey`), throwing,
in place of the old `lookupD false` default. The read is *conditional*: the comprehension's
`and`/`or` short-circuit reaches `timeliness[il_root]` only for a non-equivocator's list and
only when `only_timely` is set, so the guards below run in that exact order. Unreachable on
the spec path either way, where `process_inclusion_list` writes every stored list and its
timeliness entry together, so every stored `ilRoot` has an entry.

Only `getInclusionListTransactions` calls it, so this would be `private`. It is not,
because the pins that drive its throwing branches live in `EthCLSpecsTests` and Lean has
no test-visible modifier. The alternative was leaving one pin behind in the shipped
library for a visibility keyword's sake. -/
def collectInclusionListTransactions (inclusionLists : map Root InclusionList)
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool) (onlyTimely : Bool) :
    StoreTransition (Array Transaction) := do
  -- Gather the stored `(ilRoot, il)` entries in the map's fold order first (a pure pass);
  -- the fold order feeds the `arrayUnion` dedup below, so it is preserved. The throwing
  -- timeliness read then runs per entry, inside the comprehension's own guard order.
  let entries : Array (Root × InclusionList) :=
    FcMap.fold (fun acc ilRoot il => acc.push (ilRoot, il)) #[] inclusionLists
  let collected ← entries.foldlM (init := (#[] : Array Transaction)) fun acc (ilRoot, il) => do
    -- The condition is `validator_index not in store.equivocators[key] and (not only_timely
    -- or store.inclusion_list_timeliness[il_root])`: `and`/`or` short-circuit, so the
    -- (raising) timeliness read runs last, and only when it can decide the outcome.
    if equivocators.contains il.validatorIndex then pure acc
    else if !onlyTimely then pure (acc ++ il.transactions.toArray)
    else
      let timely ← FcMap.getOrThrow timeliness ilRoot
      if timely then pure (acc ++ il.transactions.toArray) else pure acc
  pure (arrayUnion #[] collected)

/-- `process_inclusion_list(store, inclusion_list, is_timely)`
(`consensus-specs/specs/heze/inclusion-list.md:57-82`): file a newly-received inclusion list,
or record an equivocation. Pure here (returns the updated `InclusionListStore`); the spec
mutates in place. The three branches mirror the Python:

* (A) the list is from a known equivocator for this committee (`validator_index in
  store.equivocators[key]`) → ignore it, return the store unchanged.
* (B) we already hold a list from this validator for this committee → if the new list differs
  from the stored one, add the validator to `equivocators[key]`; either way we have processed
  it, so return (storing nothing new). At most one stored list per validator exists (a list is
  filed only on branch (C), reached only when none matches), so the single `find?` match is
  exactly the Python loop's first-and-only hit. The equivocator `push` is guarded by branch
  (A) above, so it never duplicates.
* (C) otherwise → store the list under its `hash_tree_root` and record its timeliness.

`key` is the list's `inclusion_list_committee_root` (a field, no rehash). -/
forkdef processInclusionList (store : InclusionListStore map) (inclusionList : InclusionList)
    (isTimely : Bool) : InclusionListStore map :=
  let key := inclusionList.inclusionListCommitteeRoot
  let equivs := FcMap.lookupD store.equivocators key
  -- (A) ignore inclusion lists from known equivocators for this committee
  if equivs.contains inclusionList.validatorIndex then store
  else
    let stored := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
    match (FcMap.values stored).find? (fun il => il.validatorIndex == inclusionList.validatorIndex) with
    -- (B) already hold a list from this validator: equivocate iff it differs, then stop
    | some existing =>
      if existing == inclusionList then store
      else
        { store with
            equivocators := FcMap.insert store.equivocators key (equivs.push inclusionList.validatorIndex) }
    -- (C) first list from this validator: store it and its timeliness
    | none =>
      let inclusionListRoot := htr inclusionList
      let stored' := FcMap.insert stored inclusionListRoot inclusionList
      { store with
          inclusionLists := FcMap.insert store.inclusionLists key stored',
          inclusionListTimeliness := FcMap.insert store.inclusionListTimeliness inclusionListRoot isTimely }

/-- `get_inclusion_list_committee(state, slot)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:95-110`): concatenate every beacon committee for
`slot` in committee-index order, then take the first `INCLUSION_LIST_COMMITTEE_SIZE` members
cyclically (`cyclicSample`, in `Heze/Committees.lean`). Relocated from the beacon-state accessors
into this store-throwing block beside its sole caller `getInclusionListTransactions`: the spec's
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

/-- `get_inclusion_list_transactions(store, state, slot, only_timely=True)`
(`consensus-specs/specs/heze/inclusion-list.md:95-114`): the unique transactions from every
valid, non-equivocating inclusion list whose committee root matches the one `state`/`slot`
compute, optionally restricted to lists received before `INCLUSION_LIST_DUE_BPS`. Mirrors the
Python: derive the committee, key it by `hash_tree_root`, read the `defaultdict` entries for
that key, then run the comprehension (here `collectInclusionListTransactions`). Returns an
`Array` for the spec's `Sequence[Transaction]`; the dedup leaves order unspecified, as the
spec notes. -/
forkdef getInclusionListTransactions (store : InclusionListStore map) (state : State)
    (slot : Slot) (onlyTimely : Bool := true) : StoreTransition (Array Transaction) := do
  let committee ← getInclusionListCommittee state slot
  let key := htr committee
  -- `inclusion_lists` and `equivocators` are `DefaultDict`s (inclusion-list.md:31,35): the
  -- spec's `[key]` auto-creates an empty entry on a miss, so the defaults here are faithful.
  let inclusionLists := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
  let equivocators := FcMap.lookupD store.equivocators key
  collectInclusionListTransactions inclusionLists equivocators store.inclusionListTimeliness onlyTimely

end

/-- The Heze fork-choice store: the Gloas store plus the EIP-7805 fields. Re-declared as a
`forkstruct` rather than an `inherit Store`, so the two `[New in Heze:EIP7805]` fields can be added.
`payloadInclusionListSatisfaction` tracks, per beacon-block root, whether the revealed payload
satisfied the inclusion-list constraints (`consensus-specs/specs/heze/fork-choice.md:134`);
`inclusionListStore` folds in the spec's separate `InclusionListStore` (see the module docstring).
The seventeen Gloas fields are restated verbatim. -/
forkstruct Store (map : MapKind) [HasherTag] where
  time                          : UInt64
  genesisTime                   : UInt64
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
  -- [New in Heze:EIP7805] (consensus-specs/specs/heze/fork-choice.md:134)
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
inherit timeIntoSlotMs
inherit bpsDeadlineMs
inherit getParentPayloadStatus
inherit isParentNodeFull
inherit getAncestor
inherit isAncestor
inherit getCheckpointBlock
inherit getSupportedNode
inherit getDependentRoot
inherit isPayloadVerified
inherit voteCount
inherit payloadTimeliness
inherit payloadDataAvailability
inherit isPreviousSlotPayloadDecision

/-- `is_payload_inclusion_list_satisfied(store, root)`
(`consensus-specs/specs/heze/fork-choice.md:199-212`): whether the payload for `root`
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
`consensus-specs/specs/heze/fork-choice.md:221-236`): the Gloas body with the one new
inclusion-list gate. After the `is_payload_verified` check, a payload that fails the
inclusion-list constraints is not extended (`fork-choice.md:226`). The rest is Gloas verbatim.
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
inherit committeeWeight
inherit calculateCommitteeFraction
inherit getProposerScore
inherit getAttestationScore
inherit isHeadWeak
inherit isParentStrong
inherit shouldApplyProposerBoost
inherit getWeight
inherit getVotingSource
inherit filterBlockTree
inherit getFilteredBlockTree
inherit getNodeChildren
inherit getHead
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
inherit verifyExecutionPayloadEnvelopeSignature

-- Three verdicts on this fork's paths belong to something outside the vector: the EL's
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
whether a payload includes the required inclusion-list transactions. Its verdict is
EL-implementation-defined (the Engine API answers it against an external EL), so it reads the
`[ExecutionEngine]` seam rather than a fixed value; the default and the trust boundary are
documented on `EthCLLib.Spec.ExecutionEngine`. -/
forkdef isInclusionListSatisfied (payload : ExecutionPayload) (ilTxs : Array Transaction) : Bool :=
  -- Named type arguments: the class parameters are implicit on the projection, and `Requests`
  -- appears in no argument of this method, so it cannot be recovered from the call.
  ExecutionEngine.isInclusionListSatisfied (Payload := ExecutionPayload) (Tx := Transaction)
    (Requests := ExecutionRequests) payload ilTxs

/-- `record_payload_inclusion_list_satisfaction(store, state, root, payload, execution_engine)`
(`consensus-specs/specs/heze/fork-choice.md:180-193`): record whether `payload` satisfies the
inclusion-list constraints for `root`. Pure here (returns the updated store); the spec mutates
in place. `get_inclusion_list_store()` is `store.inclusionListStore`; the required
transactions are read for the previous slot (`state.slot - 1`) at the default `only_timely =
True`, and the EL verdict comes from `isInclusionListSatisfied`, which reads the
`[ExecutionEngine]` seam (the spec's `execution_engine` argument, modeled injectably). -/
forkdef recordPayloadInclusionListSatisfaction (store : Store map) (state : State) (root : Root)
    (payload : ExecutionPayload) : StoreTransition (Store map) := do
  -- The spec reads `Slot(state.slot - 1)`, a `uint64` subtraction that raises `ValueError` on a
  -- slot-0 state (invalidating the whole envelope). The reference runner leaves that fault
  -- uncaught, so it is `checkedSub`, the same operator `balanceAfterWithdrawals` reads its
  -- underflow through. The reject arrives as `.transition (.arithmetic …)`, an `uncaughtFault`
  -- rather than a caught `.assert` or a silent empty set.
  let stateSlot := sszGet state slot
  let prevSlot ← checkedSub stateSlot 1 "record_payload_inclusion_list_satisfaction: Slot(state.slot - 1)"
  let ilTxs ← getInclusionListTransactions store.inclusionListStore state prevSlot
  let satisfied := isInclusionListSatisfied payload ilTxs
  pure { store with
      payloadInclusionListSatisfaction := FcMap.insert store.payloadInclusionListSatisfaction root satisfied }

/-- `on_execution_payload_envelope` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:273-300`): the Gloas body with one added step,
`record_payload_inclusion_list_satisfaction` is called on the verified envelope *before* the
payload is stored (`fork-choice.md:295`), so `should_extend_payload` can later read the
recorded verdict. `state` is the pre-verify `block_states[root]`, as in the spec; the warm
state from `verify_execution_payload_envelope` is kept only for `blockStates`. -/
forkdef onExecutionPayloadEnvelope (signedEnv : SignedExecutionPayloadEnvelope) : StoreTransition Unit := do
  let store ← get
  let envelope := signedEnv.message
  let state ← FcMap.getOrAssert store.blockStates envelope.beaconBlockRoot
    "envelope.beacon_block_root in store.block_states"
  -- `assert is_data_available(envelope.beacon_block_root)` (`heze/fork-choice.md:285`),
  -- inherited from Gloas at the same position.
  assert (isDataAvailable envelope.beaconBlockRoot)

  match verifyExecutionPayloadEnvelope state signedEnv with
  | .error e => throw e
  | .ok warm =>
    -- [New in Heze:EIP7805] record whether the payload satisfies the inclusion-list constraints
    let store ← recordPayloadInclusionListSatisfaction store state envelope.beaconBlockRoot envelope.payload
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
`consensus-specs/specs/heze/fork-choice.md:140-166`): the Gloas anchor store with the two
`[New in Heze:EIP7805]` fields seeded empty: `payloadInclusionListSatisfaction` as an empty
map (`fork-choice.md:165`) and `inclusionListStore` as the empty `InclusionListStore` (no
spec counterpart; the spec's store is a process-lifetime singleton, folded into `Store` here,
see the `InclusionListStore` docstring). The rest is Gloas verbatim, including the opening
`assert anchor_block.state_root == hash_tree_root(anchor_state)` (`fork-choice.md:141`), so the
seed is a throwing `Except StoreTransitionError` action rather than a total store literal.
`pinAnchorRejects` below locks the reject branch. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) :
    Except StoreTransitionError (Store map) := do
  -- `anchor_block.state_root == hash_tree_root(anchor_state)`: the boxed state hashes
  -- through `stateRoot` (the cached-tree path), not `htr` (which wants a bare `SSZRepr`).
  assert (anchorBlock.stateRoot == bytesToRoot (stateRoot anchorState).1)
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }

  -- `uint64(anchor_state.genesis_time + SLOT_DURATION_MS * anchor_state.slot // 1000)`
  -- (`phase0/fork-choice.md:223`): both the product and the sum are checked. `anchor_state`
  -- comes straight off the wire, so a slot at or above `2^64 / SLOT_DURATION_MS` wraps and
  -- seeds the store with a wrong clock where pyspec errors.
  let elapsedMs ← checkedMul Const.slotDurationMs (sszGet anchorState slot)
    "get_forkchoice_store: SLOT_DURATION_MS * anchor_state.slot"
  let storeTime ← checkedAdd (sszGet anchorState genesisTime) (elapsedMs / 1000)
    "get_forkchoice_store: genesis_time + SLOT_DURATION_MS * slot // 1000"
  pure
    { time := storeTime
      genesisTime := sszGet anchorState genesisTime
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
      payloadTimelinessVote := FcMap.empty
      payloadDataAvailabilityVote := FcMap.empty
      -- [New in Heze:EIP7805] seeded empty in lockstep with `payloads` above (the INVARIANT
      -- note in `onExecutionPayloadEnvelope`: the two maps are always written together).
      payloadInclusionListSatisfaction := FcMap.empty
      inclusionListStore := InclusionListStore.empty }

/-- `get_inclusion_list_due_ms()` (`consensus-specs/specs/heze/fork-choice.md:242-243`):
`get_slot_component_duration_ms(INCLUSION_LIST_DUE_BPS)`. `bpsDeadlineMs` (inherited from Gloas)
IS `get_slot_component_duration_ms`. A fork-choice deadline helper leaning on that inherited
fork-choice function, so it lives here with the rest of the fork-choice layer. -/
forkdef getInclusionListDueMs : UInt64 := bpsDeadlineMs Const.inclusionListDueBps

/-- `on_inclusion_list(store, signed_inclusion_list)` (the new wire handler,
`consensus-specs/specs/heze/fork-choice.md:256-267`): on receiving an inclusion list, judge its
timeliness against `INCLUSION_LIST_DUE_BPS` and hand it to `process_inclusion_list`. The spec's
`seconds_to_milliseconds(store.time - store.genesis_time) % SLOT_DURATION_MS` is exactly the
inherited `timeIntoSlotMs`. `process_inclusion_list` is total, so the spec's "an invalid call
MUST NOT modify the store" is automatic here. The inclusion-list store rides inside `Store`, so
`get_inclusion_list_store()` is `store.inclusionListStore`. -/
forkdef onInclusionList (signed : SignedInclusionList) : StoreTransition Unit := do
  let store ← get
  let inclusionList := signed.message
  let isTimely := (← timeIntoSlotMs store) < getInclusionListDueMs
  set { store with
    inclusionListStore := processInclusionList store.inclusionListStore inclusionList isTimely }

end

end EthCLSpecs.Heze
