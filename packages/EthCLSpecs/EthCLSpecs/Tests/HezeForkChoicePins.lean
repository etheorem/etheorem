import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Tests.HezeForkChoicePins`: the Heze fork-choice build-enforced pins

The vectorless pins for Heze's fork choice: reject branches and helper values no
conformance vector reaches, locked by `#guard` / `native_decide` so a regression fails
the build rather than passing silently.

They live in `EthCLSpecsTests` rather than beside the declarations they pin. The
lakefile already declares that library for exactly this content, and a pin compiled
into `EthCLSpecs` is shipped weight: `native_decide` bakes its evaluation into the
shipped module, and a consumer importing the fork body pays for checks that only the
build gate reads. Every declaration these pins reach is public.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.HezeForkChoicePins

-- Inside `namespace EthCLSpecs.Heze`, where these pins used to sit, the fork's own
-- declarations beat the `open EthCLSpecs.Fulu` above it. Out here neither wins, so the
-- Fulu names that Heze (or Gloas, through it) redeclares are hidden.
open EthCLSpecs.Heze
  BeaconBlock

/-! ### Build-enforced pin (vectorless): the inclusion-list satisfaction gate

`is_payload_inclusion_list_satisfied` is the FOCIL fork-choice gate `should_extend_payload`
reads to refuse a payload that failed its inclusion-list constraints. No conformance vector
exercises it, and the pyspec conformance runs answer every engine call through the optimistic
`is_inclusion_list_satisfied = true` default, so the discriminating `false` branch is
otherwise dead code. This pin drives the predicate on a minimal `Store` directly; the four
verified/recorded combinations are enumerated one per `#guard` below, each with its expected
answer beside it. Everything is hash-free (`is_payload_verified` is a `payloads` membership
test, no `htr`), so kernel `#guard` per the hash-tactic rule.

The pin fixes the recorded bit by hand rather than through the engine, so the
`isInclusionListSatisfied` answer itself is out of its reach; `pinRecordRefuted` below
drives that refuting branch through the record path into this gate. -/

/-- The pins' concrete fork-choice monad: the minimal preset over the deterministic
`treeMap` and the FFI hasher, the annotation every pin's `.run` otherwise repeats. -/
private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

private def pinPilsRoot : Root := Vector.replicate 32 9

/-- A minimal Heze `Store` exercising `isPayloadInclusionListSatisfied` at `pinPilsRoot`.
`payloadPresent` controls whether `root ∈ payloads` (the `is_payload_verified` gate); `recorded` is
the optional `payloadInclusionListSatisfaction[root]` entry. Every other field is empty/zero
(`FcMap.empty`, default checkpoints, `fcZeroRoot`), mirroring the `getForkchoiceStore` literal. The
`payloads` value is never read (the predicate tests membership only), so a `default` envelope
serves. The `letI`s fix the preset / hasher so the anonymous `Store` constructor synthesizes them. -/
private def pinPilsStore (payloadPresent : Bool) (recorded : Option Bool) :
    @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { timeMs := 0, genesisTimeMs := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := if payloadPresent then FcMap.insert FcMap.empty pinPilsRoot default else FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction :=
      match recorded with
      | some b => FcMap.insert FcMap.empty pinPilsRoot b
      | none   => FcMap.empty
    inclusionListStore := InclusionListStore.empty }

/-- What `pinPils` observed: the predicate's answer, or which class of throw rejected it.

Naming the class is the point. Folding every `.error` to a single marker pins only *that* a
throw happened, so a regression from the spec's `assert` to an uncaught `.missingKey` would
still satisfy the pin, and that swap is exactly the difference between a faithful rejection and
a bug. `pinCommitteeThrows` below holds the same line from the other side, asserting a reject is
*not* an expected rejection. -/
private inductive PilsAnswer where
  /-- The predicate ran clean and answered `b`. -/
  | answer (b : Bool)
  /-- The spec's `assert root ∈ payload_inclusion_list_satisfaction` fired: the expected reject. -/
  | assertReject
  /-- Any other throw (a bare `.missingKey` read, a decode miss). Never expected at this gate. -/
  | otherReject
  deriving DecidableEq

/-- The predicate's answer on `pinPilsStore payloadPresent recorded`. The `letI`s re-supply the
preset / hasher the `forkdef` parameters want (Lean re-synthesizes them rather than reading the
store's fixed type), the same pattern the `InclusionListStore` pins in this file use. -/
private def pinPils (payloadPresent : Bool) (recorded : Option Bool) : PilsAnswer :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store := pinPilsStore payloadPresent recorded
  -- Run the predicate concretely and match on *which* reject fired: `.assert` is the spec's
  -- own guard, anything else is our bug.
  match (isPayloadInclusionListSatisfied (map := treeMap) store pinPilsRoot : PinM Bool).run store with
  | .ok b _              => .answer b
  | .error (.assert _) _ => .assertReject
  | .error _ _           => .otherReject

-- verified + recorded `false` ⇒ `false` (do not extend this payload).
#guard pinPils true (some false) = .answer false
-- verified + recorded `true` ⇒ `true`.
#guard pinPils true (some true) = .answer true
-- unverified (root ∉ payloads) ⇒ `false`, even with the satisfaction bit recorded `true`.
#guard pinPils false (some true) = .answer false
-- verified but no recorded entry ⇒ the spec's `assert root ∈ payload_inclusion_list_satisfaction`
-- now *rejects* (a state the invariant rules out) rather than reading a `lookupD` default. The
-- `.assertReject` (over a bare "it threw") is what a regression to `.missingKey` would break.
#guard pinPils true none = .assertReject
-- unverified AND no recorded entry ⇒ still the spec's assert, because
-- `assert root in store.payload_inclusion_list_satisfaction` precedes the verified check
-- (`heze/fork-choice.md:207-220`). A model that tested `is_payload_verified` first would answer
-- `.answer false` here, and the other three quadrants could not tell the difference.
#guard pinPils false none = .assertReject

/-! ### Build-enforced pins (vectorless): the FOCIL fork-choice helpers

`get_inclusion_list_due_ms`, `record_payload_inclusion_list_satisfaction`, and `on_inclusion_list`
ship no conformance vector either. These drive them end-to-end so a future edit can't regress them
silently: the deadline constant, the record path's rejects and its `(slot, dependent_root)` key,
the recorded EL answer, and the timeliness bit `on_inclusion_list` files with each list. -/

/-- `get_inclusion_list_due_ms = INCLUSION_LIST_DUE_BPS * SLOT_DURATION_MS // BASIS_POINTS`. Under
the minimal config that is `6667 * 6000 / 10000 = 4000` (truncating divide), pinning both the
`INCLUSION_LIST_DUE_BPS = 6667` constant and the inherited `bpsDeadlineMs` composition. Arithmetic
only (no hash), so kernel `#guard`. -/
private def pinIlDueMs : UInt64 :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  getInclusionListDueMs
#guard pinIlDueMs = 4000

/-- The faithful empty-committee throw. Over a zero-validator `default BeaconState`, slot 0's
beacon committee is empty, so `getInclusionListCommittee` hits the empty-committee guard and
rejects. Pyspec raises `ZeroDivisionError` on the same `indices[i % 0]`, an uncaught fault, so the
pin checks the reject is NOT an expected rejection (a `.transition (.arithmetic …)`, not a caught
`.assert`), the property a regression to `assert` would break. `on_inclusion_list` reaches the
helper after its state advance. At v1.7.0-beta.4 the record path no longer computes a committee,
so the pin drives the helper directly, in plain `Except` (it needs no `MonadStateOf`). `State` is
FFI-backed (`FastBox`), so `native_decide`. -/
private def pinCommitteeThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Heze.BeaconState minimal)
  match (getInclusionListCommittee (StoreTransition := Except StoreTransitionError) state 0) with
  | .ok _    => false
  | .error e => !e.isExpectedRejection
example : pinCommitteeThrows = true := by native_decide

/-! #### The record path

`record_payload_inclusion_list_satisfaction(store, root, payload, execution_engine)` reads the
block at `root`, takes the slot before it, and keys the inclusion-list store by that slot and the
shuffling dependent root `root`'s chain fixes for it. The fixture store holds two blocks:
`pinPilsRoot` at `headSlot`, and its parent `pinParentRoot` at slot 0. For a head at slot 1 the
previous slot is 0, its dependent slot is 0, and the ancestor walk from the head lands on the
parent, so the record path reads the key `(0, pinParentRoot)`. -/

private def pinParentRoot : Root := Vector.replicate 32 8

/-- A transaction holding the single byte `b` (enough to make two transactions compare
unequal for the dedup pins). -/
private def pinTx (b : UInt8) : Transaction := ⟨#[b]⟩

/-- An inclusion list from validator `v` for `(slot, dependentRoot)`, carrying `txs`. The `letI`
fixes the preset so the anonymous constructor can synthesize it (a return-type annotation alone
does not flow into instance resolution for `{ … }`). -/
private def pinIL (v : ValidatorIndex) (slot : Slot) (dependentRoot : Root)
    (txs : Array Transaction) : @InclusionList minimal :=
  letI : Preset := minimal
  { slot := slot, validatorIndex := v, dependentRoot := dependentRoot, transactions := ⟨txs⟩ }

/-- `pinIL` wrapped with an empty signature. No pin here verifies it. -/
private def pinSIL (v : ValidatorIndex) (slot : Slot) (dependentRoot : Root)
    (txs : Array Transaction) : @SignedInclusionList minimal :=
  letI : Preset := minimal
  { message := pinIL v slot dependentRoot txs, signature := default }

/-- An inclusion-list store holding one list from validator 5, filed under
`(0, filedUnder)` with timeliness `timely`, carrying the transaction `0xAA`. -/
private def pinFiledStore (filedUnder : Root) (timely : Bool) :
    @InclusionListStore minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let entry : InclusionListEntry :=
    { signedInclusionList := pinSIL 5 0 filedUnder #[pinTx 0xAA], timely := timely }
  { InclusionListStore.empty with
    inclusionLists := FcMap.insert FcMap.empty (0, filedUnder) (FcMap.insert FcMap.empty 5 entry) }

/-- `pinPilsStore payloadPresent none` with the two fixture blocks and the given
inclusion-list store. -/
private def pinRecordStore (payloadPresent : Bool) (headSlot : Slot)
    (ils : @InclusionListStore minimal treeMap fastHasherTag) :
    @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let parent : @BeaconBlock minimal := default
  let head : @BeaconBlock minimal :=
    { (default : @BeaconBlock minimal) with slot := headSlot, parentRoot := pinParentRoot }
  { pinPilsStore payloadPresent none with
    blocks := FcMap.insert (FcMap.insert FcMap.empty pinParentRoot parent) pinPilsRoot head
    inclusionListStore := ils }

/-- A root missing from `store.blocks` is the `missingKey root` reject: the spec's bare
`store.blocks[root]` read, a `KeyError`. Hash-free, so kernel `#guard`. -/
private def pinRecordMissingBlock : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let store := pinPilsStore false none
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .error (.missingKey k) _ => k == pinPilsRoot
  | _                        => false
#guard pinRecordMissingBlock = true

/-- A block at slot 0 is the checked-subtraction fault: `store.blocks[root].slot - 1` underflows,
which pyspec raises as `ValueError`, an uncaught fault, so the reject is `.transition
(.arithmetic …)`. Hash-free, so kernel `#guard`. -/
private def pinRecordSlotZero : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let store := pinRecordStore false 0 InclusionListStore.empty
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .error (.transition (.arithmetic _)) _ => true
  | _                                      => false
#guard pinRecordSlotZero = true

/-- `record_payload_inclusion_list_satisfaction` records the engine answer at `root`: with
the optimistic default (`isInclusionListSatisfied = true`) it writes `true`. The head at slot 1
clears the underflow fault, and the parent block lets the dependent-root walk finish. The recorded
answer is `true` regardless of the required transactions (the optimistic oracle ignores `ilTxs`),
so what this pin fixes is the record path writing the answer at the right key. Hash-free, so
kernel `#guard`. -/
private def pinRecordSatisfied : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let store := pinRecordStore false 1 InclusionListStore.empty
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .ok after _ => FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot
  | .error _ _  => none
#guard pinRecordSatisfied = some true

/-- The recorded bit and the gate's answer, or the reject that fired. Keeping `threw`
separate is the whole point: the *gate* arm is where a tuple collapses, since a throw from
`isPayloadInclusionListSatisfied` would hand back `(some false, false)`, byte-identical to the
legitimate refusal this pin exists to check. The record-path arm was already distinguishable
(`(none, false)`); this makes both so. -/
private inductive RecordAnswer where
  /-- The record path completed: the stored bit and the gate's answer. -/
  | recorded (value : Option Bool) (gate : Bool)
  /-- Either the record path or the gate rejected. -/
  | threw
  deriving DecidableEq

/-- The discriminating counterpart to `pinRecordSatisfied`: the same record path under a
*refuting* engine, a local `letI` instance answering `false` in place of the optimistic
default (`EthCLLib.Spec.Engine` documents the design). The record path writes `false` at a
*verified* `root`, and `isPayloadInclusionListSatisfied` then refuses to extend it. That
covers the branch every conformance vector leaves dead, end-to-end: oracle → recorded
answer → gate. `pinRecordStore true …` puts `root ∈ payloads`, so the membership check
passes and the recorded bit is what decides. Hash-free, so kernel `#guard`. -/
private def pinRecordRefuted : RecordAnswer :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : ExecutionEngine (@EthCLSpecs.Heze.ExecutionPayload minimal) Transaction
      (@EthCLSpecs.Heze.ExecutionRequests minimal) :=
    { isInclusionListSatisfied := fun _ _ => false
      verifyAndNotifyNewPayload := fun _ _ _ _ => true }
  let store := pinRecordStore true 1 InclusionListStore.empty
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .error _ _  => .threw
  | .ok after _ =>
    let recorded := FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot
    match (isPayloadInclusionListSatisfied (map := treeMap) after pinPilsRoot : PinM Bool).run after with
    | .ok gate _  => .recorded recorded gate
    | .error _ _  => .threw
-- refuting oracle ⇒ recorded `false`, and the gate rejects the verified payload.
#guard pinRecordRefuted = .recorded (some false) false

/-- The record path reads the key `(slot - 1, dependent_root)` and only the timely lists there.
The engine here is an observer: it answers whether the required transactions it was handed
contain `0xAA`, so the recorded bit says whether the record path found the filed list. A list
filed under the parent (the walk's dependent root) and timely is found. A list filed under any
other root, or filed untimely, is not. Hash-free, so kernel `#guard`. -/
private def pinRecordKeyed (filedUnder : Root) (timely : Bool) : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : ExecutionEngine (@EthCLSpecs.Heze.ExecutionPayload minimal) Transaction
      (@EthCLSpecs.Heze.ExecutionRequests minimal) :=
    { isInclusionListSatisfied := fun _ ilTxs => ilTxs.contains (pinTx 0xAA)
      verifyAndNotifyNewPayload := fun _ _ _ _ => true }
  let store := pinRecordStore false 1 (pinFiledStore filedUnder timely)
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .ok after _ => FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot
  | .error _ _  => none
#guard pinRecordKeyed pinParentRoot true = some true
#guard pinRecordKeyed pinPilsRoot true = some false
#guard pinRecordKeyed pinParentRoot false = some false

/-! #### `on_inclusion_list`

The handler asserts the retention window, the transaction sizes, the dependent block, its slot,
`is_valid_dependent_root`, committee membership, and the signature before it files the list. The
fixture store comes from `getForkchoiceStore` over a populated anchor, so the head, the dependent
root, and the committee all resolve as on a real store. The anchor block is the dependent block,
the list is for slot 0, and its validator is the committee's first member. The verify-off crypto
backend (`bls_setting: 2`) accepts the empty signature. -/

/-- A minimal populated `BeaconState`: `SLOTS_PER_EPOCH` active validators at slot 0. Enough
that slot 0's beacon committee is non-empty (`computeCommittee` takes the shuffled slice
`[0, N // SLOTS_PER_EPOCH) = [0, 1)`). A `default` validator has `exitEpoch = 0`, hence
inactive, so only `exitEpoch := farFutureEpoch` is overridden (`is_active_validator` needs
`activationEpoch ≤ epoch < exitEpoch`, and `activationEpoch` is already `0`). The registry is
pushed onto the empty `base.validators` so the `SSZList` element type is inferred, never
spelled. -/
private def pinPopulatedState : @EthCLSpecs.Heze.BeaconState minimal :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let base := (default : @EthCLSpecs.Heze.BeaconState minimal)
  let activeValidator : Validator := { (default : Validator) with exitEpoch := Const.farFutureEpoch }
  let vals := (Array.replicate Const.slotsPerEpoch activeValidator).foldl (·.push ·) base.validators
  { base with validators := vals }

/-- `on_inclusion_list` files the list with its timeliness: a list received in its own slot
before `get_inclusion_list_due_ms` is timely, one at or after the deadline is not. Runs the handler
end-to-end with the store clock `intoSlotMs` into slot 0, then reads the filed entry's timeliness
back at `(0, anchor_root)` and the validator. `getForkchoiceStore` hashes the anchor (FFI
`Sha256`), so this is a `native_decide` `example` (`Lean.ofReduceBool`). -/
private def pinOnIlTimely (intoSlotMs : UInt64) : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.verifyOff
  let state : State := SSZ.FastBox pinPopulatedState
  let anchorBlock : @BeaconBlock minimal :=
    { (default : @BeaconBlock minimal) with stateRoot := htr pinPopulatedState }
  let anchorRoot := htr anchorBlock
  match (getForkchoiceStore (map := treeMap) state anchorBlock,
      getInclusionListCommittee (StoreTransition := Except StoreTransitionError) state 0) with
  | (.ok store0, .ok committee) =>
    let validatorIndex := vget committee 0
    let signed := pinSIL validatorIndex 0 anchorRoot #[pinTx 0xAA]
    let store := { store0 with timeMs := store0.genesisTimeMs + intoSlotMs }
    match runOn store
        (onInclusionList (map := treeMap) signed : EStateM StoreTransitionError (Store treeMap) Unit) with
    | .ok after =>
      let entries := (FcMap.lookup after.inclusionListStore.inclusionLists (0, anchorRoot)).getD
        FcMap.empty
      (FcMap.lookup entries validatorIndex).map (·.timely)
    | .error _ => none
  | _ => none
-- 0 ms into the slot: 0 < 4000 ⇒ timely.
example : pinOnIlTimely 0 = some true := by native_decide
-- 4000 ms into the slot: not < 4000 ⇒ untimely.
example : pinOnIlTimely 4000 = some false := by native_decide

/-! ### Build-enforced pins for the inclusion-list store (vectorless)

FOCIL has no conformance vector (the module docstring carries the coverage story), so these
pin `process_inclusion_list`'s two branches, `get_inclusion_list_transactions`, and
`get_inclusion_list_bits` to hand-derived outcomes. They build a small
`InclusionListStore treeMap` (deterministic key order) under the minimal preset and the FFI
hasher. At v1.7.0-beta.4 the store is keyed by `(slot, dependent_root)` and each entry carries its
own timeliness, so nothing here hashes, and every pin is a kernel `#guard`. -/

private def pinKey : Root := Vector.replicate 32 7
private def pinAltRoot : Root := Vector.replicate 32 2

/-- Number of inclusion lists stored under `(0, pinKey)`. The `letI`s supply the store's preset /
hasher for the field projection (Lean re-synthesizes them rather than reading the argument's
fixed type). -/
private def pinNumStored (s : @InclusionListStore minimal treeMap fastHasherTag) : Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  ((FcMap.lookup s.inclusionLists ((0 : Slot), pinKey)).getD FcMap.empty |> FcMap.keys).length
/-- The equivocator set recorded under `(0, pinKey)`. -/
private def pinEquivs (s : @InclusionListStore minimal treeMap fastHasherTag) : Array ValidatorIndex :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  FcMap.lookupD s.equivocators ((0 : Slot), pinKey)

/-- A store already holding one timely list from validator 5 under `(0, pinKey)`. Shared by the
stored-entry pins. -/
private def pinStoreB : @InclusionListStore minimal treeMap fastHasherTag := pinFiledStore pinKey true

-- Stored entry, conflict: a second, differing list from validator 5 adds 5 to
-- `equivocators[key]` and stores nothing new. Returns (equivocators, stored count); expected
-- (#[5], 1).
private def pinResConflict : Array ValidatorIndex × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinSIL 5 0 pinKey #[pinTx 0xBB]) true
  (pinEquivs after, pinNumStored after)
#guard pinResConflict = (#[5], 1)

-- Stored entry, a third differing list from an equivocator: `equivocators[key]` is a set, so 5
-- is not added twice. Expected (#[5], 1).
private def pinResRepeatConflict : Array ValidatorIndex × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let once := processInclusionList pinStoreB (pinSIL 5 0 pinKey #[pinTx 0xBB]) true
  let after := processInclusionList once (pinSIL 5 0 pinKey #[pinTx 0xCC]) true
  (pinEquivs after, pinNumStored after)
#guard pinResRepeatConflict = (#[5], 1)

-- Stored entry, match: re-receiving the *same* list is a no-op. Returns (equivocator count,
-- stored count); expected (0, 1).
private def pinResMatch : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinSIL 5 0 pinKey #[pinTx 0xAA]) true
  ((pinEquivs after).size, pinNumStored after)
#guard pinResMatch = (0, 1)

-- No stored entry: the first list from a validator is stored (one entry under the key) with
-- its timeliness in the entry. Reads the bit back from the entry, so a flipped `timely` fails;
-- the stored-count half pins that exactly one list was filed. Returns (stored count, timeliness
-- of validator 5's entry); expected (1, some isTimely).
private def pinResNew (isTimely : Bool) : Nat × Option Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList InclusionListStore.empty (pinSIL 5 0 pinKey #[pinTx 0xAA]) isTimely
  let entries := (FcMap.lookup after.inclusionLists ((0 : Slot), pinKey)).getD FcMap.empty
  (pinNumStored after, (FcMap.lookup entries 5).map (·.timely))
#guard pinResNew true = (1, some true)
#guard pinResNew false = (1, some false)

/-- Two stored lists under `(0, pinKey)`: validator 5 → [0xAA] timely, validator 6 →
[0xAA, 0xBB] untimely, and the key's equivocator set `equiv`. -/
private def pinTwoLists (equiv : Array ValidatorIndex) :
    @InclusionListStore minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let entry5 : InclusionListEntry :=
    { signedInclusionList := pinSIL 5 0 pinKey #[pinTx 0xAA], timely := true }
  let entry6 : InclusionListEntry :=
    { signedInclusionList := pinSIL 6 0 pinKey #[pinTx 0xAA, pinTx 0xBB], timely := false }
  { inclusionLists := FcMap.insert FcMap.empty ((0 : Slot), pinKey)
      (FcMap.insert (FcMap.insert FcMap.empty 5 entry5) 6 entry6)
    equivocators := FcMap.insert FcMap.empty ((0 : Slot), pinKey) equiv }

/-- `get_inclusion_list_transactions` over `pinTwoLists equiv` at `(0, dependentRoot)`. Pure, so
the `#guard`s below compare the result directly. -/
private def pinTxs (equiv : Array ValidatorIndex) (dependentRoot : Root) (onlyTimely : Bool) :
    Array Transaction :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  getInclusionListTransactions (pinTwoLists equiv) 0 dependentRoot onlyTimely

-- No equivocators, timeliness ignored: union of {0xAA} and {0xAA, 0xBB}, deduped to two.
#guard (pinTxs #[] pinKey false).size == 2
#guard (pinTxs #[] pinKey false).contains (pinTx 0xAA)
#guard (pinTxs #[] pinKey false).contains (pinTx 0xBB)
-- only_timely drops validator 6's untimely list, leaving just {0xAA}.
#guard pinTxs #[] pinKey true == #[pinTx 0xAA]
-- Equivocator 6 is filtered out regardless of timeliness, leaving just {0xAA}.
#guard pinTxs #[6] pinKey false == #[pinTx 0xAA]
-- Another dependent root is another key: nothing is stored there.
#guard pinTxs #[] pinAltRoot false == #[]

/-- A committee with validator 5 at position 0, validator 6 at position 1, and validator 99
(who sent no list) everywhere else. -/
private def pinCommittee : Vector ValidatorIndex 16 :=
  Vector.ofFn fun i => if i.val = 0 then 5 else if i.val = 1 then 6 else 99

/-- The first three bits of `get_inclusion_list_bits` over `pinTwoLists equiv` for
`pinCommittee`: a member's bit is set when it has a counted list for the key. -/
private def pinBits (equiv : Array ValidatorIndex) (onlyTimely : Bool) : List Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let bits := getInclusionListBits (pinTwoLists equiv) pinCommittee 0 pinKey onlyTimely
  [bitGet bits 0, bitGet bits 1, bitGet bits 2]

-- Timeliness ignored: both senders' bits are set, the silent member's is not.
#guard pinBits #[] false = [true, true, false]
-- only_timely: validator 6's untimely list does not count.
#guard pinBits #[] true = [true, false, false]
-- An equivocator's bit is clear.
#guard pinBits #[5] false = [false, true, false]

/-- `is_inclusion_list_bits_inclusive` against the timely local view `[true, false, …]`: bits
that set position 0 are inclusive, and bits that miss it are not. -/
private def pinInclusive (given : List Nat) : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let bits := given.foldl (fun b i => bitSet b i true) (default : Bitvector 16)
  isInclusionListBitsInclusive (pinTwoLists #[]) pinCommittee 0 pinKey bits

#guard pinInclusive [0] = true
#guard pinInclusive [0, 1, 2] = true
#guard pinInclusive [1] = false
#guard pinInclusive [] = false

/-- Vectorless reject pin for `get_forkchoice_store`'s opening assert
(`assert anchor_block.state_root == hash_tree_root(anchor_state)`, `heze/fork-choice.md:140`). The
default block's all-zero `stateRoot` cannot equal `hash_tree_root` of the default state (a
non-zero SHA-256 digest), so the seed takes the reject branch. No conformance vector reaches the
mismatch (the harness derives anchor block + state from one vector, so `state_root` always
matches), so this pin is the only witness of the throw. Computes `hash_tree_root` (FFI `Sha256`)
→ `native_decide`. The Fulu and Gloas constructors carry the textually-identical assert.

Matches `.assert` specifically rather than reading `toOption.isNone`: the spec's opening guard is
what should fire here, and a regression to some other throw class is a bug this pin has to catch
rather than absorb. -/
private def pinAnchorRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match getForkchoiceStore (SSZ.FastBox (default : @BeaconState minimal))
      (default : @BeaconBlock minimal) (map := treeMap) with
  | .error (.assert _) => true
  | _                  => false
example : pinAnchorRejects = true := by native_decide

end EthCLSpecs.Tests.HezeForkChoicePins
