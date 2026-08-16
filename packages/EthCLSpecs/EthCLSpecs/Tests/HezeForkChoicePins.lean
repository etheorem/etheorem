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
build gate reads.

One declaration had to give up `private` for this: `collectInclusionListTransactions`,
whose throwing branches the `pinCollect` gates drive. Lean has no test-visible modifier,
so the choice was that or stranding one pin in the shipped library. Everything else these
pins reach was already public.

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
verdict beside it. Everything is hash-free (`is_payload_verified` is a `payloads` membership
test, no `htr`), so kernel `#guard` per the hash-tactic rule.

The pin fixes the recorded bit by hand rather than through the engine, so the
`isInclusionListSatisfied` verdict itself is out of its reach; `pinRecordRefuted` below
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
  { time := 0, genesisTime := 0
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

/-- What `pinPils` observed: the predicate's verdict, or which class of throw rejected it.

Naming the class is the point. Folding every `.error` to a single marker pins only *that* a
throw happened, so a regression from the spec's `assert` to an uncaught `.missingKey` would
still satisfy the pin, and that swap is exactly the difference between a faithful rejection and
a bug. `pinCommitteeThrows` below holds the same line from the other side, asserting a reject is
*not* an expected rejection. -/
private inductive PilsVerdict where
  /-- The predicate ran clean and answered `b`. -/
  | verdict (b : Bool)
  /-- The spec's `assert root ∈ payload_inclusion_list_satisfaction` fired: the expected reject. -/
  | assertReject
  /-- Any other throw (a bare `.missingKey` read, a decode miss). Never expected at this gate. -/
  | otherReject
  deriving DecidableEq

/-- The predicate's verdict on `pinPilsStore payloadPresent recorded`. The `letI`s re-supply the
preset / hasher the `forkdef` parameters want (Lean re-synthesizes them rather than reading the
store's fixed type), the same pattern the `InclusionListStore` pins in this file use. -/
private def pinPils (payloadPresent : Bool) (recorded : Option Bool) : PilsVerdict :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store := pinPilsStore payloadPresent recorded
  -- Run the predicate concretely and match on *which* reject fired: `.assert` is the spec's
  -- own guard, anything else is our bug.
  match (isPayloadInclusionListSatisfied (map := treeMap) store pinPilsRoot : PinM Bool).run store with
  | .ok b _              => .verdict b
  | .error (.assert _) _ => .assertReject
  | .error _ _           => .otherReject

-- verified + recorded `false` ⇒ `false` (do not extend this payload).
#guard pinPils true (some false) = .verdict false
-- verified + recorded `true` ⇒ `true`.
#guard pinPils true (some true) = .verdict true
-- unverified (root ∉ payloads) ⇒ `false`, even with the satisfaction bit recorded `true`.
#guard pinPils false (some true) = .verdict false
-- verified but no recorded entry ⇒ the spec's `assert root ∈ payload_inclusion_list_satisfaction`
-- now *rejects* (a state the invariant rules out) rather than reading a `lookupD` default. The
-- `.assertReject` (over a bare "it threw") is what a regression to `.missingKey` would break.
#guard pinPils true none = .assertReject
-- unverified AND no recorded entry ⇒ still the spec's assert, because
-- `assert root in store.payload_inclusion_list_satisfaction` precedes the verified check
-- (`heze/fork-choice.md:199-212`). A model that tested `is_payload_verified` first would answer
-- `.verdict false` here, and the other three quadrants could not tell the difference.
#guard pinPils false none = .assertReject

/-! ### Build-enforced pins (vectorless): the FOCIL fork-choice helpers

`get_inclusion_list_due_ms`, `record_payload_inclusion_list_satisfaction`, and `on_inclusion_list`
ship no conformance vector either. These drive them end-to-end so a future edit can't regress them
silently: the deadline constant, the recorded EL verdict, and the timeliness bit `on_inclusion_list`
threads into `process_inclusion_list`. -/

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

/-- The faithful empty-committee throw. Over a zero-validator `default BeaconState` (at `slot :=
1`, so the `state.slot != 0` underflow throw does not fire), `slot - 1`'s beacon committee is
empty, so `getInclusionListCommittee` (reached through the record path) hits the empty-committee
guard and rejects. Pyspec raises `ZeroDivisionError` on the same `indices[i % 0]`, an uncaught
fault, so the pin checks the reject is NOT an expected rejection (a `.transition (.arithmetic …)`,
not a caught `.assert`), the property a regression to `assert` would break. This is the throw the
populated `pinRecordSatisfied` / `pinRecordRefuted` below deliberately avoid. `State` is
FFI-backed (`FastBox`), so `native_decide`. -/
private def pinCommitteeThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox ({ (default : @EthCLSpecs.Heze.BeaconState minimal) with slot := 1 })
  let store := pinPilsStore false none
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store state pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .ok _ _    => false
  | .error e _ => !e.isExpectedRejection
example : pinCommitteeThrows = true := by native_decide

/-- A minimal populated `BeaconState`: `SLOTS_PER_EPOCH` active validators at `slot := 1`. Enough
that slot-0's beacon committee is non-empty (`computeCommittee` takes the shuffled slice
`[0, N // SLOTS_PER_EPOCH) = [0, 1)`), so the record path's `getInclusionListCommittee` clears its
empty-committee guard instead of throwing. A `default` validator has `exitEpoch = 0`, hence
inactive, so only `exitEpoch := farFutureEpoch` is overridden (`is_active_validator` needs
`activationEpoch ≤ epoch < exitEpoch`, and `activationEpoch` is already `0`). Effective balance is
irrelevant here: `computeCommittee` is a plain shuffled slice, not balance-weighted. The registry
is pushed onto the empty `base.validators` so the `SSZList` element type is inferred, never spelled.
-/
private def pinPopulatedState : @EthCLSpecs.Heze.BeaconState minimal :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  let base := (default : @EthCLSpecs.Heze.BeaconState minimal)
  let activeValidator : Validator := { (default : Validator) with exitEpoch := Const.farFutureEpoch }
  let vals := (Array.replicate Const.slotsPerEpoch activeValidator).foldl (·.push ·) base.validators
  { base with slot := 1, validators := vals }

/-- `record_payload_inclusion_list_satisfaction` records the engine verdict at `root`: with
the optimistic default (`isInclusionListSatisfied = true`) it writes `true`. `slot := 1` clears the
`state.slot != 0` underflow throw, and the populated validator set (`pinPopulatedState`)
gives `slot - 1` a non-empty beacon committee, so the record path runs end-to-end through
`getInclusionListCommittee` without hitting its empty-committee throw. The recorded verdict is
`true` regardless of the required transactions (the optimistic oracle ignores `ilTxs`), so what
this pin fixes is the record path writing the verdict at the right key.

Lean mechanics: the forkdef wants the boxed `State` (`State = SSZ.Box HasherTag.H
BeaconState`), so `state` is a `FastBox` of `pinPopulatedState`. `FastBox` is
FFI-backed, so this is a `native_decide` `example` (`Lean.ofReduceBool`). -/
private def pinRecordSatisfied : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox pinPopulatedState
  let store := pinPilsStore false none
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store state pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .ok after _ => FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot
  | .error _ _  => none
example : pinRecordSatisfied = some true := by native_decide

/-- The recorded verdict and the gate's answer, or the reject that fired. Keeping `threw`
separate is the whole point: the *gate* arm is where a tuple collapses, since a throw from
`isPayloadInclusionListSatisfied` would hand back `(some false, false)`, byte-identical to the
legitimate refusal this pin exists to check. The record-path arm was already distinguishable
(`(none, false)`); this makes both so. -/
private inductive RecordVerdict where
  /-- The record path completed: the stored bit and the gate's verdict. -/
  | recorded (value : Option Bool) (gate : Bool)
  /-- Either the record path or the gate rejected. -/
  | threw
  deriving DecidableEq

/-- The discriminating counterpart to `pinRecordSatisfied`: the same record path under a
*refuting* engine, a local `letI` instance answering `false` in place of the optimistic
default (`EthCLLib.Spec.Engine` documents the design). The record path writes `false` at a
*verified* `root`, and `isPayloadInclusionListSatisfied` then refuses to extend it. That
covers the branch every conformance vector leaves dead, end-to-end: oracle → recorded
verdict → gate. `pinPilsStore true none` puts `root ∈ payloads`, so the membership check
passes and the recorded bit is what decides. `State` is FFI-backed (`FastBox`), so
`native_decide`. -/
private def pinRecordRefuted : RecordVerdict :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : ExecutionEngine (@EthCLSpecs.Heze.ExecutionPayload minimal) Transaction
      (@EthCLSpecs.Heze.ExecutionRequests minimal) :=
    { isInclusionListSatisfied := fun _ _ => false
      verifyAndNotifyNewPayload := fun _ _ _ _ => true }
  -- Slot 1 clears the faithful underflow assert and the populated set clears the empty-committee
  -- throw (see `pinRecordSatisfied` / `pinPopulatedState`).
  let state : State := SSZ.FastBox pinPopulatedState
  let store := pinPilsStore true none
  match (recordPayloadInclusionListSatisfaction (map := treeMap) store state pinPilsRoot
      (default : @EthCLSpecs.Heze.ExecutionPayload minimal) : PinM (Store treeMap)).run store with
  | .error _ _  => .threw
  | .ok after _ =>
    let recorded := FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot
    match (isPayloadInclusionListSatisfied (map := treeMap) after pinPilsRoot : PinM Bool).run after with
    | .ok gate _  => .recorded recorded gate
    | .error _ _  => .threw
-- refuting oracle ⇒ recorded `false`, and the gate rejects the verified payload.
example : pinRecordRefuted = .recorded (some false) false := by native_decide

/-- `on_inclusion_list` threads the slot-timeliness bit into `process_inclusion_list`: a list
received before `INCLUSION_LIST_DUE_BPS` is filed timely, one at/after the deadline untimely. Runs
the handler end-to-end on a minimal store whose `time` puts `timeIntoSlotMs` below vs at the
`getInclusionListDueMs = 4000` deadline, then reads the stored timeliness bit back at `htr il`.
`process_inclusion_list` files the default list on branch (C), computing `htr` (FFI `Sha256`), so
this is a `native_decide` `example` (`Lean.ofReduceBool`). -/
private def pinOnIlTimely (time : UInt64) : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let signed : @SignedInclusionList minimal := default
  match runOn { pinPilsStore false none with time := time }
      (onInclusionList (map := treeMap) signed : EStateM StoreTransitionError (Store treeMap) Unit) with
  | .ok after => FcMap.lookup after.inclusionListStore.inclusionListTimeliness (htr signed.message)
  | .error _  => none
-- time 0: timeIntoSlotMs = 0 < 4000 ⇒ timely.
example : pinOnIlTimely 0 = some true := by native_decide
-- time 4: timeIntoSlotMs = 4000, not < 4000 ⇒ untimely.
example : pinOnIlTimely 4 = some false := by native_decide

/-! ### Build-enforced pins for the inclusion-list store (vectorless)

FOCIL has no conformance vector (the module docstring carries the coverage story), so these
pin `process_inclusion_list`'s three branches and
`get_inclusion_list_transactions`'s comprehension to hand-derived outcomes. They build a small
`InclusionListStore treeMap` (deterministic key order) under the minimal preset and the FFI
hasher. The branch-(A)/(B) pins and every `collectInclusionListTransactions` pin are
hash-free, so kernel `#guard`; the branch-(C) pin computes `htr` (FFI `Sha256`), so it is a
`native_decide` `example` (`Lean.ofReduceBool`), per the project's hash-tactic rule. -/

private def pinKey : Root := Vector.replicate 32 7
private def pinDummyRoot : Root := Vector.replicate 32 1
private def pinAltRoot : Root := Vector.replicate 32 2

/-- A transaction holding the single byte `b` (enough to make two transactions compare
unequal for the dedup pins). -/
private def pinTx (b : UInt8) : Transaction := sszOfArray #[b]

/-- An inclusion list from validator `v` over committee `pinKey`, carrying `txs`. The `letI`
fixes the preset so the anonymous constructor can synthesize it (a return-type annotation alone
does not flow into instance resolution for `{ … }`). -/
private def pinIL (v : ValidatorIndex) (txs : Array Transaction) : @InclusionList minimal :=
  letI : Preset := minimal
  { slot := 0, validatorIndex := v, inclusionListCommitteeRoot := pinKey, transactions := sszOfArray txs }

/-- Number of inclusion lists stored under `pinKey`. The `letI`s supply the store's preset /
hasher for the field projection (Lean re-synthesizes them rather than reading the argument's
fixed type). -/
private def pinNumStored (s : @InclusionListStore minimal treeMap fastHasherTag) : Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  ((FcMap.lookup s.inclusionLists pinKey).getD FcMap.empty |> FcMap.keys).length
/-- The equivocator set recorded under `pinKey`. -/
private def pinEquivs (s : @InclusionListStore minimal treeMap fastHasherTag) : Array ValidatorIndex :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  FcMap.lookupD s.equivocators pinKey

/-- A store already holding one inclusion list from validator 5, filed under an arbitrary root
(branch (B) never rehashes the stored list, so the key is free). Shared by the two branch-(B)
pins. -/
private def pinStoreB : @InclusionListStore minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { inclusionLists := FcMap.insert FcMap.empty pinKey (FcMap.insert FcMap.empty pinDummyRoot (pinIL 5 #[pinTx 0xAA])),
    inclusionListTimeliness := FcMap.insert FcMap.empty pinDummyRoot true,
    equivocators := FcMap.empty }

-- Branch (A): a list from a validator already in `equivocators[key]` is ignored; nothing is
-- stored and the equivocator set is untouched. Hash-free, so kernel `#guard`. Returns
-- (stored count, equivocator count); expected (0, 1).
private def pinResA : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store : InclusionListStore treeMap :=
    { InclusionListStore.empty with equivocators := FcMap.insert FcMap.empty pinKey #[5] }
  let after := processInclusionList store (pinIL 5 #[pinTx 0xAA]) true
  (pinNumStored after, (pinEquivs after).size)
#guard pinResA = (0, 1)

-- Branch (B), conflict: a second, differing list from validator 5 adds 5 to `equivocators[key]`
-- and stores nothing new. Returns (equivocators, stored count); expected (#[5], 1).
private def pinResBConflict : Array ValidatorIndex × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinIL 5 #[pinTx 0xBB]) true
  (pinEquivs after, pinNumStored after)
#guard pinResBConflict = (#[5], 1)

-- Branch (B), match: re-receiving the *same* list is a no-op. Returns (equivocator count,
-- stored count); expected (0, 1).
private def pinResBMatch : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinIL 5 #[pinTx 0xAA]) true
  ((pinEquivs after).size, pinNumStored after)
#guard pinResBMatch = (0, 1)

-- Branch (C): the first list from a validator is stored (one entry under `key`) with its
-- timeliness recorded under `htr inclusion_list`. Reads the bit back at the actual `htr il` key
-- (not just its presence), so a flipped `insert … (!isTimely)` fails; the stored-count half pins
-- that branch (C) filed exactly one list. Computes `htr` (FFI `Sha256`), so `native_decide`
-- `example`s. Returns (stored count, timeliness at `htr il`); expected (1, some isTimely).
private def pinResC (isTimely : Bool) : Nat × Option Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store : InclusionListStore treeMap := InclusionListStore.empty
  let il := pinIL 5 #[pinTx 0xAA]
  let after := processInclusionList store il isTimely
  (pinNumStored after, FcMap.lookup after.inclusionListTimeliness (htr il))
example : pinResC true = (1, some true) := by native_decide
example : pinResC false = (1, some false) := by native_decide

-- `collectInclusionListTransactions` (the `get_inclusion_list_transactions` comprehension).
-- Two stored lists: validator 5 → [0xAA], validator 6 → [0xAA, 0xBB], timeliness 5=true /
-- 6=false. Pins worked out by hand from the comprehension. All hash-free, kernel `#guard`.
private def pinLists : treeMap Root (@InclusionList minimal) :=
  FcMap.insert (FcMap.insert FcMap.empty pinDummyRoot (pinIL 5 #[pinTx 0xAA]))
    pinAltRoot (pinIL 6 #[pinTx 0xAA, pinTx 0xBB])
private def pinTimeliness : treeMap Root Bool :=
  FcMap.insert (FcMap.insert FcMap.empty pinDummyRoot true) pinAltRoot false

/-- Run the comprehension over `pinLists` / `pinTimeliness` under the minimal preset, so the
hash-free `#guard`s below need no ambient instance. `collectInclusionListTransactions` throws on
the `timeliness` plain-`Dict` read, and `pinTimeliness` carries an entry for every `pinLists`
key, so the reject is unreachable here. That is exactly why the reject must stay visible in the
result type: collapsing it to `#[]` would let a throw satisfy any future case that is
legitimately empty. The `#guard`s below compare through the `Except`. -/
private def pinCollect (equiv : Array ValidatorIndex) (onlyTimely : Bool) :
    Except StoreTransitionError (Array Transaction) :=
  letI : Preset := minimal
  collectInclusionListTransactions pinLists equiv pinTimeliness onlyTimely

/-- `p` applied to the collected transactions, and `false` when the comprehension rejected. The
reject failing every predicate is the point: folding it to `#[]` instead let a throw satisfy any
claim about an empty result. -/
private def pinCollectSat (equiv : Array ValidatorIndex) (onlyTimely : Bool)
    (p : Array Transaction → Bool) : Bool :=
  match pinCollect equiv onlyTimely with
  | .ok txs  => p txs
  | .error _ => false

-- No equivocators, timeliness ignored: union of {0xAA} and {0xAA, 0xBB}, deduped to two.
#guard pinCollectSat #[] false (·.size == 2)
#guard pinCollectSat #[] false (·.contains (pinTx 0xAA))
#guard pinCollectSat #[] false (·.contains (pinTx 0xBB))
-- only_timely drops validator 6's untimely list, leaving just {0xAA}.
#guard pinCollectSat #[] true (·.size == 1)
#guard pinCollectSat #[] true (·.contains (pinTx 0xAA))
-- Equivocator 6 is filtered out regardless of timeliness, leaving just {0xAA}.
#guard pinCollectSat #[6] false (·.size == 1)
#guard pinCollectSat #[6] false (·.contains (pinTx 0xAA))

/-- Vectorless reject pin for `get_forkchoice_store`'s opening assert
(`assert anchor_block.state_root == hash_tree_root(anchor_state)`, `fork-choice.md:141`). The
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
