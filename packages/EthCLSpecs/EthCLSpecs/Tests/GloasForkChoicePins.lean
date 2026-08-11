import EthCLSpecs.Gloas.ForkChoice

/-!
# `EthCLSpecs.Tests.GloasForkChoicePins`: the Gloas fork-choice build-enforced pins

The vectorless pins for Gloas's fork choice: reject branches and helper values no
conformance vector reaches, locked by `#guard` / `native_decide` so a regression fails
the build rather than passing silently.

They live in `EthCLSpecsTests` rather than beside the declarations they pin. The
lakefile already declares that library for exactly this content, and a pin compiled
into `EthCLSpecs` is shipped weight: `native_decide` bakes its evaluation into the
shipped module, and a consumer importing the fork body pays for checks that only the
build gate reads. The pinned declarations are all public, so nothing is lost by the
move except adjacency.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasForkChoicePins

-- Inside `namespace EthCLSpecs.Gloas`, where these pins used to sit, the fork's own
-- `Store` / `State` beat the `open EthCLSpecs.Fulu` above it. Out here neither wins, so
-- the Fulu names that Gloas redeclares are hidden and the rest (`Preset`, `Config`,
-- `minimal`, `Root`, ...) come through as before.
open EthCLSpecs.Gloas
open EthCLSpecs.Fulu hiding Store State fcZeroRoot Checkpoint

/-! ### Build-enforced pins (vectorless): the PTC replay rejects

The replay conversions' reject branches are unreachable by conformance vectors (the
generators cannot ship the pyspec `KeyError` case), so they are locked here, the
same pattern as Heze's inclusion-list pins. `pinStore` mirrors Heze's
`pinPilsStore` without the two FOCIL fields. -/

/-- The pins' concrete fork-choice monad: the minimal preset over the deterministic
`treeMap` and the FFI hasher. -/
private abbrev PinM := EStateM StoreTransitionError (@Store minimal treeMap fastHasherTag)

private def pinRoot : Root := Vector.replicate 32 9

/-- A minimal empty Gloas `Store`: every field empty/zero, mirroring the
`getForkchoiceStore` literal. The `letI`s fix the preset / hasher so the anonymous
`Store` constructor synthesizes them. -/
private def pinStore : @Store minimal treeMap fastHasherTag :=
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
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty }

/-- `recordPtcVotes` rejects (`missingKey`) when the per-block vote maps carry no
entry for the attested root, the pinned plain-`Dict` read; the pre-conversion
`lookupD` silently defaulted to `#[]` and the writes no-opped. `FcMap` only
(hash-free), so kernel `#guard`. -/
private def pinRecordPtcVotesThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let data : PayloadAttestationData := { (default : PayloadAttestationData) with beaconBlockRoot := pinRoot }
  match (recordPtcVotes (map := treeMap) pinStore data #[0] : PinM (Store treeMap)).run pinStore with
  | .error (.missingKey _) _ => true
  | _ => false
#guard pinRecordPtcVotesThrows = true

/-- The routed replay throw, end-to-end: `notifyPtcMessages` over a state at
`slot := 1` (zeroed `ptc_window`, so the PTC is all validator 0; alpha.11 `get_ptc`
is a plain window read) and a one-bit payload attestation whose `beacon_block_root`
the store does not know rejects with the wire handler's `.assert` (the pinned
`assert data.beacon_block_root in store.block_states` membership assert, a
`getOrAssert` miss), where the pre-conversion replay silently skipped the
message. This locks the routing itself: the replay path IS
`on_payload_attestation_message (is_from_block = true)`. `State` is FFI-backed
(`FastBox`), so `native_decide`. -/
private def pinReplayThrows : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  -- The handler wants a `CryptoBackend` for its wire-path signature check; the
  -- block-replay path (`is_from_block = true`) never reaches it, but elaboration does.
  letI : CryptoBackend := CryptoBackend.realBackend
  let state : State := SSZ.FastBox ({ (default : @EthCLSpecs.Gloas.BeaconState minimal) with slot := 1 })
  let pa : PayloadAttestation := { (default : PayloadAttestation) with
    aggregationBits := bitSet default 0 true
    data := { (default : PayloadAttestationData) with beaconBlockRoot := pinRoot, slot := 1 } }
  match (notifyPtcMessages (map := treeMap) state #[pa] : PinM Unit).run pinStore with
  | .error (.assert _) _ => true
  | _ => false
example : pinReplayThrows = true := by native_decide

/-- The target-checkpoint advance propagates a `process_slots` reject. The fixture
state is `default` (zero validators, slot 0) carrying one queued
`PendingConsolidation`: advancing to epoch 1's start slot reaches
`process_pending_consolidations`, whose `state.validators[source_index]` read is a
pinned plain-list read (pyspec `IndexError`), so the epoch step rejects with
`outOfBounds` and the unguarded pinned `process_slots` means
`store_target_checkpoint_state` re-throws it (`.transition`) with nothing cached. This
pins the propagation semantics; the throw site inside epoch processing is incidental. The
consolidation carrier is deliberate: a bare zero-validator advance does NOT reject,
it grinds through `cbwsAux`'s 10M-iteration fuel in the proposer lookahead, so the
reject must land earlier in the epoch pipeline. `State` is FFI-backed (`FastBox`),
so `native_decide`. -/
private def pinTargetAdvanceRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  -- `process_slots` runs the state machine, whose section wants a `CryptoBackend`.
  letI : CryptoBackend := CryptoBackend.realBackend
  let bs : @EthCLSpecs.Gloas.BeaconState minimal :=
    { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
      pendingConsolidations := sszOfArray #[{ sourceIndex := 0, targetIndex := 0 }] }
  let state : State := SSZ.FastBox bs
  let store := { pinStore with blockStates := FcMap.insert FcMap.empty pinRoot state }
  let target : Checkpoint := { epoch := 1, root := pinRoot }
  match (storeTargetCheckpointState (map := treeMap) store target : PinM (Store treeMap)).run store with
  -- Match the constructor, not the wrapper: `.transition` also spans `.arithmetic`, an uncaught
  -- fault that would fail the very step this fixture pins as an expected rejection. The pin has
  -- to break when the reject class changes, which is what Leo's note 3 asked for.
  | .error (.transition (.outOfBounds _ _)) _ => true
  | _ => false
example : pinTargetAdvanceRejects = true := by native_decide

/-- `getBlockRootAtSlot` rejects (`.assert`) the restored recency guard `slot <
state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT`: a `default` state has slot 0, so
`get_block_root_at_slot(state, 0)` fails `0 < 0` where the pre-restore accessor
mod-indexed silently. This locks the assert itself; the end-to-end
`compute_pulled_up_tip` pjf reachability it opens up is conformance-gated rather than
pinned (the epoch-boundary near-zero-stake fixture is finicky to construct). `State` is
FFI-backed, so `native_decide`. -/
private def pinBlockRootRecencyRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Gloas.BeaconState minimal)
  match (getBlockRootAtSlot state 0 : EStateM StateTransitionError State Root).run state with
  | .error (.assert _) _ => true
  | _ => false
example : pinBlockRootRecencyRejects = true := by native_decide

/-- `verifyExecutionPayloadEnvelopeSignature` rejects (`.transition (.outOfBounds …)`) an
out-of-range `builder_index`: a `default` state has an empty `builders` registry, so an
envelope with `builder_index = 1` (not the self-build sentinel `UINT64_MAX`) reads
`state.builders[1]`, which the spec's `IndexError` surfaces through `sszGetIdx` where the
former `[i]!` would have panicked. The read throws before `bls.Verify`, so no backend runs.
`State` is FFI-backed, so `native_decide`. -/
private def pinEnvelopeSigBuilderOob : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Gloas.BeaconState minimal)
  let signedEnv : SignedExecutionPayloadEnvelope :=
    { (default : SignedExecutionPayloadEnvelope) with
      message := { (default : ExecutionPayloadEnvelope) with builderIndex := 1 } }
  match verifyExecutionPayloadEnvelopeSignature state signedEnv with
  | .error (.transition (.outOfBounds _ _)) => true
  | _ => false
example : pinEnvelopeSigBuilderOob = true := by native_decide

/-! ### The execution-layer seams, refuted

Both verdicts default to `true`, so every conformance vector runs the accepting branch and
the refuting one is dead to the suite. These pin that the branch exists and that the verdict
comes from the seam: the same call under the two instances, once each way. `pinRecordRefuted`
does this for Heze's FOCIL gate; this is the pair for Gloas's two.

Value pins rather than end-to-end reject pins. Both asserts raise `.assert`, and so does
every other assert on the envelope path, so a handler-level pin would match on a class it
shares with the asserts around it and pass whether or not the seam was consulted. The
handler wiring is a one-line `assert` over the wrapper each pin drives. -/

/-- The pair of engine verdicts under the optimistic default. Pure `Bool`s off the seam, no
hashing, so kernel `#guard` closes them. -/
private def pinEngineOptimistic : Bool × Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  (verifyAndNotifyNewPayload (default : @EthCLSpecs.Gloas.ExecutionPayload minimal) #[]
     (Vector.replicate 32 0) (default : @EthCLSpecs.Gloas.ExecutionRequests minimal),
   isDataAvailable (Vector.replicate 32 0))

#guard pinEngineOptimistic = (true, true)

/-- The same two calls under refuting instances. A `letI` at the concrete fork types
overrides the global optimistic instance, which is the override a consumer wiring a real EL
writes. Both flip, so neither wrapper is a constant. -/
private def pinEngineRefuted : Bool × Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : ExecutionEngine (@EthCLSpecs.Gloas.ExecutionPayload minimal) Transaction
      (@EthCLSpecs.Gloas.ExecutionRequests minimal) :=
    { isInclusionListSatisfied := fun _ _ => true
      verifyAndNotifyNewPayload := fun _ _ _ _ => false }
  letI : DataAvailability := { isDataAvailable := fun _ => false }
  (verifyAndNotifyNewPayload (default : @EthCLSpecs.Gloas.ExecutionPayload minimal) #[]
     (Vector.replicate 32 0) (default : @EthCLSpecs.Gloas.ExecutionRequests minimal),
   isDataAvailable (Vector.replicate 32 0))

#guard pinEngineRefuted = (false, false)

end EthCLSpecs.Tests.GloasForkChoicePins
