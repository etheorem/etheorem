import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Operations
import EthCLSpecs.Heze.Withdrawals
import EthCLSpecs.Heze.Transition
import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Heze.Interface`: the Heze fork-interface instance

Heze's implementation of `ForkInterface`, the entry points the pyspec runner drives
(`SPEC_AUTHORING_MODEL.md` §11). At v1.7.0-alpha.11 EIP-7805 (FOCIL) adds no state transition
and no vector-tested fork-choice change. Its fork-choice overrides do run on the existing
fork_choice vectors, but only on the path where the inclusion-list store stays empty, which
behaves exactly like Gloas; the FOCIL-specific behavior ships no vector. So every dynamic
runner reuses the Gloas spine re-instantiated over Heze types (`Heze.EpochProcessing` /
`Operations` / `Withdrawals` / `Transition` / `ForkChoice`).

The Heze-specific entries: `runUpgrade` is the Gloas→Heze `fork` format (a pure field copy,
see `upgradeToHeze`); `runTransition` is the Gloas→Heze boundary; `runForkChoice` runs the
Heze ePBS store. `runGenesis` and any `ssz_static` type Heze does not model report
`outOfScope`, a deliberate skip rather than xfail work, matching Fulu / Gloas. Pinned to
v1.7.0-alpha.11.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open EthCLSpecs.Fulu
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Heze.Interface

/-- Pinned upstream release; Heze tracks the same tag as Fulu / Gloas. -/
def pyspecPinnedVersion : String := "v1.7.0-alpha.11"

/-- `stateRoot`: decode a Heze `BeaconState` at preset `P` and take its root. -/
private def stateRootImpl (P : Preset) (bytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  match SSZ.deserialize (T := @Heze.BeaconState P) bytes with
  | .ok v    => .ok (htr v)
  | .error _ => .error (.decode "BeaconState")

/-- `runUpgrade` (the `fork` format, Gloas→Heze): decode the Gloas pre-state at preset `P`,
apply `upgradeToHeze` with the config's `HEZE_FORK_VERSION`, return the Heze post root. A
pure field copy; `upgradeToHeze`'s docstring carries the why. -/
private def runUpgradeImpl (P : Preset) (forkVersion : Version) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  match SSZ.deserialize (T := @Gloas.BeaconState P) preBytes with
  | .ok pre  => .ok (htr (upgradeToHeze forkVersion pre))
  | .error _ => .error (.decode "Gloas BeaconState")

/-- Decode a Heze `BeaconState` into a `FastBox`, or the runner's `decode` error. -/
private def decodeState (P : Preset) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (SSZ.Box Sha256 (@Heze.BeaconState P)) :=
  letI : Preset := P
  match SSZ.FastBox.deserialize (T := @Heze.BeaconState P) bytes with
  | .ok box  => .ok box
  | .error _ => .error (.decode "BeaconState")

/-- `runEpochSubstep`: dispatch the `epoch_processing/<handler>` name to its Heze substep,
run it over the decoded Heze pre-state, return the post root. Every substep is the Gloas
one re-instantiated over Heze. -/
private def runEpochSubstepImpl (P : Preset) (C : Config) (step : EpochStep) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Heze.BeaconState P)) Unit :=
    match step with
    | .slashingsReset               => processSlashingsReset
    | .randaoMixesReset             => processRandaoMixesReset
    | .eth1DataReset                => processEth1DataReset
    | .historicalSummariesUpdate    => processHistoricalSummariesUpdate
    | .participationFlagUpdates     => processParticipationFlagUpdates
    | .justificationAndFinalization => processJustificationAndFinalization
    | .inactivityUpdates            => processInactivityUpdates
    | .rewardsAndPenalties          => processRewardsAndPenalties
    | .registryUpdates              => processRegistryUpdates
    | .slashings                    => processSlashings
    | .effectiveBalanceUpdates      => processEffectiveBalanceUpdates
    | .pendingDeposits              => processPendingDeposits
    | .pendingDepositsChurn         => processPendingDeposits
    | .pendingConsolidations        => processPendingConsolidations
    | .builderPendingPayments       => processBuilderPendingPayments
    | .syncCommitteeUpdates         => processSyncCommitteeUpdates
    | .proposerLookahead            => processProposerLookahead
    | .ptcWindow                    => processPtcWindow
  RunError.ofSpec (runToRoot box0 action)

/-- `runRewards`: the four reward-delta blobs computed by the inherited Heze delta
functions. The `Deltas` container is Fulu's (fork-agnostic). -/
private def runRewardsImpl (P : Preset) (C : Config) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) (Array ByteArray) := do
  let state ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  let mkDeltas : Array Gwei × Array Gwei → ByteArray := fun rp =>
    SSZ.serialize ({ rewards := sszOfArray rp.1, penalties := sszOfArray rp.2 } : Fulu.Deltas)
  let n := (sszGet state validators).size
  let zeros := Array.replicate n (0 : Gwei)
  RunError.ofSpec do
    let d0 ← liftErr (getFlagIndexDeltas state 0)
    let d1 ← liftErr (getFlagIndexDeltas state 1)
    let d2 ← liftErr (getFlagIndexDeltas state 2)
    pure #[mkDeltas d0, mkDeltas d1, mkDeltas d2, mkDeltas (zeros, getInactivityPenaltyDeltas state)]

/-- Decode a plain (non-boxed) SSZ operation value. -/
private def decodeOp (T : Type) [SizzLean.SSZRepr T] (b : ByteArray) :
    Except (RunError StateTransitionError) T :=
  match SSZ.deserialize (T := T) b with
  | .ok v    => .ok v
  | .error _ => .error (.decode "operation")

/-- `runOperation`: dispatch every operation handler over the decoded Heze pre-state. Each
handler is the Gloas one re-instantiated over Heze. -/
private def runOperationImpl (P : Preset) (C : Config) (kind : OpKind)
    (preBytes opBytes : ByteArray) (cmeta : CaseMeta) : Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let dispatch : Except (RunError StateTransitionError) (EStateM StateTransitionError (SSZ.Box Sha256 (@Heze.BeaconState P)) Unit) :=
    match kind with
    | .proposerSlashing       => (decodeOp (@ProposerSlashing P) opBytes).map processProposerSlashing
    | .attesterSlashing       => (decodeOp (@AttesterSlashing P) opBytes).map processAttesterSlashing
    | .attestation            => (decodeOp (@Attestation P) opBytes).map processAttestation
    | .payloadAttestation     => (decodeOp (@PayloadAttestation P) opBytes).map processPayloadAttestation
    | .executionPayloadBid    => (decodeOp (@SignedExecutionPayloadBid P) opBytes).map processExecutionPayloadBid
    | .parentExecutionPayload => (decodeOp (@BeaconBlock P) opBytes).map processParentExecutionPayload
    | .blockHeader            => (decodeOp (@BeaconBlock P) opBytes).map processBlockHeader
    | .withdrawals            => .ok processWithdrawals
    | .voluntaryExit          => (decodeOp (@SignedVoluntaryExit P) opBytes).map processVoluntaryExit
    | .voluntaryExitChurn     => (decodeOp (@SignedVoluntaryExit P) opBytes).map processVoluntaryExit
    | .blsToExecutionChange   => (decodeOp (@SignedBLSToExecutionChange P) opBytes).map processBlsToExecutionChange
    | .depositRequest         => (decodeOp (@DepositRequest P) opBytes).map processDepositRequest
    | .withdrawalRequest      => (decodeOp (@WithdrawalRequest P) opBytes).map processWithdrawalRequest
    | .consolidationRequest   => (decodeOp (@ConsolidationRequest P) opBytes).map processConsolidationRequest
    | .builderDepositRequest  => (decodeOp (@Heze.BuilderDepositRequest P) opBytes).map processBuilderDepositRequest
    | .builderExitRequest     => (decodeOp (@Heze.BuilderExitRequest P) opBytes).map processBuilderExitRequest
    | .syncAggregate          => (decodeOp (@SyncAggregate P) opBytes).map processSyncAggregate
    | .deposit | .executionPayload =>
        .error (.spec (.todo s!"heze operations/{reprStr kind}: not a standalone ePBS operation"))
  match dispatch with
  | .error e   => .error e
  | .ok action =>
    RunError.ofSpec (runToRoot box0 action)

/-- `runSlots`: advance the decoded Heze pre-state by `n` empty slots. -/
private def runSlotsImpl (P : Preset) (C : Config) (preBytes : ByteArray) (n : Nat) :
    Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Heze.BeaconState P)) Unit := do
    let state ← get
    processSlots ((sszGet state slot) + UInt64.ofNat n)
  RunError.ofSpec (runToRoot box0 action)

/-- `runBlocks` (`sanity/blocks`, `finality`, `random`): fold the Heze `state_transition`
over the decoded signed blocks. -/
private def runBlocksImpl (P : Preset) (C : Config) (preBytes : ByteArray)
    (blocks : Array ByteArray) (cmeta : CaseMeta) : Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  let signedBlocks ← blocks.mapM (fun bb =>
    match SSZ.deserialize (T := @Heze.SignedBeaconBlock P) bb with
    | .ok sb   => .ok sb
    | .error _ => .error (RunError.decode "Heze SignedBeaconBlock"))
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Heze.BeaconState P)) Unit := do
    for sb in signedBlocks do stateTransition sb
  RunError.ofSpec (runToRoot box0 action)

/-- `runTransition` (the `transition` format, Gloas→Heze): fold the pre-fork blocks under
Gloas `state_transition`, advance the Gloas state to the fork-epoch boundary, apply
`upgradeToHeze` (a pure copy, see its docstring), then fold the post-fork blocks under the
Heze spine. Unqualified spine names resolve to the Heze copies; the pre-fork Gloas calls are
qualified. -/
private def runTransitionImpl (P : Preset) (C : Config) (forkVersion : Version)
    (preBytes : ByteArray) (blocks : Array ByteArray) (cmeta : CaseMeta) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let forkEpoch := cmeta.forkEpoch.getD 0
  let boundary : Slot := UInt64.ofNat (forkEpoch * Const.slotsPerEpoch)
  let nPre := match cmeta.forkBlock with | some n => n + 1 | none => 0
  match SSZ.deserialize (T := @Gloas.BeaconState P) preBytes with
  | .error _ => .error (.decode "Gloas BeaconState")
  | .ok preGloas => do
    let preBlocks ← (List.range nPre).toArray.mapM (fun i =>
      match blocks[i]? with
      | none    => Except.error (RunError.spec (.outOfBounds i blocks.size))
      | some bb => match SSZ.deserialize (T := @Gloas.SignedBeaconBlock P) bb with
        | .ok sb   => Except.ok sb
        | .error _ => Except.error (RunError.decode "Gloas SignedBeaconBlock"))
    let postBlocks ← (blocks.extract nPre blocks.size).mapM (fun bb =>
      match SSZ.deserialize (T := @Heze.SignedBeaconBlock P) bb with
      | .ok sb   => Except.ok sb
      | .error _ => Except.error (RunError.decode "Heze SignedBeaconBlock"))
    let gloasBox0 : SSZ.Box Sha256 (@Gloas.BeaconState P) := SSZ.FastBox preGloas
    let gloasAction : EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit := do
      for sb in preBlocks do Gloas.stateTransition sb
      if (sszGet (← get) slot) < boundary then Gloas.processSlots boundary
    match gloasAction.run gloasBox0 with
    | .error e _ => Except.error (RunError.spec e)
    | .ok _ gloasSt =>
      let hezeBox0 : SSZ.Box Sha256 (@Heze.BeaconState P) := SSZ.FastBox (upgradeToHeze forkVersion gloasSt.view)
      let hezeAction : EStateM StateTransitionError (SSZ.Box Sha256 (@Heze.BeaconState P)) Unit := do
        for sb in postBlocks do
          if (sszGet (← get) slot) < sb.message.slot then processSlots sb.message.slot
          if cmeta.blsSetting != 2 then assert (verifyBlockSignature (← get) sb)
          processBlock sb.message
          let root ← getStateRoot
          assert (sb.message.stateRoot == bytesToRoot root)
      RunError.ofSpec (runToRoot hezeBox0 hezeAction)

/-- Fold the decoded fork-choice `steps` over the Heze store. Identical shape to Gloas's
interpreter, re-instantiated over Heze types: a `block` step runs `on_block` then replays
the block's own attestations / attester-slashings; `execution_payload` /
`payload_attestation_message` drive the two ePBS handlers; the checks read the head node's
payload status and the per-block PTC vote arrays. -/
private def fcInterpretHeze [Preset] [Config] [HasherTag] [CryptoBackend]
    (P : Preset) (store0 : Store hashMap) (steps : Array FcStep) : Except StoreTransitionError Unit := do
  let mut store : Store hashMap := store0
  for step in steps do
    match step with
    | .tick t =>
      store := (← checkStepValidity store true
        (runOn store (onTick (map := hashMap) (UInt64.ofNat t) : EStateM StoreTransitionError (Store hashMap) Unit)))
    | .block bytes _columns valid =>
      let outcome := decodeStepOr (α := @Heze.SignedBeaconBlock P) bytes "block" fun sb =>
        let action : EStateM StoreTransitionError (Store hashMap) Unit := do
          onBlock (map := hashMap) sb
          for a in sb.message.body.attestations do onAttestation (map := hashMap) a true
          for a in sb.message.body.attesterSlashings do onAttesterSlashing (map := hashMap) a
        runOn store action
      store := (← checkStepValidity store valid outcome)
    | .attestation bytes valid =>
      let outcome := decodeStepOr (α := @Attestation P) bytes "attestation" fun a =>
        runOn store (onAttestation (map := hashMap) a false : EStateM StoreTransitionError (Store hashMap) Unit)
      store := (← checkStepValidity store valid outcome)
    | .attesterSlashing bytes valid =>
      let outcome := decodeStepOr (α := @AttesterSlashing P) bytes "attester_slashing" fun a =>
        runOn store (onAttesterSlashing (map := hashMap) a : EStateM StoreTransitionError (Store hashMap) Unit)
      store := (← checkStepValidity store valid outcome)
    | .executionPayload bytes valid =>
      let outcome := decodeStepOr (α := @Heze.SignedExecutionPayloadEnvelope P) bytes "envelope" fun env =>
        runOn store (onExecutionPayloadEnvelope (map := hashMap) env : EStateM StoreTransitionError (Store hashMap) Unit)
      store := (← checkStepValidity store valid outcome)
    | .payloadAttestationMessage bytes valid =>
      let outcome := decodeStepOr (α := @Heze.PayloadAttestationMessage P) bytes "ptc message" fun msg =>
        runOn store (onPayloadAttestationMessage (map := hashMap) msg false : EStateM StoreTransitionError (Store hashMap) Unit)
      store := (← checkStepValidity store valid outcome)
    | .checkHead root slot =>
      let head := getHead store
      assert (head.root == root)
      let headSlot := match FcMap.lookup store.blocks head.root with | some b => b.slot.toNat | none => 0
      assert (headSlot == slot)
    | .checkHeadPayloadStatus status =>
      assert ((getHead store).payloadStatus.toNat == status)
    | .checkPayloadTimelinessVote blockRoot votes =>
      assert (FcMap.lookupD store.payloadTimelinessVote (bytesToRoot blockRoot) == votes)
    | .checkPayloadDataAvailabilityVote blockRoot votes =>
      assert (FcMap.lookupD store.payloadDataAvailabilityVote (bytesToRoot blockRoot) == votes)
    | .checkJustified epoch root =>
      assert (store.justifiedCheckpoint.epoch.toNat == epoch)
      assert (store.justifiedCheckpoint.root == root)
    | .checkFinalized epoch root =>
      assert (store.finalizedCheckpoint.epoch.toNat == epoch)
      assert (store.finalizedCheckpoint.root == root)
    | .checkBoost root =>
      assert (store.proposerBoostRoot == root)
    | .checkTime t => assert (store.time.toNat == t)
    | .checkGenesisTime t => assert (store.genesisTime.toNat == t)
    | .unsupported reason => throw (StoreTransitionError.todo reason)
    -- `get_proposer_head` is Gloas-Modified but not ported, and no alpha.11 vector exercises it;
    -- surface it as unmodeled (a `todo` xfail) rather than passing it vacuously. This arm makes
    -- the match exhaustive over `FcStep`, so a newly added constructor becomes a build error rather
    -- than a silent pass through a catch-all.
    | .checkProposerHead _ => throw (StoreTransitionError.todo "get_proposer_head check: not modeled")
  pure ()

/-- `runForkChoice` (Heze): decode the anchor state / block, build the ePBS store, and run
the step interpreter. -/
private def runForkChoiceImpl (P : Preset) (C : Config) (anchorStateBytes anchorBlockBytes : ByteArray)
    (steps : Array FcStep) : Except (RunError StoreTransitionError) Unit :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match SSZ.FastBox.deserialize (T := @Heze.BeaconState P) anchorStateBytes,
        SSZ.deserialize (T := @Heze.BeaconBlock P) anchorBlockBytes with
  | .error _, _ => .error (.decode "fork_choice anchor state")
  | _, .error _ => .error (.decode "fork_choice anchor block")
  | .ok anchorState, .ok anchorBlock =>
    RunError.ofSpec (fcInterpretHeze P (getForkchoiceStore anchorState anchorBlock) steps)

/-- The `ssz_static` per-type kernel: decode `bytes` as `T`, return its root paired with
the round-trip check (`reserialize == bytes`). -/
private def runStatic (T : Type) [SizzLean.SSZRepr T] (typeName : String) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (ByteArray × Bool) :=
  letI : HasherTag := fastHasherTag
  match SSZ.deserialize (T := T) bytes with
  | .ok v    => .ok ((htr v : ByteArray), SSZ.serialize v == bytes)
  | .error _ => .error (.decode typeName)

/-- `sszStatic`: the Gloas set retargeted to the Heze namespace, plus the FOCIL-new
`InclusionList` / `SignedInclusionList`. Types Heze does not model report `.outOfScope`
(skip), matching Fulu / Gloas. -/
private def sszStaticImpl (P : Preset) (typeName : String) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (ByteArray × Bool) :=
  match typeName with
  | "AttestationData"            => runStatic (@Heze.AttestationData P) typeName bytes
  | "Attestation"                => runStatic (@Heze.Attestation P) typeName bytes
  | "AttesterSlashing"           => runStatic (@Heze.AttesterSlashing P) typeName bytes
  | "BeaconBlock"                => runStatic (@Heze.BeaconBlock P) typeName bytes
  | "BeaconBlockBody"            => runStatic (@Heze.BeaconBlockBody P) typeName bytes
  | "BeaconBlockHeader"          => runStatic (@Heze.BeaconBlockHeader P) typeName bytes
  | "BeaconState"                => runStatic (@Heze.BeaconState P) typeName bytes
  | "BLSToExecutionChange"       => runStatic (@Heze.BLSToExecutionChange P) typeName bytes
  | "Builder"                    => runStatic (@Heze.Builder P) typeName bytes
  | "BuilderDepositRequest"      => runStatic (@Heze.BuilderDepositRequest P) typeName bytes
  | "BuilderExitRequest"         => runStatic (@Heze.BuilderExitRequest P) typeName bytes
  | "BuilderPendingPayment"      => runStatic (@Heze.BuilderPendingPayment P) typeName bytes
  | "BuilderPendingWithdrawal"   => runStatic (@Heze.BuilderPendingWithdrawal P) typeName bytes
  | "Checkpoint"                 => runStatic (@Heze.Checkpoint P) typeName bytes
  | "ConsolidationRequest"       => runStatic (@Heze.ConsolidationRequest P) typeName bytes
  | "Deposit"                    => runStatic (@Heze.Deposit P) typeName bytes
  | "DepositData"                => runStatic (@Heze.DepositData P) typeName bytes
  | "DepositRequest"             => runStatic (@Heze.DepositRequest P) typeName bytes
  | "Eth1Data"                   => runStatic (@Heze.Eth1Data P) typeName bytes
  | "ExecutionPayload"           => runStatic (@Heze.ExecutionPayload P) typeName bytes
  | "ExecutionPayloadBid"        => runStatic (@Heze.ExecutionPayloadBid P) typeName bytes
  | "ExecutionPayloadEnvelope"   => runStatic (@Heze.ExecutionPayloadEnvelope P) typeName bytes
  | "ExecutionRequests"          => runStatic (@Heze.ExecutionRequests P) typeName bytes
  | "Fork"                       => runStatic (@Heze.Fork P) typeName bytes
  | "HistoricalSummary"          => runStatic (@Heze.HistoricalSummary P) typeName bytes
  | "InclusionList"              => runStatic (@Heze.InclusionList P) typeName bytes
  | "IndexedAttestation"         => runStatic (@Heze.IndexedAttestation P) typeName bytes
  | "IndexedPayloadAttestation"  => runStatic (@Heze.IndexedPayloadAttestation P) typeName bytes
  | "PayloadAttestation"         => runStatic (@Heze.PayloadAttestation P) typeName bytes
  | "PayloadAttestationData"     => runStatic (@Heze.PayloadAttestationData P) typeName bytes
  | "PayloadAttestationMessage"  => runStatic (@Heze.PayloadAttestationMessage P) typeName bytes
  | "PendingConsolidation"       => runStatic (@Heze.PendingConsolidation P) typeName bytes
  | "PendingDeposit"             => runStatic (@Heze.PendingDeposit P) typeName bytes
  | "PendingPartialWithdrawal"   => runStatic (@Heze.PendingPartialWithdrawal P) typeName bytes
  | "ProposerSlashing"           => runStatic (@Heze.ProposerSlashing P) typeName bytes
  | "SyncAggregate"              => runStatic (@Heze.SyncAggregate P) typeName bytes
  | "SyncCommittee"              => runStatic (@Heze.SyncCommittee P) typeName bytes
  | "Validator"                  => runStatic (@Heze.Validator P) typeName bytes
  | "VoluntaryExit"              => runStatic (@Heze.VoluntaryExit P) typeName bytes
  | "Withdrawal"                 => runStatic (@Heze.Withdrawal P) typeName bytes
  | "WithdrawalRequest"          => runStatic (@Heze.WithdrawalRequest P) typeName bytes
  | "SignedBeaconBlock"          => runStatic (@Heze.SignedBeaconBlock P) typeName bytes
  | "SignedBeaconBlockHeader"    => runStatic (@Heze.SignedBeaconBlockHeader P) typeName bytes
  | "SignedBLSToExecutionChange" => runStatic (@Heze.SignedBLSToExecutionChange P) typeName bytes
  | "SignedExecutionPayloadBid"      => runStatic (@Heze.SignedExecutionPayloadBid P) typeName bytes
  | "SignedExecutionPayloadEnvelope" => runStatic (@Heze.SignedExecutionPayloadEnvelope P) typeName bytes
  | "SignedInclusionList"        => runStatic (@Heze.SignedInclusionList P) typeName bytes
  | "SignedVoluntaryExit"        => runStatic (@Heze.SignedVoluntaryExit P) typeName bytes
  | _ => .error (.spec (.outOfScope s!"ssz_static/{typeName}: not modeled by EthCLSpecs.Heze"))

/-- Heze's fork-interface instance at preset `P` / config `C` with `HEZE_FORK_VERSION`.
Every in-scope entry is driven via the inherited Gloas spine over Heze state; `runUpgrade`
is the pure Gloas→Heze copy and `runTransition` the Gloas→Heze boundary. `runGenesis` is
`outOfScope` (not modeled; no genesis vectors at the pin), as in Fulu / Gloas. -/
@[reducible] def hezeInterfaceFor (P : Preset) (C : Config) (forkVersion : Version) : ForkInterface where
  stateRoot       := stateRootImpl P
  sszStatic       := sszStaticImpl P
  runUpgrade      := runUpgradeImpl P forkVersion
  runEpochSubstep := runEpochSubstepImpl P C
  runRewards      := runRewardsImpl P C
  runForkChoice   := runForkChoiceImpl P C
  runOperation    := runOperationImpl P C
  runBlocks       := runBlocksImpl P C
  runSlots        := runSlotsImpl P C
  runGenesis      := fun _ _   => .error (.spec (.outOfScope "heze genesis: out of scope (not modeled)"))
  runTransition   := runTransitionImpl P C forkVersion

/-- The `minimal`-preset / config Heze interface. -/
@[reducible] def hezeInterface : ForkInterface := hezeInterfaceFor minimal minimalConfig hezeForkVersionMinimal

/-- The `mainnet`-preset / config Heze interface (on demand). -/
@[reducible] def hezeInterfaceMainnet : ForkInterface := hezeInterfaceFor mainnet mainnetConfig hezeForkVersionMainnet

end EthCLSpecs.Heze.Interface
