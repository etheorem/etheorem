import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Gloas.EpochProcessing
import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Gloas.Withdrawals
import EthCLSpecs.Gloas.Transition
import EthCLSpecs.Gloas.ForkChoice

/-!
# `EthCLSpecs.Gloas.Interface`: the Gloas fork-interface instance

Gloas's implementation of `ForkInterface`. Every in-scope entry is driven:
`stateRoot`, `runUpgrade` (the `fork` format: decode a Fulu pre-state, apply
`upgradeToGloas` + builder onboarding, compare the Gloas post root), the full
`runEpochSubstep` / `runOperation` surface (the EIP-7732 ePBS handlers included),
`runRewards`, `runBlocks` / `runSlots` (the ePBS block spine), `runTransition` (the
Fulu→Gloas boundary), and `runForkChoice` (the node-based ePBS fork choice with the
envelope and PTC-vote handlers). Only `runGenesis` stays `todo` (no genesis vectors
at the pin).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open EthCLSpecs.Fulu
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Gloas.Interface

/-- Pinned upstream release; Gloas tracks the same tag as Fulu while it is
pre-release. -/
def pyspecPinnedVersion : String := "v1.7.0-alpha.10"

/-- `stateRoot`: decode a Gloas `BeaconState` at preset `P` and take its root. -/
private def stateRootImpl (P : Preset) (bytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  match SSZ.deserialize (T := @Gloas.BeaconState P) bytes with
  | .ok v    => .ok (htr v)
  | .error _ => .error (.decode "BeaconState")

/-- `runUpgrade` (the `fork` format): decode the Fulu pre-state at preset `P`,
apply `upgradeToGloas` with the config's `GLOAS_FORK_VERSION`, run the builder
onboarding (`onboard_builders_from_pending_deposits`, which needs the Gloas
builder-registry helpers and a `[CryptoBackend]` for deposit-signature checks),
and return the Gloas post root. -/
private def runUpgradeImpl (P : Preset) (C : Config) (forkVersion : Version) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match SSZ.deserialize (T := @Fulu.BeaconState P) preBytes with
  | .ok pre  =>
    let box0 : SSZ.Box Sha256 (@Gloas.BeaconState P) := SSZ.FastBox (upgradeToGloas forkVersion pre)
    let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit :=
      onboardBuildersFromPendingDeposits
    RunError.ofSpec (runToRoot box0 action)
  | .error _ => .error (.decode "Fulu BeaconState")

/-- Decode a Gloas `BeaconState` into a `FastBox`, or the runner's `decode` error. -/
private def decodeState (P : Preset) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (SSZ.Box Sha256 (@Gloas.BeaconState P)) :=
  letI : Preset := P
  match SSZ.FastBox.deserialize (T := @Gloas.BeaconState P) bytes with
  | .ok box  => .ok box
  | .error _ => .error (.decode "BeaconState")

/-- `runEpochSubstep`: dispatch the `epoch_processing/<handler>` name to its
substep, run it over the decoded Gloas pre-state at the fast config, return the
post root. All substeps are wired: the Fulu ones inherited verbatim
(`EpochProcessing`), the EIP-8061 churn overrides, the shuffle-dependent ones (now
that the committees are inheritable), and the ePBS-new `builder_pending_payments`
and `ptc_window`. -/
private def runEpochSubstepImpl (P : Preset) (C : Config) (step : EpochStep) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit :=
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
    -- The EIP-8061 churn suite exercises the same substep body.
    | .pendingDepositsChurn         => processPendingDeposits
    | .pendingConsolidations        => processPendingConsolidations
    | .builderPendingPayments       => processBuilderPendingPayments
    | .syncCommitteeUpdates         => processSyncCommitteeUpdates
    | .proposerLookahead            => processProposerLookahead
    | .ptcWindow                    => processPtcWindow
  RunError.ofSpec (runToRoot box0 action)

/-- `runRewards`: the same four reward-delta blobs as Fulu, computed by the
inherited Gloas delta functions over the Gloas pre-state. The `Deltas` container is
reused from Fulu. -/
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

/-- `runOperation`: dispatch every operation handler over the decoded Gloas
pre-state. The non-ePBS handlers are inherited from Fulu (`Gloas.Operations`); the
ePBS-modified / ePBS-new ones are Gloas-specific: `proposer_slashing` (builder-payment
cleanup), payload-aware `attestation`, `payload_attestation`, the builder-aware
`withdrawals`, `execution_payload_bid`, `parent_execution_payload`, `block_header`,
and the builder-branch `voluntary_exit` / `deposit_request`. -/
private def runOperationImpl (P : Preset) (C : Config) (kind : OpKind)
    (preBytes opBytes : ByteArray) (cmeta : CaseMeta) : Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let dispatch : Except (RunError StateTransitionError) (EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit) :=
    match kind with
    | .proposerSlashing       => (decodeOp (@ProposerSlashing P) opBytes).map processProposerSlashing
    | .attesterSlashing       => (decodeOp (@AttesterSlashing P) opBytes).map processAttesterSlashing
    | .attestation            => (decodeOp (@Attestation P) opBytes).map processAttestation
    | .payloadAttestation     => (decodeOp (@PayloadAttestation P) opBytes).map processPayloadAttestation
    -- The bid / parent-payload handlers decode a full `BeaconBlock`, not a single
    -- operation container (the spec functions read `block.body` / `block.slot`).
    | .executionPayloadBid    => (decodeOp (@BeaconBlock P) opBytes).map processExecutionPayloadBid
    | .parentExecutionPayload => (decodeOp (@BeaconBlock P) opBytes).map processParentExecutionPayload
    | .blockHeader            => (decodeOp (@BeaconBlock P) opBytes).map processBlockHeader
    -- `process_withdrawals` (Gloas) takes no operand; it runs purely from state.
    | .withdrawals            => .ok processWithdrawals
    | .voluntaryExit          => (decodeOp (@SignedVoluntaryExit P) opBytes).map processVoluntaryExit
    -- Gloas-only suite exercising the EIP-8061 exit churn; same handler body.
    | .voluntaryExitChurn     => (decodeOp (@SignedVoluntaryExit P) opBytes).map processVoluntaryExit
    | .blsToExecutionChange   => (decodeOp (@SignedBLSToExecutionChange P) opBytes).map processBlsToExecutionChange
    | .depositRequest         => (decodeOp (@DepositRequest P) opBytes).map processDepositRequest
    | .withdrawalRequest      => (decodeOp (@WithdrawalRequest P) opBytes).map processWithdrawalRequest
    | .consolidationRequest   => (decodeOp (@ConsolidationRequest P) opBytes).map processConsolidationRequest
    | .syncAggregate          => (decodeOp (@SyncAggregate P) opBytes).map processSyncAggregate
    -- Handlers EIP-7732 does not drive as standalone Gloas operations.
    | .deposit | .executionPayload =>
        .error (.spec (.todo s!"gloas operations/{reprStr kind}: not a standalone ePBS operation"))
  match dispatch with
  | .error e   => .error e
  | .ok action =>
    RunError.ofSpec (runToRoot box0 action)

/-- `runSlots`: advance the decoded Gloas pre-state by `n` empty slots through the
Gloas `process_slots` (which runs the Gloas `process_epoch` at boundaries). -/
private def runSlotsImpl (P : Preset) (C : Config) (preBytes : ByteArray) (n : Nat) :
    Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit := do
    let state ← get
    processSlots ((sszGet state slot) + UInt64.ofNat n)
  RunError.ofSpec (runToRoot box0 action)

/-- `runBlocks` (`sanity/blocks`, `finality`, `random`): fold the Gloas
`state_transition` over the decoded signed blocks (verify-off at `bls_setting = 2`),
returning the post root. -/
private def runBlocksImpl (P : Preset) (C : Config) (preBytes : ByteArray)
    (blocks : Array ByteArray) (cmeta : CaseMeta) : Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  -- Decode the block sequence up front (both binds stay ahead of the `letI`s, which close
  -- the do-block into term context): a malformed block is a `decode` error, not a reject.
  let signedBlocks ← blocks.mapM (fun bb =>
    match SSZ.deserialize (T := @Gloas.SignedBeaconBlock P) bb with
    | .ok sb   => .ok sb
    | .error _ => .error (RunError.decode "Gloas SignedBeaconBlock"))
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit := do
    for sb in signedBlocks do stateTransition sb
  RunError.ofSpec (runToRoot box0 action)

/-- `runTransition` (the `transition` format, Fulu→Gloas): fold the pre-fork blocks
(indices `0..forkBlock`) under Fulu `state_transition`, advance the Fulu state to the
fork-epoch boundary (so the boundary `process_epoch` runs under Fulu rules), apply
`upgradeToGloas` + builder onboarding, then fold the post-fork blocks under Gloas
`state_transition`. A post-fork block landing exactly on the boundary slot skips the
slot advance (the upgrade already positioned the state there). -/
private def runTransitionImpl (P : Preset) (C : Config) (forkVersion : Version)
    (preBytes : ByteArray) (blocks : Array ByteArray) (cmeta : CaseMeta) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let forkEpoch := cmeta.forkEpoch.getD 0
  let boundary : Slot := UInt64.ofNat (forkEpoch * Const.slotsPerEpoch)
  let nFulu := match cmeta.forkBlock with | some n => n + 1 | none => 0
  match SSZ.deserialize (T := @Fulu.BeaconState P) preBytes with
  | .error _ => .error (.decode "Fulu BeaconState")
  | .ok preFulu => do
    -- Decode both block runs up front (the runner's job): the pre-fork blocks `0..nFulu`
    -- as Fulu, the post-fork blocks `nFulu..` as Gloas. `nFulu` comes from the case
    -- metadata (`forkBlock`), not `blocks.size`, so a missing pre-fork block is the real
    -- `outOfBounds i blocks.size` (a malformed input), while a present-but-unparseable
    -- block is a `decode` error; neither is a consensus reject inside the fold.
    let fuluBlocks ← (List.range nFulu).toArray.mapM (fun i =>
      match blocks[i]? with
      | none    => Except.error (RunError.spec (.outOfBounds i blocks.size))
      | some bb => match SSZ.deserialize (T := @Fulu.SignedBeaconBlock P) bb with
        | .ok sb   => Except.ok sb
        | .error _ => Except.error (RunError.decode "Fulu SignedBeaconBlock"))
    let gloasBlocks ← (blocks.extract nFulu blocks.size).mapM (fun bb =>
      match SSZ.deserialize (T := @Gloas.SignedBeaconBlock P) bb with
      | .ok sb   => Except.ok sb
      | .error _ => Except.error (RunError.decode "Gloas SignedBeaconBlock"))
    let fuluBox0 : SSZ.Box Sha256 (@Fulu.BeaconState P) := SSZ.FastBox preFulu
    let fuluAction : EStateM StateTransitionError (SSZ.Box Sha256 (@Fulu.BeaconState P)) Unit := do
      for sb in fuluBlocks do Fulu.stateTransition sb
      if (sszGet (← get) slot) < boundary then Fulu.processSlots boundary
    match fuluAction.run fuluBox0 with
    | .error e _ => Except.error (RunError.spec e)
    | .ok _ fuluSt =>
      let gloasBox0 : SSZ.Box Sha256 (@Gloas.BeaconState P) := SSZ.FastBox (upgradeToGloas forkVersion fuluSt.view)
      let gloasAction : EStateM StateTransitionError (SSZ.Box Sha256 (@Gloas.BeaconState P)) Unit := do
        onboardBuildersFromPendingDeposits
        for sb in gloasBlocks do
          if (sszGet (← get) slot) < sb.message.slot then Gloas.processSlots sb.message.slot
          if cmeta.blsSetting != 2 then assert (Gloas.verifyBlockSignature (← get) sb)
          Gloas.processBlock sb.message
          let root ← getStateRoot
          assert (sb.message.stateRoot == bytesToRoot root)
      RunError.ofSpec (runToRoot gloasBox0 gloasAction)

/-- Fold the decoded fork-choice `steps` over the Gloas store. A `block` step runs
`on_block` (which internally records PTC votes from the block's payload attestations
via `notify_ptc_messages`), then replays the block's own attestations /
attester-slashings (`is_from_block = true`); `execution_payload` /
`payload_attestation_message` drive the two new ePBS handlers; the new checks compare
the head node's payload status and the per-block PTC vote arrays. -/
private def fcInterpretGloas [Preset] [Config] [HasherTag] [CryptoBackend]
    (P : Preset) (store0 : Store hashMap) (steps : Array FcStep) : Except StoreTransitionError Unit := do
  -- Same uniform shape as Fulu's `fcInterpret`: each step runs to an `Except` outcome,
  -- which `checkStepValidity` resolves against the step's `valid` flag over the pre-step
  -- snapshot (the framework owns the valid/invalid policy; this loop only threads the
  -- store). The `block` step folds `on_block` and the block's own attestations /
  -- attester-slashings into one action; `execution_payload` / `payload_attestation_message`
  -- are the two ePBS-new valid-flagged steps.
  let mut store : Store hashMap := store0
  for step in steps do
    match step with
    | .tick t =>
      store := (← checkStepValidity store true
        (runOn store (onTick (map := hashMap) (UInt64.ofNat t) : EStateM StoreTransitionError (Store hashMap) Unit)))
    | .block bytes _columns valid =>
      let outcome := decodeStepOr (α := @Gloas.SignedBeaconBlock P) bytes "block" fun sb =>
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
      let outcome := decodeStepOr (α := @Gloas.SignedExecutionPayloadEnvelope P) bytes "envelope" fun env =>
        runOn store (onExecutionPayloadEnvelope (map := hashMap) env : EStateM StoreTransitionError (Store hashMap) Unit)
      store := (← checkStepValidity store valid outcome)
    | .payloadAttestationMessage bytes valid =>
      let outcome := decodeStepOr (α := @Gloas.PayloadAttestationMessage P) bytes "ptc message" fun msg =>
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
    -- Fulu-only checks (e.g. get_proposer_head) never appear in Gloas vectors; ignore
    -- them so the shared `FcStep` match stays exhaustive.
    | _ => pure ()
  pure ()

/-- `runForkChoice` (Gloas): decode the anchor state / block, build the ePBS store,
and run the step interpreter. -/
private def runForkChoiceImpl (P : Preset) (C : Config) (anchorStateBytes anchorBlockBytes : ByteArray)
    (steps : Array FcStep) : Except (RunError StoreTransitionError) Unit :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match SSZ.FastBox.deserialize (T := @Gloas.BeaconState P) anchorStateBytes,
        SSZ.deserialize (T := @Gloas.BeaconBlock P) anchorBlockBytes with
  | .error _, _ => .error (.decode "fork_choice anchor state")
  | _, .error _ => .error (.decode "fork_choice anchor block")
  | .ok anchorState, .ok anchorBlock =>
    RunError.ofSpec (fcInterpretGloas P (getForkchoiceStore anchorState anchorBlock) steps)

/-- Gloas's fork-interface instance at preset `P` with the config's
`GLOAS_FORK_VERSION`. Every in-scope entry is driven: the `fork` upgrade, `stateRoot`,
all `epoch_processing` substeps, `rewards`, the operation handlers (including the ePBS
ones), the block spine (`sanity/blocks` / `sanity/slots` / `finality` / `random`), the
`transition` boundary, and the node-based ePBS fork choice (`runForkChoice`). Only
`runGenesis` stays `todo` (no genesis vectors at the pin). -/
@[reducible] def gloasInterfaceFor (P : Preset) (C : Config) (forkVersion : Version) : ForkInterface where
  stateRoot       := stateRootImpl P
  runUpgrade      := runUpgradeImpl P C forkVersion
  runEpochSubstep := runEpochSubstepImpl P C
  runRewards      := runRewardsImpl P C
  runForkChoice   := runForkChoiceImpl P C
  runOperation    := runOperationImpl P C
  runBlocks       := runBlocksImpl P C
  runSlots        := runSlotsImpl P C
  runGenesis      := fun _ _   => .error (.spec (.todo "gloas genesis: not yet ported"))
  runTransition   := runTransitionImpl P C forkVersion

/-- The `minimal`-preset / config Gloas interface. -/
@[reducible] def gloasInterface : ForkInterface := gloasInterfaceFor minimal minimalConfig gloasForkVersionMinimal

/-- The `mainnet`-preset / config Gloas interface (on demand, Phase 4). -/
@[reducible] def gloasInterfaceMainnet : ForkInterface := gloasInterfaceFor mainnet mainnetConfig gloasForkVersionMainnet

end EthCLSpecs.Gloas.Interface
