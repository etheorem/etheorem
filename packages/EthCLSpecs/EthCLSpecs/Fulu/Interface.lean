import EthCLSpecs.Fulu.Transition
import EthCLSpecs.Fulu.EpochProcessing
import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Fulu.ForkChoice

/-!
# `EthCLSpecs.Fulu.Interface`: the fork-interface instance

Fulu's implementation of `EthCLLib.PySpecTests.ForkInterface`, the inverted
conformance contract (`SPEC_AUTHORING_MODEL.md` §11). Every in-scope entry is
driven: `stateRoot`, `runSlots`, `runBlocks`, `runEpochSubstep`, `runOperation`
(including the standalone `execution_payload`), `runRewards`, and `runForkChoice`
(including the PeerDAS data-availability gate and `get_proposer_head`). The three
remaining `todo` entries are out of scope: `runGenesis` (no genesis vectors at the
pin), `runUpgrade` / `runTransition` (the Electra→Fulu boundary needs the Electra
parent fork the library does not build). A vector that reaches a `todo` fails
loudly rather than passing silently.

The discharge here pins the **fast** configuration: `EStateM
StateTransitionError`, `FastBox` (cached `Sha256`), and the FFI `CryptoBackend`,
at the preset/config the runner selects (`minimal` or `mainnet`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Fulu.Interface

/-- Pinned upstream spec / vectors release (`SPEC_AUTHORING_MODEL.md` §10). The
latest `consensus-spec-tests` release; confirmed to carry both Fulu and Gloas
minimal vectors. -/
def pyspecPinnedVersion : String := "v1.7.0-alpha.11"

/-- Decode a `BeaconState` at preset `P` into a `FastBox`, or the runner's `decode`
error (a well-formed vector should always decode, so a parse failure is our bug, not a
consensus reject). -/
private def decodeState (P : Preset) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (SSZ.Box Sha256 (@BeaconState P)) :=
  match SSZ.FastBox.deserialize (T := @BeaconState P) bytes with
  | .ok box  => .ok box
  | .error _ => .error (.decode "BeaconState")

/-- `stateRoot`: decode a `BeaconState` and take its hash-tree-root. A one-shot
terminal root: the decoded value never escapes (the interface returns bytes), and
no mutation happens between decode and root, so it roots through the uncached
`htr` with no cached box to build and immediately drop. The mutating entries
(`runOperation`, `runSlots`, …) still take the cached `decodeState` box, where the
cache earns its keep across `sszUpdate` re-hashes. -/
private def stateRootImpl (P : Preset) (bytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray :=
  letI : Preset := P
  letI : HasherTag := fastHasherTag
  match SSZ.deserialize (T := @BeaconState P) bytes with
  | .ok v    => .ok (htr v)
  | .error _ => .error (.decode "BeaconState")

/-- `runSlots`: decode the pre-state, advance to `slot + n` through the real
`processSlots` (running `processEpoch` at each boundary) at the fast config, and
return the post root. Drives `sanity/slots`. -/
private def runSlotsImpl (P : Preset) (C : Config) (preBytes : ByteArray) (n : Nat) :
    Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@BeaconState P)) Unit := do
    let state ← get
    processSlots ((sszGet state slot) + UInt64.ofNat n)
  RunError.ofSpec (runToRoot box0 action)

/-- `runEpochSubstep`: dispatch the `epoch_processing/<handler>` name to its
substep, run it over the decoded pre-state at the fast config, return the post
root. All epoch substeps are wired; an unknown handler is a `todo`. -/
private def runEpochSubstepImpl (P : Preset) (C : Config) (step : EpochStep) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@BeaconState P)) Unit :=
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
    | .pendingConsolidations        => processPendingConsolidations
    | .syncCommitteeUpdates         => processSyncCommitteeUpdates
    | .proposerLookahead            => processProposerLookahead
    -- Gloas-only epoch substeps; Fulu does not run them as standalone steps.
    | .pendingDepositsChurn | .builderPendingPayments | .ptcWindow =>
        throw (.todo s!"epoch_processing/{reprStr step}: not a Fulu substep")
  RunError.ofSpec (runToRoot box0 action)

/-- Decode a plain (non-boxed) SSZ operation value, or the runner's `decode` error (a
well-formed operation vector always decodes). -/
private def decodeOp (T : Type) [SSZRepr T] (b : ByteArray) :
    Except (RunError StateTransitionError) T :=
  match SSZ.deserialize (T := T) b with
  | .ok v    => .ok v
  | .error _ => .error (.decode "operation")

/-- `runOperation`: decode the named operation, run its handler over the decoded
pre-state at the fast config (verify-off when `bls_setting = 2`), return the post
root. The block-scoped handlers (`block_header`, `sync_aggregate`, `withdrawals`,
`execution_payload`) are driven through `runBlocks`, so they stay `todo` here. -/
private def runOperationImpl (P : Preset) (C : Config) (kind : OpKind)
    (preBytes opBytes : ByteArray) (cmeta : CaseMeta) : Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let dispatch : Except (RunError StateTransitionError) (EStateM StateTransitionError (SSZ.Box Sha256 (@BeaconState P)) Unit) :=
    match kind with
    | .proposerSlashing      => (decodeOp (@ProposerSlashing P) opBytes).map processProposerSlashing
    | .attesterSlashing      => (decodeOp (@AttesterSlashing P) opBytes).map processAttesterSlashing
    | .attestation           => (decodeOp (@Attestation P) opBytes).map processAttestation
    | .deposit               => (decodeOp (@Deposit P) opBytes).map processDeposit
    | .voluntaryExit         => (decodeOp (@SignedVoluntaryExit P) opBytes).map processVoluntaryExit
    | .blsToExecutionChange  => (decodeOp (@SignedBLSToExecutionChange P) opBytes).map processBlsToExecutionChange
    | .depositRequest        => (decodeOp (@DepositRequest P) opBytes).map processDepositRequest
    | .withdrawalRequest     => (decodeOp (@WithdrawalRequest P) opBytes).map processWithdrawalRequest
    | .consolidationRequest  => (decodeOp (@ConsolidationRequest P) opBytes).map processConsolidationRequest
    | .blockHeader           => (decodeOp (@BeaconBlock P) opBytes).map processBlockHeader
    | .syncAggregate         => (decodeOp (@SyncAggregate P) opBytes).map processSyncAggregate
    | .withdrawals           => (decodeOp (@ExecutionPayload P) opBytes).map processWithdrawals
    -- The standalone execution_payload op runs the in-block handler, gated on the
    -- mocked execution-engine verdict (`execution.yaml`): a `false` verdict is the
    -- spec's `assert verify_and_notify_new_payload(...)` failing, so the op rejects.
    | .executionPayload      => (decodeOp (@BeaconBlockBody P) opBytes).map (fun body => do
        assert cmeta.executionValid
        processExecutionPayload body)
    -- Gloas / EIP-7732-only operation handlers; not standalone Fulu operations.
    | .voluntaryExitChurn | .payloadAttestation | .executionPayloadBid | .parentExecutionPayload =>
        .error (.spec (.todo s!"operations/{reprStr kind}: not a standalone Fulu operation"))
  match dispatch with
  | .error e     => .error e
  | .ok action   =>
    RunError.ofSpec (runToRoot box0 action)

/-- `runRewards`: decode the pre-state and return the four reward-delta blobs
(`source` / `target` / `head` flag-index deltas, then the inactivity-penalty
deltas) serialized as `Deltas`, in the order the driver compares them. The
inactivity `Deltas` carries all-zero rewards, matching the spec's
`get_inactivity_penalty_deltas` (penalties only). -/
private def runRewardsImpl (P : Preset) (C : Config) (preBytes : ByteArray) :
    Except (RunError StateTransitionError) (Array ByteArray) := do
  let state ← decodeState P preBytes
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  let mkDeltas : Array Gwei × Array Gwei → ByteArray := fun rp =>
    SSZ.serialize ({ rewards := sszOfArray rp.1, penalties := sszOfArray rp.2 } : Deltas)
  let n := (sszGet state validators).size
  let zeros := Array.replicate n (0 : Gwei)
  RunError.ofSpec do
    let d0 ← liftErr (getFlagIndexDeltas state 0)
    let d1 ← liftErr (getFlagIndexDeltas state 1)
    let d2 ← liftErr (getFlagIndexDeltas state 2)
    pure #[mkDeltas d0, mkDeltas d1, mkDeltas d2, mkDeltas (zeros, getInactivityPenaltyDeltas state)]

/-- `runBlocks`: decode the pre-state, fold `stateTransition` over the block
sequence (verify-off when `bls_setting = 2`), and return the post root. Drives
`sanity/blocks`, `finality`, `random`. -/
private def runBlocksImpl (P : Preset) (C : Config) (preBytes : ByteArray)
    (blocks : Array ByteArray) (cmeta : CaseMeta) : Except (RunError StateTransitionError) ByteArray := do
  let box0 ← decodeState P preBytes
  -- Decode the whole block sequence up front (both binds stay ahead of the `letI`s, which
  -- close the do-block into term context): deserialization is the runner's job, so a
  -- malformed block is a `decode` error, not a consensus reject inside the fold.
  let signedBlocks ← blocks.mapM (fun bb =>
    match SSZ.deserialize (T := @SignedBeaconBlock P) bb with
    | .ok sb   => .ok sb
    | .error _ => .error (RunError.decode "SignedBeaconBlock"))
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.forBlsSetting cmeta.blsSetting
  let action : EStateM StateTransitionError (SSZ.Box Sha256 (@BeaconState P)) Unit := do
    for sb in signedBlocks do stateTransition sb
  RunError.ofSpec (runToRoot box0 action)

/-- Fold the decoded `steps` over the store from `store0`, verifying each `checks`
step. A `block` step also feeds the block's own attestations / attester-slashings
into the store (`is_from_block = true`). -/
private def fcInterpret [Preset] [Config] [HasherTag] [CryptoBackend]
    (P : Preset) (store0 : Store hashMap) (steps : Array FcStep) : Except StoreTransitionError Unit := do
  -- Each step runs to an `Except StoreTransitionError (Store hashMap)` outcome (the new
  -- store, or the handler's reject), which `checkStepValidity` resolves against the step's
  -- `valid` flag over the pre-step `store` snapshot: an expected rejection rolls back to it
  -- and continues, a valid-vs-actual mismatch is returned as the run's failure. The
  -- per-step valid/invalid policy lives in the framework `checkStepValidity`, not here; this
  -- loop only runs steps and threads the store. Steps with no `valid` flag (`tick`, the
  -- block's own `is_from_block` sub-attestations) are implicitly `valid := true`, so any
  -- reject on them propagates. The handler type annotation pins the abstract `StoreTransition`
  -- monad at `EStateM StoreTransitionError (Store hashMap)`.
  let mut store : Store hashMap := store0
  for step in steps do
    match step with
    | .tick t =>
      store := (← checkStepValidity store true
        (runOn store (onTick (map := hashMap) (UInt64.ofNat t) : EStateM StoreTransitionError (Store hashMap) Unit)))
    | .block bytes columns valid =>
      let outcome := decodeStepOr (α := @SignedBeaconBlock P) bytes "block" fun sb =>
        let cols := columns.filterMap (fun cb => (SSZ.deserialize (T := @DataColumnSidecar P) cb).toOption)
        -- `on_block`, then the block's own attestations / attester-slashings, as one
        -- action: a reject anywhere is the step's reject (and `on_block` rejecting
        -- short-circuits the sub-steps, as the spec requires).
        let action : EStateM StoreTransitionError (Store hashMap) Unit := do
          onBlock (map := hashMap) sb cols
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
    | .checkHead root slot =>
      let head := getHead store
      assert (head == root)
      let headSlot := match FcMap.lookup store.blocks head with | some b => b.slot.toNat | none => 0
      assert (headSlot == slot)
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
    | .checkProposerHead root =>
      let proposerHead := getProposerHead store (getHead store) (getCurrentSlot store)
      assert (proposerHead == root)
    | .unsupported reason => throw (StoreTransitionError.todo reason)
    -- ePBS-only steps (envelope, PTC message, payload-status / vote checks) never
    -- appear in Fulu vectors; ignore them so the shared `FcStep` stays exhaustive.
    | _ => pure ()
  pure ()

/-- `runForkChoice`: decode the anchor state / block, build the store, and run the
step interpreter. The fork-choice vectors carry real signatures, so the FFI crypto
backend is used. -/
private def runForkChoiceImpl (P : Preset) (C : Config) (anchorStateBytes anchorBlockBytes : ByteArray)
    (steps : Array FcStep) : Except (RunError StoreTransitionError) Unit :=
  letI : Preset := P
  letI : Config := C
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match SSZ.FastBox.deserialize (T := @BeaconState P) anchorStateBytes,
        SSZ.deserialize (T := @BeaconBlock P) anchorBlockBytes with
  | .error _, _ => .error (.decode "fork_choice anchor state")
  | _, .error _ => .error (.decode "fork_choice anchor block")
  | .ok anchorState, .ok anchorBlock =>
    RunError.ofSpec (fcInterpret P (getForkchoiceStore anchorState anchorBlock) steps)

/-- The `ssz_static` per-type kernel: decode `bytes` as the container `T`, and on
success return its hash-tree-root paired with whether re-serializing reproduces
`bytes` (the round-trip check). A decode failure on a well-formed static vector is
the runner's `decode` bug, not a consensus reject. `htr` coerces its `Vector UInt8
32` to the `ByteArray` the driver compares against `roots.yaml`. -/
private def runStatic (T : Type) [SSZRepr T] (typeName : String) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (ByteArray × Bool) :=
  letI : HasherTag := fastHasherTag
  match SSZ.deserialize (T := T) bytes with
  | .ok v    => .ok ((htr v : ByteArray), SSZ.serialize v == bytes)
  | .error _ => .error (.decode typeName)

/-- `sszStatic`: dispatch an `ssz_static/<TypeName>` directory name to the Fulu
container it names and run it through `runStatic`. The consensus containers Fulu
models are covered; the light-client, networking, and gossip-aggregation types the
spec does not declare (`AggregateAndProof`, `LightClient*`, `PowBlock`, …) fall to
the `todo` default, so they xfail as out of scope rather than failing. -/
private def sszStaticImpl (P : Preset) (typeName : String) (bytes : ByteArray) :
    Except (RunError StateTransitionError) (ByteArray × Bool) :=
  match typeName with
  | "AttestationData"          => runStatic (@AttestationData P) typeName bytes
  | "Attestation"              => runStatic (@Attestation P) typeName bytes
  | "AttesterSlashing"         => runStatic (@AttesterSlashing P) typeName bytes
  | "BeaconBlock"              => runStatic (@BeaconBlock P) typeName bytes
  | "BeaconBlockBody"          => runStatic (@BeaconBlockBody P) typeName bytes
  | "BeaconBlockHeader"        => runStatic (@BeaconBlockHeader P) typeName bytes
  | "BeaconState"              => runStatic (@BeaconState P) typeName bytes
  | "BLSToExecutionChange"     => runStatic (@BLSToExecutionChange P) typeName bytes
  | "Checkpoint"               => runStatic (@Checkpoint P) typeName bytes
  | "ConsolidationRequest"     => runStatic (@ConsolidationRequest P) typeName bytes
  | "DataColumnSidecar"        => runStatic (@DataColumnSidecar P) typeName bytes
  | "Deposit"                  => runStatic (@Deposit P) typeName bytes
  | "DepositData"              => runStatic (@DepositData P) typeName bytes
  | "DepositMessage"           => runStatic (@DepositMessage P) typeName bytes
  | "DepositRequest"           => runStatic (@DepositRequest P) typeName bytes
  | "Eth1Data"                 => runStatic (@Eth1Data P) typeName bytes
  | "ExecutionPayload"         => runStatic (@ExecutionPayload P) typeName bytes
  | "ExecutionPayloadHeader"   => runStatic (@ExecutionPayloadHeader P) typeName bytes
  | "ExecutionRequests"        => runStatic (@ExecutionRequests P) typeName bytes
  | "Fork"                     => runStatic (@Fork P) typeName bytes
  | "HistoricalSummary"        => runStatic (@HistoricalSummary P) typeName bytes
  | "IndexedAttestation"       => runStatic (@IndexedAttestation P) typeName bytes
  | "PendingConsolidation"     => runStatic (@PendingConsolidation P) typeName bytes
  | "PendingDeposit"           => runStatic (@PendingDeposit P) typeName bytes
  | "PendingPartialWithdrawal" => runStatic (@PendingPartialWithdrawal P) typeName bytes
  | "ProposerSlashing"         => runStatic (@ProposerSlashing P) typeName bytes
  | "SyncAggregate"            => runStatic (@SyncAggregate P) typeName bytes
  | "SyncCommittee"            => runStatic (@SyncCommittee P) typeName bytes
  | "Validator"                => runStatic (@Validator P) typeName bytes
  | "VoluntaryExit"            => runStatic (@VoluntaryExit P) typeName bytes
  | "Withdrawal"               => runStatic (@Withdrawal P) typeName bytes
  | "WithdrawalRequest"        => runStatic (@WithdrawalRequest P) typeName bytes
  | "SignedBeaconBlock"        => runStatic (@SignedBeaconBlock P) typeName bytes
  | "SignedBeaconBlockHeader"  => runStatic (@SignedBeaconBlockHeader P) typeName bytes
  | "SignedBLSToExecutionChange" => runStatic (@SignedBLSToExecutionChange P) typeName bytes
  | "SignedVoluntaryExit"      => runStatic (@SignedVoluntaryExit P) typeName bytes
  | _ => .error (.spec (.todo s!"ssz_static/{typeName}: not modeled by EthCLSpecs.Fulu"))

/-- Fulu's fork-interface instance at preset `P`. The runner injects `minimal` or
`mainnet` per test; both coexist because the preset is a parameter, not a global
instance (`FRAMEWORK_ARCHITECTURE.md` §4). -/
@[reducible] def fuluInterfaceFor (P : Preset) (C : Config) : ForkInterface where
  stateRoot       := stateRootImpl P
  sszStatic       := sszStaticImpl P
  runSlots        := runSlotsImpl P C
  runBlocks       := runBlocksImpl P C
  runEpochSubstep := runEpochSubstepImpl P C
  runOperation    := runOperationImpl P C
  runRewards      := runRewardsImpl P C
  runForkChoice   := runForkChoiceImpl P C
  runGenesis      := fun _ _   => .error (.spec (.todo "genesis: no vectors at this pin (out of scope)"))
  runUpgrade      := fun _     => .error (.spec (.todo "fork upgrade: Gloas only (Phase 3)"))
  runTransition   := fun _ _ _ => .error (.spec (.todo "transition: needs the Electra parent fork (Electra→Fulu boundary)"))

/-- The `minimal`-preset interface (the default; runs on every push). -/
@[reducible] def fuluInterface : ForkInterface := fuluInterfaceFor minimal minimalConfig

/-- The `mainnet`-preset interface (runs on demand / sharded, Phase 4). -/
@[reducible] def fuluInterfaceMainnet : ForkInterface := fuluInterfaceFor mainnet mainnetConfig

end EthCLSpecs.Fulu.Interface
