import EthCLLib.Spec.Errors
import SizzLean

/-!
# `EthCLLib.PySpecTests.Interface`: the fork interface

The conformance contract is inverted (`SPEC_AUTHORING_MODEL.md` §11): the author
implements a fixed typeclass and `PySpecTests`, written once and fork-agnostic,
drives every format against it. This module defines that typeclass,
`ForkInterface`, and the per-case metadata the drivers read.

## The ByteArray boundary

A fork's container types are fork-specific, so the interface cannot name them
and stay fork-agnostic. It works at the **wire boundary** instead: every method
takes raw SSZ `ByteArray`s (a pre-state, a block, an operation) and returns a
post-state Merkle **root** as a `ByteArray`, or a typed reject. The fork decodes
through its own `SSZRepr`, runs the entry point on the boxed state, and takes the
root; the driver compares two roots, both `ByteArray`s, so it never names a fork
type. This is what lets the generic driver live in `EthCLLib` and depend on no
spec.

## Independently invocable entry points

A single-operation vector drives a single handler, so the operation and
epoch-substep methods take a **typed handler tag** (`OpKind` / `EpochStep`) and the
fork dispatches on it internally. The wire handler name from the case path (e.g.
`operations/proposer_slashing` → `"proposer_slashing"`) is parsed to its tag once, at
the driver boundary (`OpKind.ofString?` / `EpochStep.ofString?`); an unrecognized name
is out of scope. This keeps the method set fixed while still driving one handler in
isolation, the inverted contract's requirement.

## One method per format family, dispatched on a typed tag

The docs list "the individual `process_*` steps" as separate entry points. A
typeclass with ~40 methods is unwieldy, so the interface exposes one method per
*format family* (`runOperation`, `runEpochSubstep`) taking the handler axis as an
inductive tag rather than one method per step. The tag keeps the contract on the
typechecker (`SPEC_AUTHORING_MODEL.md` §11): a fork's `runOperation` / `runEpochSubstep`
matches the tag exhaustively, so omitting a handler is a compile error and adding a
handler for a later fork forces every fork to route or explicitly defer it. A handler
the fork does not drive maps to an explicit `todo` arm, not a silent `_`, so the
deferral is visible on the page. Each handler stays independently invocable.
-/

set_option autoImplicit false

namespace EthCLLib.PySpecTests

/-- The per-case metadata the Python layer parses from `meta.yaml` and forwards
(`FRAMEWORK_ARCHITECTURE.md` §13.1). `blsSetting = 2` selects the verify-off
crypto backend; `blocksCount` bounds a block fold; `forkEpoch` is the
`transition` format's boundary epoch, injected as a config override. -/
structure CaseMeta where
  /-- `bls_setting`: `2` ⇒ verify-off. Default `1` (verify on). -/
  blsSetting : Nat := 1
  /-- `blocks_count`: how many `blocks_N` inputs the fold consumes. -/
  blocksCount : Nat := 0
  /-- `fork_epoch` for the `transition` format; `none` otherwise. -/
  forkEpoch : Option Nat := none
  /-- `fork_block` for the `transition` format: the 0-based index of the last
  pre-fork block. `none` ⇒ every block is post-fork. -/
  forkBlock : Option Nat := none
  /-- `execution.yaml`'s `execution_valid` for `operations/execution_payload`: the
  mocked execution-engine verdict. `true` for every other format. -/
  executionValid : Bool := true
  deriving Inhabited, Repr

/-- One step of a `fork_choice` vector's `steps.yaml`, decoded by the runner.
`checks` carries the expected store values to compare; `unsupported` marks a step
the runner does not model (a `should_override` check, an unrecognized key), so the
case reports `todo` (an xfail) rather than falsely passing. -/
inductive FcStep where
  /-- `{tick: t}`: advance the store clock to absolute time `t` (seconds). -/
  | tick (time : Nat)
  /-- `{block: …}`: a `SignedBeaconBlock`; `valid` is the step's expected outcome.
  `columns` are the raw `DataColumnSidecar` SSZ buffers the step lists (PeerDAS data
  availability, EIP-7594); empty for pre-Fulu blocks and blocks with no blob data. -/
  | block (ssz : ByteArray) (columns : Array ByteArray) (valid : Bool)
  /-- `{attestation: …}`: a wire `Attestation` (`is_from_block = false`); `valid` is the
  step's expected outcome (`valid: false` ⇒ `on_attestation` is expected to reject it,
  so the store is left unchanged). -/
  | attestation (ssz : ByteArray) (valid : Bool)
  /-- `{attester_slashing: …}`: a wire `AttesterSlashing`; `valid` is the expected
  outcome (`valid: false` ⇒ `on_attester_slashing` is expected to reject it). -/
  | attesterSlashing (ssz : ByteArray) (valid : Bool)
  /-- `checks.head`: expected `get_head` root and slot. -/
  | checkHead (root : ByteArray) (slot : Nat)
  /-- `checks.get_proposer_head`: expected `get_proposer_head(store, get_head(store),
  get_current_slot(store))` root. -/
  | checkProposerHead (root : ByteArray)
  /-- `{execution_payload: …}` (Gloas, EIP-7732): a `SignedExecutionPayloadEnvelope`
  for `on_execution_payload_envelope`; `valid` is the expected outcome. -/
  | executionPayload (ssz : ByteArray) (valid : Bool)
  /-- `{payload_attestation_message: …}` (Gloas): a `PayloadAttestationMessage` for
  `on_payload_attestation_message`; `valid` is the expected outcome. -/
  | payloadAttestationMessage (ssz : ByteArray) (valid : Bool)
  /-- `checks.head.payload_status` (Gloas): the head node's payload status. -/
  | checkHeadPayloadStatus (status : Nat)
  /-- `checks.payload_timeliness_vote` (Gloas): the per-PTC-slot timeliness votes
  (`true`/`false`/`none`) recorded for `blockRoot`. -/
  | checkPayloadTimelinessVote (blockRoot : ByteArray) (votes : Array (Option Bool))
  /-- `checks.payload_data_availability_vote` (Gloas). -/
  | checkPayloadDataAvailabilityVote (blockRoot : ByteArray) (votes : Array (Option Bool))
  /-- `checks.justified_checkpoint`. -/
  | checkJustified (epoch : Nat) (root : ByteArray)
  /-- `checks.finalized_checkpoint`. -/
  | checkFinalized (epoch : Nat) (root : ByteArray)
  /-- `checks.proposer_boost_root`. -/
  | checkBoost (root : ByteArray)
  /-- `checks.time`. -/
  | checkTime (t : Nat)
  /-- `checks.genesis_time`. -/
  | checkGenesisTime (t : Nat)
  /-- A check the runner does not model (`should_override_forkchoice_update`, an
  unrecognized step or check key); the case reports `todo`, an xfail. -/
  | unsupported (reason : String)
  deriving Inhabited

/-- Run a state-only `EStateM` action on `s` and project its result to `Except`: the new
store on success, the reject on failure. The bridge from a fork-choice handler (`onBlock`,
`onAttestation`, …) to the `Except` outcome `checkStepValidity` consumes. -/
def runOn {ε σ : Type} (s : σ) (act : EStateM ε σ Unit) : Except ε σ :=
  match act.run s with
  | .ok _ s' => .ok s'
  | .error e _ => .error e

open EthCLLib.Spec in
/-- The runner's per-step valid/invalid check for a fork-choice step, fork-agnostic over
the store type `σ`. `before` is the pre-step store (the snapshot, free here since stores
are immutable values), `expectedValid` the step's wire flag, `outcome` the result of
running the step.

The step itself never decides pass/fail; this does. A step expected valid that succeeds
threads its new store; one expected invalid that is rejected rolls back to `before` and
continues (the rejection is the expected result). The two mismatches, a valid step that is
rejected and an invalid step that is accepted, are failures: the first returns the step's
own error, the second a typed mismatch. So a fork interpreter runs each step to an
`Except` outcome and pipes it through here; the valid/invalid policy lives in one place. -/
def checkStepValidity {σ : Type} (before : σ) (expectedValid : Bool)
    (outcome : Except StoreTransitionError σ) : Except StoreTransitionError σ :=
  match outcome, expectedValid with
  | .ok after, true  => .ok after
  | .ok _,     false => .error (.assert "fork_choice: step accepted but expected invalid")
  | .error _,  false => .ok before
  | .error e,  true  => .error e

open EthCLLib.Spec in
/-- Decode a fork-choice step's SSZ `bytes` to its typed value and run `f` on it, or
short-circuit to the step's reject when the bytes do not deserialize. Factors the
decode-or-reject the `block` / `attestation` / `attester_slashing` step arms repeat: each
decodes its own wire type through the fork's `SSZRepr` and, on a parse failure, fails the
step with a `<label> decode failed` assertion. `label` names the wire type in that message;
`f` runs the handler over the decoded value (typically `runOn store …`). -/
def decodeStepOr {α σ : Type} [SizzLean.SSZRepr α] (bytes : ByteArray) (label : String)
    (f : α → Except StoreTransitionError σ) : Except StoreTransitionError σ :=
  match SizzLean.SSZ.deserialize (T := α) bytes with
  | .error _    => .error (.assert s!"fork_choice: {label} decode failed")
  | .ok value   => f value

/-- The `operations/<handler>` axis as a typed tag, one constructor per pyspec
operation-handler directory across the in-scope forks. `ForkInterface.runOperation`
matches it, so the match is exhaustive: a fork that omits a constructor fails to compile,
and adding a handler for a later fork forces every fork to route or explicitly defer it.
This is the typed contract `SPEC_AUTHORING_MODEL.md` §11 wants, recovered without a
method-per-handler interface. The wire handler string is interpreted only once, at the
driver boundary (`ofString?`). -/
inductive OpKind where
  | proposerSlashing | attesterSlashing | attestation | deposit | voluntaryExit
  | voluntaryExitChurn | blsToExecutionChange | depositRequest | withdrawalRequest
  | consolidationRequest | blockHeader | syncAggregate | withdrawals | executionPayload
  | payloadAttestation | executionPayloadBid | parentExecutionPayload
  | builderDepositRequest | builderExitRequest
  deriving DecidableEq, Repr, Inhabited

/-- Parse a pyspec `operations/<handler>` directory name to its `OpKind`. The single site
a handler string is interpreted; `none` ⇒ the handler is out of scope (no fork drives it),
reported as a deferral rather than a silent miss. -/
def OpKind.ofString? : String → Option OpKind
  | "proposer_slashing"        => some .proposerSlashing
  | "attester_slashing"        => some .attesterSlashing
  | "attestation"              => some .attestation
  | "deposit"                  => some .deposit
  | "voluntary_exit"           => some .voluntaryExit
  | "voluntary_exit_churn"     => some .voluntaryExitChurn
  | "bls_to_execution_change"  => some .blsToExecutionChange
  | "deposit_request"          => some .depositRequest
  | "withdrawal_request"       => some .withdrawalRequest
  | "consolidation_request"    => some .consolidationRequest
  | "block_header"             => some .blockHeader
  | "sync_aggregate"           => some .syncAggregate
  | "withdrawals"              => some .withdrawals
  | "execution_payload"        => some .executionPayload
  | "payload_attestation"      => some .payloadAttestation
  | "execution_payload_bid"    => some .executionPayloadBid
  | "parent_execution_payload" => some .parentExecutionPayload
  | "builder_deposit_request"  => some .builderDepositRequest
  | "builder_exit_request"     => some .builderExitRequest
  | _                          => none

/-- The `epoch_processing/<handler>` axis as a typed tag, one constructor per pyspec
epoch-substep directory across the in-scope forks. Exhaustive like `OpKind`. -/
inductive EpochStep where
  | justificationAndFinalization | inactivityUpdates | rewardsAndPenalties
  | registryUpdates | slashings | effectiveBalanceUpdates | slashingsReset
  | randaoMixesReset | eth1DataReset | historicalSummariesUpdate | participationFlagUpdates
  | pendingDeposits | pendingDepositsChurn | pendingConsolidations | syncCommitteeUpdates
  | proposerLookahead | builderPendingPayments | ptcWindow
  deriving DecidableEq, Repr, Inhabited

/-- Parse a pyspec `epoch_processing/<handler>` directory name to its `EpochStep`. -/
def EpochStep.ofString? : String → Option EpochStep
  | "justification_and_finalization" => some .justificationAndFinalization
  | "inactivity_updates"             => some .inactivityUpdates
  | "rewards_and_penalties"          => some .rewardsAndPenalties
  | "registry_updates"               => some .registryUpdates
  | "slashings"                      => some .slashings
  | "effective_balance_updates"      => some .effectiveBalanceUpdates
  | "slashings_reset"                => some .slashingsReset
  | "randao_mixes_reset"             => some .randaoMixesReset
  | "eth1_data_reset"                => some .eth1DataReset
  | "historical_summaries_update"    => some .historicalSummariesUpdate
  | "participation_flag_updates"     => some .participationFlagUpdates
  | "pending_deposits"               => some .pendingDeposits
  | "pending_deposits_churn"         => some .pendingDepositsChurn
  | "pending_consolidations"         => some .pendingConsolidations
  | "sync_committee_updates"         => some .syncCommitteeUpdates
  | "proposer_lookahead"             => some .proposerLookahead
  | "builder_pending_payments"       => some .builderPendingPayments
  | "ptc_window"                     => some .ptcWindow
  | _                                => none

open EthCLLib.Spec in
/-- The fixed entry-point surface every fork implements so `PySpecTests` can
drive it. Methods return the post-state root (a `ByteArray`) or a typed reject;
the driver compares roots and classifies by the reject constructor.

A fork satisfies this by implementing the driven entries and stubbing the rest
as documented `todo`s, so adding a format in a later phase fills a stub rather
than editing the interface. -/
class ForkInterface where
  /-- Decode a `BeaconState` from wire bytes and return its hash-tree-root. Used
  to turn a vector's `post.ssz_snappy` into the expected root, and to root the
  output of `genesis` / `fork`. -/
  stateRoot : ByteArray → Except (RunError StateTransitionError) ByteArray
  /-- Decode the SSZ container named `typeName` from wire bytes; return its
  hash-tree-root together with whether re-serializing reproduces the input (the
  round-trip check). Drives `ssz_static/<TypeName>`: the fork maps the type name
  to its own `SSZRepr` container, so the method stays at the `ByteArray`
  boundary. A container the fork does not model returns a `todo`, so an
  out-of-scope type xfails rather than failing. -/
  sszStatic : String → ByteArray → Except (RunError StateTransitionError) (ByteArray × Bool)
  /-- Fold a block sequence over the decoded pre-state and return the post root.
  Drives `sanity/blocks`, `finality`, `random`. -/
  runBlocks : ByteArray → Array ByteArray → CaseMeta → Except (RunError StateTransitionError) ByteArray
  /-- Advance the pre-state by `slots` empty slots and return the post root.
  Drives `sanity/slots`. -/
  runSlots : ByteArray → Nat → Except (RunError StateTransitionError) ByteArray
  /-- Run one epoch sub-step (named by the typed `EpochStep`) over the pre-state and
  return the post root. Drives `epoch_processing/<handler>`. -/
  runEpochSubstep : EpochStep → ByteArray → Except (RunError StateTransitionError) ByteArray
  /-- Run one operation handler (named by the typed `OpKind`) with its single SSZ input
  over the pre-state and return the post root. Drives `operations/<handler>`. -/
  runOperation : OpKind → ByteArray → ByteArray → CaseMeta → Except (RunError StateTransitionError) ByteArray
  /-- Compute the per-flag and inactivity reward deltas over the pre-state and
  return them serialized, one `Deltas` SSZ blob per output in the fixed order
  `[source, target, head, inactivity]`. The driver compares each to the vector's
  expected delta file. Drives `rewards/*`. -/
  runRewards : ByteArray → Except (RunError StateTransitionError) (Array ByteArray)
  /-- Interpret a `fork_choice` vector: build the store from the anchor state /
  block, fold the `steps`, and verify each `checks` step. `.ok` ⇒ every check
  matched; `.error e` carries a `RunError StoreTransitionError` the harness
  classifies: a `.decode` is a likely bug, and a wrapped `.spec` reject classifies
  by its constructor (`.todo` an unmodeled-branch xfail, `.assert` an expected
  rejection, `.missingKey` / a wrapped `.outOfBounds` a likely bug). Drives
  `fork_choice/*`. -/
  runForkChoice : ByteArray → ByteArray → Array FcStep → Except (RunError StoreTransitionError) Unit
  /-- Build a genesis state from the eth1 inputs and return its root. Drives
  `genesis`. -/
  runGenesis : Array ByteArray → CaseMeta → Except (RunError StateTransitionError) ByteArray
  /-- Upgrade a finished parent-fork state to this fork and return the upgraded
  root. Drives `fork`. -/
  runUpgrade : ByteArray → Except (RunError StateTransitionError) ByteArray
  /-- Fold a block sequence across the fork boundary at `meta.forkEpoch`,
  applying the upgrade mid-fold, and return the post root. Drives `transition`. -/
  runTransition : ByteArray → Array ByteArray → CaseMeta → Except (RunError StateTransitionError) ByteArray

end EthCLLib.PySpecTests
