import EthCLSpecs.Tests.HezeWitnessSeams
import EthCLSpecs.Proofs.Heze.PaymentCarried

/-!
# `EthCLSpecs.Tests.HezePaymentWitness`: the payment run has a witness

`bidPaymentCarried_of_run` (`Proofs/Heze/PaymentCarried.lean`) takes a run from the block
of a bid to the epoch substep that judges the bid. This module builds such a run at the
minimal preset and checks every hypothesis of the theorem on it. So the theorem is not
vacuous. The check of `BidPaymentCarried` at the end runs the spec functions and does not
use the theorem.

## The run

The start state is at slot `16`, the first slot of epoch `2`. It has eight active
validators with `MIN_ACTIVATION_BALANCE`, a finalized checkpoint at epoch `1`, and one
builder with a balance of 1000 ETH.

1. `processSlots` takes the state to slot `17`.
2. Block `r` at slot `17` carries a bid of value `1` from builder `0`.
3. One slot step takes the state to slot `18`. A self-built child at slot `18` builds on
   the EMPTY edge of `r`: its parent hash is the latest block hash, which `r` did not
   change.
4. Thirteen slot steps take the state to slot `31`, the last slot of epoch `3`. The slot
   step at the end of epoch `2` moves the entry of `r` to the lower half of the window.
5. `processSlot` and the eight epoch substeps before `processBuilderPendingPayments` run.

No block carries a proposer slashing. The blocks skip the signature check and the state
root check (`validateResult := false`).

The states of the run are plain values. Each one is the view of the box that a step
returns, and each step runs on the uncached box of the value before it. Every step keeps
the uncached box (`KeepsUncached`), so a checked run gives the `pureState` form that the
theorem takes (`run_eq_pure_of_toBool`).

## The seams

- `CryptoBackend.verifyOff`: every BLS signature passes.
- `pureHasherTag`: the pure-Lean SHA-256 of `LeanSha256`. The checks run the compiled
  hasher through `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLLib.Proofs (pureState KeepsUncached)
open EthCLSpecs.Proofs.Heze

namespace EthCLSpecs.Tests.HezePaymentWitness

open EthCLSpecs.Heze (Preset Config State BeaconState Validator BeaconBlock BeaconBlockBody
  BeaconBlockHeader SignedBeaconBlock ExecutionPayloadBid Builder minimal minimalConfig)
open EthCLSpecs.Heze.Const (farFutureEpoch slotsPerEpoch builderIndexSelfBuild
  g2PointAtInfinity minActivationBalance)

local instance : Preset := minimal
local instance : HasherTag := pureHasherTag
local instance : Config := minimalConfig
local instance : CryptoBackend := CryptoBackend.verifyOff

/-- The latest execution block hash of the start state. -/
def h1 : Vector UInt8 32 := Vector.replicate 32 1

/-- The block hash that the bid of `r` commits to. -/
def h2 : Vector UInt8 32 := Vector.replicate 32 2

/-- The block hash that the bid of the child commits to. -/
def h3 : Vector UInt8 32 := Vector.replicate 32 3

/-- The end state of a run, or `d` after an error. -/
def stateOr (r : Except StateTransitionError (PUnit × State)) (d : State) : State :=
  match r with
  | .ok (_, s) => s
  | .error _ => d

/-- A run that succeeds ends in the state that `stateOr` reads. -/
theorem run_eq_of_toBool {r : Except StateTransitionError (PUnit × State)} (d : State)
    (h : r.toBool = true) : r = .ok ((), stateOr r d) := by
  cases r with
  | ok p => rfl
  | error e => simp [Except.toBool] at h

/-- A run from the uncached box of `a` that succeeds, of an action that keeps the uncached
box, ends in the uncached box of the view that `stateOr` reads. -/
theorem run_eq_pure_of_toBool {x : HezeRun PUnit} (hk : KeepsUncached x) (a : BeaconState)
    (d : State) (h : (x.run (pureState a)).toBool = true) :
    x.run (pureState a) = .ok ((), pureState (stateOr (x.run (pureState a)) d).view) := by
  have h1 := run_eq_of_toBool d h
  have hp := hk a () _ h1
  rw [← hp]
  exact h1

/-- An `Option` that is `some` is `some` of its value. -/
theorem eq_some_getD {o : Option BeaconState} (d : BeaconState) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some s => rfl

/-- The start state: slot `16`, epoch `2`, finalized epoch `1`, eight funded validators,
and one active builder. -/
def v16 : BeaconState :=
  let base := (default : BeaconState)
  let active : Validator := { (default : Validator) with
    effectiveBalance := minActivationBalance, exitEpoch := farFutureEpoch,
    withdrawableEpoch := farFutureEpoch }
  let header : BeaconBlockHeader :=
    { (default : BeaconBlockHeader) with bodyRoot := htr (default : BeaconBlockBody) }
  let builder : Builder := { (default : Builder) with
    balance := 1000000000000, depositEpoch := 0, withdrawableEpoch := farFutureEpoch }
  { base with
    slot := 16
    validators := sszOfArray (Array.replicate slotsPerEpoch active)
    balances := sszOfArray (Array.replicate slotsPerEpoch minActivationBalance)
    previousEpochParticipation := sszOfArray (Array.replicate slotsPerEpoch 0)
    currentEpochParticipation := sszOfArray (Array.replicate slotsPerEpoch 0)
    inactivityScores := sszOfArray (Array.replicate slotsPerEpoch 0)
    latestBlockHeader := header
    latestBlockHash := h1
    finalizedCheckpoint := { (default : EthCLSpecs.Heze.Checkpoint) with epoch := 1 }
    builders := sszOfArray #[builder] }

/-- The uncached box of the start state, the default after an error. -/
def st16 : State := pureState v16

/-- The state at slot `17`, before block `r`. -/
def v17 : BeaconState :=
  (stateOr ((EthCLSpecs.Heze.processSlots (StateTransition := HezeRun) 17).run st16) st16).view

/-- A block on `pre` at its slot, by the proposer of `pre`, with the bid `bid`. -/
def mkBlock (pre : State) (bid : ExecutionPayloadBid) : SignedBeaconBlock :=
  { message := { (default : BeaconBlock) with
      slot := sszGet pre slot
      proposerIndex := EthCLSpecs.Heze.getBeaconProposerIndex pre
      parentRoot := htr (sszGet pre latestBlockHeader)
      body := { (default : BeaconBlockBody) with
        signedExecutionPayloadBid := { message := bid, signature := g2PointAtInfinity } } }
    signature := default }

/-- A bid on `pre` with the parent root and the RANDAO mix that
`processExecutionPayloadBid` checks. -/
def bidFor (pre : State) (builderIndex value : UInt64) (hash : Vector UInt8 32) :
    ExecutionPayloadBid :=
  let parentRoot := match (EthCLSpecs.Heze.getBlockRootAtSlot (StateTransition := HezeRun) pre
      (sszGet pre slot - 1)).run pre with
    | .ok (r, _) => r
    | .error _ => default
  let mix := match (EthCLSpecs.Heze.getRandaoMix (StateTransition := HezeRun)
      (EthCLSpecs.Heze.currentEpochOf pre)).run pre with
    | .ok (r, _) => r
    | .error _ => default
  { (default : ExecutionPayloadBid) with
    parentBlockHash := sszGet pre latestBlockHash, parentBlockRoot := parentRoot,
    blockHash := hash, builderIndex := builderIndex, value := value, slot := sszGet pre slot,
    prevRandao := mix,
    executionRequestsRoot := htr (default : EthCLSpecs.Heze.ExecutionRequests) }

/-- The bid of `r`: value `1` from builder `0`. -/
def bidR : ExecutionPayloadBid := bidFor (pureState v17) 0 1 h2

/-- Block `r` at slot `17`. -/
def blockR : SignedBeaconBlock := mkBlock (pureState v17) bidR

/-- The state after block `r`. -/
def v1 : BeaconState := (stateOr ((blockStep blockR false).run (pureState v17)) st16).view

/-- The state at slot `18`, before the child. -/
def v18 : BeaconState := (stateOr (slotIteration.run (pureState v1)) st16).view

/-- The self-built child at slot `18`, on the EMPTY edge of `r`. -/
def blockC : SignedBeaconBlock :=
  mkBlock (pureState v18) { bidFor (pureState v18) builderIndexSelfBuild 0 h3 with value := 0 }

/-- The steps after `r`: one slot, the child, and thirteen slots to slot `31`. -/
def steps : List ChainStep := .slot :: .block blockC false :: List.replicate 13 .slot

/-- The state at slot `31`, the last slot of epoch `3`. -/
def vEnd : BeaconState := (runChain (windowEnd bidR.slot) steps v1).getD v16

/-- The state after `processSlot` at slot `31`. -/
def vA : BeaconState :=
  (stateOr ((EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState vEnd))
    st16).view

/-- The state that `processBuilderPendingPayments` reads. -/
def vJudge : BeaconState := (stateOr (processEpochPrefix.run (pureState vA)) st16).view

/-- No proposer slashing in a block whose body has the default slashing list. -/
theorem noSlashingAt_of_empty {n : EthCLSpecs.Heze.Slot} {p : EthCLSpecs.Heze.ValidatorIndex}
    {sb : SignedBeaconBlock} (h : sb.message.body.proposerSlashings.val.size = 0) :
    NoSlashingAt n p sb := by
  intro ps hm
  rw [Array.eq_empty_of_size_eq_zero h] at hm
  simp at hm

/-- The bid of `r`, read from the block as the theorem statement reads it. -/
abbrev bidOfR : ExecutionPayloadBid := blockR.message.body.signedExecutionPayloadBid.message

/-- Every computed check of the witness, as one `Bool`. One `native_decide` evaluates the
chain once for all of them. -/
def checks : Bool :=
  decide (0 < bidOfR.value) &&
  ((blockStep blockR false).run (pureState v17)).toBool &&
  (runChain (windowEnd bidOfR.slot) steps v1).isSome &&
  decide ((sszGet (pureState vEnd) slot).toNat = windowEnd bidOfR.slot) &&
  decide (blockC.message.body.signedExecutionPayloadBid.message.parentBlockHash
    ≠ bidOfR.blockHash) &&
  decide (blockR.message.body.proposerSlashings.val.size = 0) &&
  decide (blockC.message.body.proposerSlashings.val.size = 0) &&
  ((EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState vEnd)).toBool &&
  (processEpochPrefix.run (pureState vA)).toBool &&
  decide ((vget (sszGet (pureState vJudge) builderPendingPayments)
    (EthCLSpecs.Heze.builderPaymentIndex bidOfR.slot false)).withdrawal
      = bidWithdrawal bidOfR)

/-- The checks pass. The compiled code runs the pure-Lean hasher. -/
theorem checks_eq_true : checks = true := by native_decide

/-- The hypotheses of `bidPaymentCarried_of_run` hold on a concrete chain at the minimal
preset, and `BidPaymentCarried` holds at its judging state. -/
theorem paymentWitness :
    ∃ (sbR : SignedBeaconBlock) (v : Bool) (steps : List ChainStep)
      (st0 st1 stEnd stA stJudge : BeaconState),
      0 < sbR.message.body.signedExecutionPayloadBid.message.value ∧
      BlockStep sbR v st0 st1 ∧
      ChainRun (windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot)
        steps st1 stEnd ∧
      stEnd.slot.toNat = windowEnd sbR.message.body.signedExecutionPayloadBid.message.slot ∧
      EmptyChild sbR.message.body.signedExecutionPayloadBid.message steps ∧
      NoSlashingAt sbR.message.body.signedExecutionPayloadBid.message.slot
        sbR.message.proposerIndex sbR ∧
      NoSlashingSteps sbR.message.body.signedExecutionPayloadBid.message.slot
        sbR.message.proposerIndex steps ∧
      (EthCLSpecs.Heze.processSlot (StateTransition := HezeRun)).run (pureState stEnd)
        = .ok ((), pureState stA) ∧
      processEpochPrefix.run (pureState stA) = .ok ((), pureState stJudge) ∧
      BidPaymentCarried stJudge sbR.message.body.signedExecutionPayloadBid.message := by
  have h := checks_eq_true
  simp only [checks, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hstep⟩, hrun⟩, hend⟩, hhash⟩, hslR⟩, hslC⟩, hslot⟩, hprefix⟩,
    hcarried⟩ := h
  refine ⟨blockR, false, steps, v17, v1, vEnd, vA, vJudge, hpos,
    blockStep_blockStep (run_eq_pure_of_toBool (keepsUncached_blockStep _ _) v17 st16 hstep),
    ChainRun.of_runChain steps v1 vEnd (eq_some_getD v16 hrun),
    hend, ?_, noSlashingAt_of_empty hslR, ?_,
    run_eq_pure_of_toBool keepsUncached_processSlot vEnd st16 hslot,
    run_eq_pure_of_toBool keepsUncached_processEpochPrefix vA st16 hprefix, hcarried⟩
  · -- The first block of `steps` is the child, and its parent hash is not the bid's hash.
    intro sb h
    simp only [steps, firstBlock?, Option.some.injEq] at h
    subst h
    exact hhash
  · -- The only block of `steps` is the child, with no proposer slashing.
    intro sb v hm
    simp [steps] at hm
    obtain ⟨rfl, -⟩ := hm
    exact noSlashingAt_of_empty hslC

end EthCLSpecs.Tests.HezePaymentWitness
