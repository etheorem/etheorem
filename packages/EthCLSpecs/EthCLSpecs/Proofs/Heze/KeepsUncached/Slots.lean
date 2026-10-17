import EthCLSpecs.Proofs.Heze.KeepsUncached.Epoch
import EthCLSpecs.Proofs.Heze.KeepsUncached.Payload
import EthCLSpecs.Proofs.Heze.KeepsUncached.Withdrawals

/-!
# `EthCLSpecs.Proofs.Heze.KeepsUncached.Slots`: the state transition keeps the uncached box

This file closes the chain. `processSlot` caches the state root and the block root.
`processSlots` runs `processSlot` and, at an epoch boundary, `processEpoch` for each slot
up to the target. `processBlock` runs the eight block substeps, and `stateTransition`
runs `processSlots`, the signature gate, `processBlock` and the state-root gate.

`processSlot` writes through `stateRoot`. On an uncached box, `stateRoot` returns the
same box (`hashTreeRoot_uncachedBox`), so the writer maps `pureState v` to `pureState`
of a value, and the record update closes by `rfl`. The other three functions are
sequences of calls with lemmas of their own, and their proofs apply those lemmas one
bind at a time. All the lemmas are supporting facts, untagged.
-/
set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze (Preset Config Slot BeaconBlock SignedBeaconBlock processSlot
  processSlots processBlock stateTransition)
open EthCLLib.Proofs (KeepsUncached keepsUncached_bind keepsUncached_getStateRoot
  keepsUncached_get keepsUncached_ite keepsUncached_pure keepsUncached_throw)

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- `processSlot` keeps the flavour: one writer that reads the state root and caches it,
the header and the block root. -/
theorem keepsUncached_processSlot :
    KeepsUncached (processSlot (StateTransition := HezeRun)) := by
  unfold processSlot
  keeps_uncached

/-- `processSlots` keeps the flavour: a gate, then a range loop whose step runs
`processSlot`, `processEpoch` at an epoch boundary, and the slot increment. -/
theorem keepsUncached_processSlots (target : Slot) :
    KeepsUncached (processSlots (StateTransition := HezeRun) target) := by
  unfold processSlots
  keeps_uncached_using [keepsUncached_processSlot, keepsUncached_processEpoch]

/-- `processBlock` keeps the flavour: its eight substeps run in order, and each has a
lemma of its own. -/
theorem keepsUncached_processBlock (block : BeaconBlock) :
    KeepsUncached (processBlock (StateTransition := HezeRun) block) := by
  unfold processBlock
  refine keepsUncached_bind (keepsUncached_processParentExecutionPayload _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_processBlockHeader _) (fun _ => ?_)
  refine keepsUncached_bind keepsUncached_processWithdrawals (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_processExecutionPayloadBid _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_processRandao _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_processEth1Data _) (fun _ => ?_)
  refine keepsUncached_bind (keepsUncached_processOperations _) (fun _ => ?_)
  exact keepsUncached_processSyncAggregate _

/-- `stateTransition` keeps the flavour: `processSlots`, the signature check (an `Except`
read of the state, then its gate), `processBlock`, and the state-root gate on
`getStateRoot`. -/
theorem keepsUncached_stateTransition (signedBlock : SignedBeaconBlock) (validateResult : Bool) :
    KeepsUncached (stateTransition (StateTransition := HezeRun) signedBlock validateResult) := by
  unfold stateTransition
  refine keepsUncached_bind (keepsUncached_processSlots _) (fun _ => ?_)
  -- Each `if validateResult then …` with no `else` elaborates to a join point
  -- `have __do_jp := …` for the code after it. `extract_lets` names them.
  extract_lets jp
  have hjp : ∀ y, KeepsUncached (jp y) := fun _ => by
    refine keepsUncached_bind (keepsUncached_processBlock _) (fun _ => ?_)
    exact keepsUncached_ite
      (fun _ => keepsUncached_bind keepsUncached_getStateRoot
        (fun _ => keepsUncached_ite (fun _ => keepsUncached_pure _)
          (fun _ => keepsUncached_throw _)))
      (fun _ => keepsUncached_pure _)
  exact keepsUncached_ite
    (fun _ => keepsUncached_bind keepsUncached_get
      (fun _ => keepsUncached_bind (EthCLLib.Proofs.keepsUncached_liftErr _)
        (fun _ => keepsUncached_bind (keepsUncached_ite (fun _ => keepsUncached_pure _)
          (fun _ => keepsUncached_throw _)) hjp)))
    (fun _ => keepsUncached_bind (keepsUncached_pure _) hjp)

end

end EthCLSpecs.Proofs.Heze
