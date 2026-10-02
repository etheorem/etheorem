import EthCLSpecs.Heze.Transition
import EthCLSpecs.Proofs.Heze.HandlerFrames
import EthCLSpecs.Proofs.Heze.FrameInvert

/-!
# `EthCLSpecs.Proofs.Heze.PaymentFrame`: the functions that keep the payment window

`processBuilderPendingPayments` judges the payment of a bid one epoch after the block.
Between the two, the chain runs slots, epochs, and blocks. Five spec functions write the
payment window `builderPendingPayments` (`PaymentWriters.lean`). This module proves that the
others keep it.

The run argument (`PaymentCarried.lean`) tracks three more fields: the state slot,
the slot of the latest block header, and the cached bid `latestExecutionPayloadBid`. The
writers settle or record the index of a slot that these fields fix. So each frame lemma
here states one fact for all four fields, the view `windowView`. A function that writes the
window but keeps the other three has a frame lemma for `spineView`.

Each lemma states its run over plain values,
`(h : f.run (pureState t) = .ok (a, pureState t')) : windowView (pureState t') = windowView
(pureState t)`, and `frame_invert` (`FrameInvert.lean`) proves it. The attribute `@[frame]`
lets a caller's proof close the call by the lemma. A function that reads the state only has
one lemma with the conclusion `(pureState t').view = (pureState t).view`, which serves each
view through `frame_of_reads`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State Slot ExecutionPayloadBid BuilderPendingPayment BeaconState
  ValidatorIndex Gwei)
open EthCLSpecs.Heze.Const (slotsPerEpoch)

attribute [frame_proj] frame_of_reads

section
variable [Preset] [HasherTag]

/-- The three fields that fix which payment index a writer touches: the state slot, the
slot of the latest block header, and the cached bid. -/
def spineView (st : State) : Slot × Slot × ExecutionPayloadBid :=
  (sszGet st slot, (sszGet st latestBlockHeader).slot, sszGet st latestExecutionPayloadBid)

/-- The spine fields and the payment window. -/
def windowView (st : State) :
    (Slot × Slot × ExecutionPayloadBid) × Vector BuilderPendingPayment (2 * slotsPerEpoch) :=
  (spineView st, sszGet st builderPendingPayments)

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The epoch functions -/

/-- `processSlashingsReset` keeps the tracked fields. -/
@[frame] theorem processSlashingsReset_frame {t t' : BeaconState} {a : PUnit}
    (h : (EthCLSpecs.Heze.processSlashingsReset (StateTransition := HezeRun)).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

/-- `processEth1Data` keeps the tracked fields. -/
@[frame] theorem processEth1Data_frame {t t' : BeaconState} {a : PUnit}
    {body : EthCLSpecs.Heze.BeaconBlockBody}
    (h : (EthCLSpecs.Heze.processEth1Data (StateTransition := HezeRun) body).run (pureState t)
      = .ok (a, pureState t')) :
    windowView (pureState t') = windowView (pureState t) := by
  frame_invert h

end

end EthCLSpecs.Proofs.Heze
