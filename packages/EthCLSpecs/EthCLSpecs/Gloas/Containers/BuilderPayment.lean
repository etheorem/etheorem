import EthCLSpecs.Gloas.Containers.PayloadBid

/-!
# `EthCLSpecs.Gloas.Containers.BuilderPayment`: the builder-payment queue (EIP-7732)

The pending builder withdrawal (`BuilderPendingWithdrawal`) and the payment that
weights it (`BuilderPendingPayment`), the records the state queues for builder
payouts.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

/-- A pending builder withdrawal. -/
forkcontainer BuilderPendingWithdrawal where
  feeRecipient : ExecutionAddress
  amount       : Gwei
  builderIndex : BuilderIndex

/-- A pending builder payment, weighting a pending withdrawal. EIP-8282 records the
proposer that produced it so a proposer slashing only clears its own payment. -/
forkcontainer BuilderPendingPayment where
  weight        : Gwei
  withdrawal    : BuilderPendingWithdrawal
  proposerIndex : ValidatorIndex

end EthCLSpecs.Gloas
