import LeanEthCS.Primitives
import LeanEthCS.Forks.Gloas.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.Builder`: ePBS builder-registry containers

EIP-7732 adds a separate "builder" entity alongside validators. The
three containers here describe a builder's registry entry plus the
pending-payment / pending-withdrawal queues that track unsettled
builder bids and exits.

All three are preset-invariant: their *list caps* on `BeaconState`
(`BUILDER_REGISTRY_LIMIT`, `BUILDER_PENDING_WITHDRAWALS_LIMIT`) are
preset-sensitive but the containers themselves are not.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS

/-- A builder registry entry, the ePBS counterpart of `Validator`.
Tracks a builder's BLS key, version, execution address, balance,
and lifecycle epochs. -/
structure Builder where
  pubkey            : BLSPubkey
  version           : UInt8
  executionAddress  : ExecutionAddress
  balance           : Gwei
  depositEpoch      : Epoch
  withdrawableEpoch : Epoch
  deriving SSZRepr

/-- A deferred payment the protocol owes a builder. `weight`
attributes the payment proportionally to attesters; `withdrawal`
records the eventual flow to the builder's execution address. -/
structure BuilderPendingWithdrawal where
  feeRecipient : ExecutionAddress
  amount       : Gwei
  builderIndex : BuilderIndex
  deriving SSZRepr

/-- A pending builder payment: a weight plus the underlying
withdrawal it will eventually settle to. -/
structure BuilderPendingPayment where
  weight     : Gwei
  withdrawal : BuilderPendingWithdrawal
  deriving SSZRepr

end LeanEthCS.Forks.Gloas
