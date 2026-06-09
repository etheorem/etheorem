import LeanEthCS.Primitives
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Capella.Withdrawal`: Capella withdrawal types

Capella enables validator withdrawals from the beacon chain to the
execution layer. Three new fixed-size containers carry the data:

* `Withdrawal`               : a single withdrawal entry.
* `BLSToExecutionChange`     : a one-time message a validator
  signs to swap their withdrawal credentials from BLS to an
  execution-layer address.
* `SignedBLSToExecutionChange` : signed wrapper.
* `HistoricalSummary`        : replacement for `historical_roots`
  (which is frozen at the Capella fork). One pair of summary
  roots per `SLOTS_PER_HISTORICAL_ROOT` block range.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Capella

open SizzLean

open LeanEthCS

/-- `Withdrawal`, index + validator + address + amount. The four
fields uniquely identify one validator's payout in a payload. -/
structure Withdrawal where
  index          : WithdrawalIndex
  validatorIndex : ValidatorIndex
  address        : ExecutionAddress
  amount         : Gwei
  deriving SSZRepr

/-- `BLSToExecutionChange`, a validator's one-shot message to swap
their withdrawal credentials from a BLS pubkey to a 20-byte
execution-layer address. Pre-signed by the BLS key. -/
structure BLSToExecutionChange where
  validatorIndex      : ValidatorIndex
  fromBlsPubkey       : BLSPubkey
  toExecutionAddress  : ExecutionAddress
  deriving SSZRepr

/-- Signed wrapper around `BLSToExecutionChange`. -/
structure SignedBLSToExecutionChange where
  message   : BLSToExecutionChange
  signature : BLSSignature
  deriving SSZRepr

/-- `HistoricalSummary`, pair of summary roots replacing the
single `historical_roots` entry that Phase 0 stored. Capella
freezes the old `historical_roots` list and starts appending
to `historical_summaries` instead. -/
structure HistoricalSummary where
  blockSummaryRoot : Root
  stateSummaryRoot : Root
  deriving SSZRepr

end LeanEthCS.Forks.Capella
