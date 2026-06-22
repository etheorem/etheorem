import EthCLSpecs.Fulu.Containers.PendingOps

/-!
# `EthCLSpecs.Fulu.Containers.Withdrawal`: the withdrawal + historical summary (load order row 13)

The Capella `Withdrawal` (referenced by Gloas's payload-expected-withdrawals) and
`HistoricalSummary` (`SPECS_ARCHITECTURE.md` §3.1). Close-kin history/withdrawal
records share this file.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- A Capella withdrawal (referenced by Gloas's payload-expected-withdrawals). -/
forkcontainer Withdrawal where
  index          : WithdrawalIndex
  validatorIndex : ValidatorIndex
  address        : ExecutionAddress
  amount         : Gwei

/-- A Capella historical summary. -/
forkcontainer HistoricalSummary where
  blockSummaryRoot : Root
  stateSummaryRoot : Root

end EthCLSpecs.Fulu
