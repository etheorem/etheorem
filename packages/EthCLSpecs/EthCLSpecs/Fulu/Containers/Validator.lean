import EthCLSpecs.Fulu.Containers.Checkpoint

/-!
# `EthCLSpecs.Fulu.Containers.Validator`: the validator record (load order row 5)

The `Validator` container plus the predicates that are **pure on a `Validator`**:
`isActiveValidator`, `isSlashableValidator`, `isEligibleForActivationQueue`, and
the withdrawal-credential predicates (`SPECS_ARCHITECTURE.md` §3.1 colocates a
container's `State`-free pure predicates with it). A predicate that reads the
`State` (e.g. `isEligibleForActivation`, which reads the finalized checkpoint) is
not pure on the container, so it lives in a state-operation concern file, not here.

The predicates name the `[Preset]`-parameterized `Validator` type, so the file
carries a `variable [Preset]` line for them; Lean attaches it only where the type
is used. The constants they read (`farFutureEpoch`, `minActivationBalance`, the
credential prefixes) are universal literals; the lone exception is
`passedShardCommitteePeriod`, whose `Const.shardCommitteePeriod` is `[Config]`-tier, so the
file also carries a `variable [Config]` line that Lean attaches only there.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

/-- A validator record. -/
forkcontainer Validator where
  pubkey                     : BLSPubkey
  withdrawalCredentials      : Bytes32
  effectiveBalance           : Gwei
  slashed                    : Bool
  activationEligibilityEpoch : Epoch
  activationEpoch            : Epoch
  exitEpoch                  : Epoch
  withdrawableEpoch          : Epoch

variable [Preset]
variable [Config]

/-! ## Validator predicates (pure on the container) -/

forkdef isActiveValidator (v : Validator) (epoch : Epoch) : Bool :=
  v.activationEpoch ≤ epoch && epoch < v.exitEpoch
forkdef isSlashableValidator (v : Validator) (epoch : Epoch) : Bool :=
  !v.slashed && v.activationEpoch ≤ epoch && epoch < v.withdrawableEpoch
forkdef isEligibleForActivationQueue (v : Validator) : Bool :=
  v.activationEligibilityEpoch == Const.farFutureEpoch && v.effectiveBalance ≥ Const.minActivationBalance

/-- `validator.exit_epoch == FAR_FUTURE_EPOCH`: the validator has not yet scheduled an exit
(its exit epoch still holds the sentinel an unscheduled validator carries). The exit /
withdrawal / consolidation guards each test this alongside other conditions, so it is named as
an atom and the surrounding branch keeps its remaining checks. `Const.farFutureEpoch` is a
universal-tier literal, so this predicate needs no `[Config]`. -/
forkdef hasNotInitiatedExit (v : Validator) : Bool :=
  v.exitEpoch == Const.farFutureEpoch

/-- `validator.activation_epoch + SHARD_COMMITTEE_PERIOD <= epoch`: the validator has been
active long enough to exit or consolidate. Written in the `≤` direction the spec uses; the call
sites that gate on *not* having passed the window spell it `!passedShardCommitteePeriod …`.
The sum is the pyspec's checked `Epoch` addition (`phase0/beacon-chain.md`,
`passed_shard_committee_period`), so it binds and the predicate carries the fault
(`SPEC_ARITHMETIC.md` §4.3): a comparison never raises, so the raise is the sum's alone.
`Const.shardCommitteePeriod` is a `[Config]`-tier constant, so this is the one predicate in this
file that carries the `[Config]` binder. -/
forkdef passedShardCommitteePeriod (v : Validator) (epoch : Epoch) : Checked Bool := do
  let shifted ← v.activationEpoch + Const.shardCommitteePeriod
  pure (shifted ≤ epoch)

/-! ## Withdrawal-credential predicates (pure on the container) -/

forkdef credPrefix (wc : Bytes32) : UInt8 := vget wc 0
forkdef hasEth1WithdrawalCredential (v : Validator) : Bool :=
  credPrefix v.withdrawalCredentials == Const.eth1AddressWithdrawalPrefix
forkdef hasCompoundingWithdrawalCredential (v : Validator) : Bool :=
  credPrefix v.withdrawalCredentials == Const.compoundingWithdrawalPrefix
forkdef hasExecutionWithdrawalCredential (v : Validator) : Bool :=
  hasEth1WithdrawalCredential v || hasCompoundingWithdrawalCredential v
forkdef getMaxEffectiveBalance (v : Validator) : Gwei :=
  if hasCompoundingWithdrawalCredential v then Const.maxEffectiveBalanceElectraG else Const.minActivationBalance

end EthCLSpecs.Fulu
