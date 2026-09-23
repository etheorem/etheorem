import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Proofs.Fulu.DepositIndex`: where the deposit index increment faults

`process_deposit` (`electra/beacon-chain.md:1672`) checks the Merkle branch, then runs
`state.eth1_deposit_index += 1`, then applies the deposit. The addition is a `uint64` addition,
so remerkleable raises `ValueError` at `2 ^ 64 - 1`. `processDeposit` runs it through
`checkedAdd` and rejects there with `.arithmetic`.

The fault cannot occur where the fork body calls the function. `processOperations` runs the
deposits only while `eth1_deposit_index < min(eth1_data.deposit_count,
deposit_requests_start_index)`. Both bounds are `uint64` values, so the index is at most
`2 ^ 64 - 2`, and the increment stays in range.

These theorems say nothing about `applyDeposit`. They state the run up to it, and hand the
state with the incremented index to it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config State Deposit processDeposit applyDeposit)
open SizzLean.Repr
open SizzLean.Cache

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The descriptor of the increment. `abbrev`, so it unfolds against the string literal in the
elaborated body. -/
abbrev depositIndexDescr : String := "process_deposit: eth1_deposit_index + 1"

/-- **Below the bound.** With a valid Merkle branch and an index below `2 ^ 64 - 1`, the run is
`applyDeposit` on the state with the index incremented by one. -/
@[characterizes processDeposit]
theorem processDeposit_run_of_valid (state : State) (d : Deposit) :
    isValidMerkleBranch (htr d.data) d.proof.toArray
        (EthCLSpecs.Fulu.Const.depositContractTreeDepth + 1)
        (sszGet state eth1DepositIndex).toNat (sszGet state eth1Data).depositRoot = true →
      (sszGet state eth1DepositIndex).toNat + 1 < 2 ^ 64 →
      (processDeposit (StateTransition := FuluRun) d).run state =
        (applyDeposit (StateTransition := FuluRun) d.data.pubkey d.data.withdrawalCredentials
            d.data.amount d.data.signature).run
          (sszUpdate state with eth1DepositIndex := sszGet state eth1DepositIndex + 1) := by
  intro hvalid hlt
  have hc : ¬ sszGet state eth1DepositIndex + 1 < sszGet state eth1DepositIndex := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
    omega
  simp [processDeposit, hvalid, checkedAdd, hc]
  rfl

/-- **At the bound.** With a valid Merkle branch and an index of `2 ^ 64 - 1`, the run rejects
with the `.arithmetic` fault. The pyspec raises `ValueError` at the same point. -/
theorem processDeposit_run_overflow (state : State) (d : Deposit) :
    isValidMerkleBranch (htr d.data) d.proof.toArray
        (EthCLSpecs.Fulu.Const.depositContractTreeDepth + 1)
        (sszGet state eth1DepositIndex).toNat (sszGet state eth1Data).depositRoot = true →
      (sszGet state eth1DepositIndex).toNat + 1 = 2 ^ 64 →
      (processDeposit (StateTransition := FuluRun) d).run state
        = .error (.arithmetic depositIndexDescr) := by
  intro hvalid heq
  have hc : sszGet state eth1DepositIndex + 1 < sszGet state eth1DepositIndex := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_one]
    omega
  simp [processDeposit, hvalid, checkedAdd, hc, throwArithmetic, liftErr, Except.mapError,
    MonadExcept.ofExcept]
  rfl

/-- **Invalid branch.** When the Merkle branch check fails, the run rejects before the
increment, and it produces no state. -/
theorem processDeposit_run_invalid (state : State) (d : Deposit) :
    isValidMerkleBranch (htr d.data) d.proof.toArray
        (EthCLSpecs.Fulu.Const.depositContractTreeDepth + 1)
        (sszGet state eth1DepositIndex).toNat (sszGet state eth1Data).depositRoot = false →
      ∃ e : StateTransitionError,
        (processDeposit (StateTransition := FuluRun) d).run state = .error e := by
  intro hinvalid
  simp [processDeposit, hinvalid]
  all_goals exact ⟨_, rfl⟩

/-- **The caller's guard.** `processOperations` runs a deposit only while the index is below
`eth1_data.deposit_count`. Under that guard the increment cannot fault, so the run is
`applyDeposit` on the incremented state. -/
theorem processDeposit_run_of_lt_depositCount (state : State) (d : Deposit) :
    isValidMerkleBranch (htr d.data) d.proof.toArray
        (EthCLSpecs.Fulu.Const.depositContractTreeDepth + 1)
        (sszGet state eth1DepositIndex).toNat (sszGet state eth1Data).depositRoot = true →
      sszGet state eth1DepositIndex < (sszGet state eth1Data).depositCount →
      (processDeposit (StateTransition := FuluRun) d).run state =
        (applyDeposit (StateTransition := FuluRun) d.data.pubkey d.data.withdrawalCredentials
            d.data.amount d.data.signature).run
          (sszUpdate state with eth1DepositIndex := sszGet state eth1DepositIndex + 1) := by
  intro hvalid hlt
  have hcount := UInt64.toNat_lt (sszGet state eth1Data).depositCount
  have hidx := UInt64.lt_iff_toNat_lt.mp hlt
  exact processDeposit_run_of_valid state d hvalid (by omega)

end EthCLSpecs.Proofs.Fulu
