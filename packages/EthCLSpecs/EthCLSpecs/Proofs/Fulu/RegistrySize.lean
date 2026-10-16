import EthCLSpecs.Proofs.Fulu.DepositIndex

/-!
# `EthCLSpecs.Proofs.Fulu.RegistrySize`: the deposit path keeps `validators` and `balances` aligned

The beacon state keeps parallel lists: `balances[i]` is the balance of `validators[i]`. So the
two lists must have the same length. This module proves that the Eth1 deposit path keeps that
equality: `addValidatorToRegistry`, `applyDeposit`, and `processDeposit`.

The equality is also what makes `addValidatorToRegistry` agree with the pyspec.
`add_validator_to_registry` (`electra/beacon-chain.md:1602`) computes
`index = len(state.validators)` and calls `set_or_append_list` on each list at that index. The
call appends only when the index equals the list's own length. The Lean body pushes onto every
list unconditionally. The two agree while the lengths are equal.

`SSZList.push` clamps at the list's cap and does nothing past it, where remerkleable raises.
The equality still holds there, because `validators` and `balances` have the same cap,
`VALIDATOR_REGISTRY_LIMIT`, and clamp together.

Statements bind plain `BeaconState` values. The run equation is stated at the box, on
`pureState s`; the size theorems read the runs through `runPure`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config BeaconState Deposit Gwei Bytes32 BLSPubkey BLSSignature
  processDeposit applyDeposit addValidatorToRegistry getValidatorFromDeposit
  isValidDepositSignature)
open EthCLLib.Proofs (pureState runPure runPure_eq runPure_of_run_ok)
open SizzLean.Repr

/-- Two lists of equal length and equal cap stay equal in length after one push each. Both
pushes land below the cap, or both clamp. -/
private theorem push_size_congr {α β : Type} {cap : Nat} (xs : SSZList α cap)
    (ys : SSZList β cap) (a : α) (b : β) (h : xs.size = ys.size) :
    (xs.push a).size = (ys.push b).size := by
  unfold SSZList.push
  by_cases hx : xs.val.size < cap
  · have hy : ys.val.size < cap := by
      have : xs.val.size = ys.val.size := h
      omega
    simp only [hx, hy, dite_true]
    show (xs.val.push a).size = (ys.val.push b).size
    simp only [Array.size_push]
    exact congrArg (· + 1) h
  · have hy : ¬ ys.val.size < cap := by
      have : xs.val.size = ys.val.size := h
      omega
    simp only [hx, hy, dite_false]
    exact h

variable [Preset] [HasherTag]

/-- **Exact run equation.** The run never rejects. It pushes a fresh validator onto
`validators`, the amount onto `balances`, and a zero onto the two participation lists and
`inactivityScores`. -/
@[characterizes addValidatorToRegistry]
theorem addValidatorToRegistry_run_eq (s : BeaconState) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) :
    (addValidatorToRegistry (StateTransition := FuluRun) pubkey wc amount).run (pureState s) =
      .ok ((), pureState
        { s with
            validators := s.validators.push (getValidatorFromDeposit pubkey wc amount)
            balances := s.balances.push amount
            previousEpochParticipation := s.previousEpochParticipation.push 0
            currentEpochParticipation := s.currentEpochParticipation.push 0
            inactivityScores := s.inactivityScores.push 0 }) :=
  rfl

/-- `addValidatorToRegistry` keeps `validators` and `balances` equal in length. -/
theorem addValidatorToRegistry_registry_sizes (s : BeaconState) (pubkey : BLSPubkey)
    (wc : Bytes32) (amount : Gwei) :
    s.validators.size = s.balances.size →
      ∃ s' : BeaconState,
        runPure (addValidatorToRegistry (StateTransition := FuluRun) pubkey wc amount) s
            = .ok ((), s') ∧
          s'.validators.size = s'.balances.size := by
  intro h
  have hpush := push_size_congr s.validators s.balances
    (getValidatorFromDeposit pubkey wc amount) amount h
  exact ⟨_, runPure_of_run_ok (addValidatorToRegistry_run_eq s pubkey wc amount), hpush⟩

variable [Config] [CryptoBackend]

/-- `applyDeposit` never rejects, and it keeps `validators` and `balances` equal in length. A
known pubkey only queues a pending deposit. A new pubkey with a valid signature goes through
`addValidatorToRegistry`, then queues. A new pubkey with an invalid signature changes
nothing. -/
theorem applyDeposit_registry_sizes (s : BeaconState) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) (sig : BLSSignature) :
    s.validators.size = s.balances.size →
      ∃ s' : BeaconState,
        runPure (applyDeposit (StateTransition := FuluRun) pubkey wc amount sig) s
            = .ok ((), s') ∧
          s'.validators.size = s'.balances.size := by
  intro h
  -- `applyDeposit` registers the validator with amount `0`, and queues the real amount.
  have hpush := push_size_congr s.validators s.balances
    (getValidatorFromDeposit pubkey wc 0) 0 h
  -- `simp` reduces the body's `get` bind, and it rewrites the `.any` test into an `∃` on the
  -- way. So each hypothesis goes into that same `simp` normal form before `simp` uses it.
  by_cases hknown : s.validators.any (·.pubkey == pubkey) = true
  · have hk := hknown
    simp at hk
    refine ⟨_, by rw [runPure_eq]; simp [applyDeposit, hk]; rfl, ?_⟩
    exact h
  · -- The goal's `if` reads the `∃` form, so state the negation in that form.
    have hk : ¬ ∃ i, ∃ hi : i < s.validators.val.size, (s.validators.val[i]'hi).pubkey = pubkey := by
      intro ⟨i, hi, he⟩
      apply hknown
      simp
      exact ⟨i, hi, he⟩
    by_cases hsig : isValidDepositSignature pubkey wc amount sig = true
    · refine ⟨_, by rw [runPure_eq]; simp [applyDeposit, hk, hsig]; rfl, ?_⟩
      exact hpush
    · exact ⟨s, by rw [runPure_eq]; simp [applyDeposit, hk, hsig]; rfl, h⟩

/-- **`processDeposit` keeps the registry aligned.** Every successful run ends with
`validators` and `balances` equal in length, when they started equal. The index write touches
neither list, and `applyDeposit_registry_sizes` covers the rest. -/
theorem processDeposit_registry_sizes (s s' : BeaconState) (d : Deposit) :
    s.validators.size = s.balances.size →
      runPure (processDeposit (StateTransition := FuluRun) d) s = .ok ((), s') →
      s'.validators.size = s'.balances.size := by
  intro h hrun
  by_cases hvalid : isValidMerkleBranch (htr d.data) d.proof.toArray
      (EthCLSpecs.Fulu.Const.depositContractTreeDepth + 1)
      s.eth1DepositIndex.toNat s.eth1Data.depositRoot = true
  · by_cases hlt : s.eth1DepositIndex.toNat + 1 < 2 ^ 64
    · -- The index write leaves both lists as they were.
      obtain ⟨s₁, hrun₁, hsizes⟩ := applyDeposit_registry_sizes
        { s with eth1DepositIndex := s.eth1DepositIndex + 1 } d.data.pubkey
        d.data.withdrawalCredentials d.data.amount d.data.signature h
      have hstep :
          runPure (processDeposit (StateTransition := FuluRun) d) s =
            runPure (applyDeposit (StateTransition := FuluRun) d.data.pubkey
                d.data.withdrawalCredentials d.data.amount d.data.signature)
              { s with eth1DepositIndex := s.eth1DepositIndex + 1 } := by
        rw [runPure_eq, processDeposit_run_of_valid s d hvalid hlt, ← runPure_eq]
      have hfinal := hrun.symm.trans (hstep.trans hrun₁)
      cases hfinal
      exact hsizes
    · have heq : s.eth1DepositIndex.toNat + 1 = 2 ^ 64 := by
        have := UInt64.toNat_lt s.eth1DepositIndex
        omega
      rw [runPure_eq, processDeposit_run_overflow s d hvalid heq] at hrun
      cases hrun
  · obtain ⟨e, he⟩ := processDeposit_run_invalid s d (by simpa using hvalid)
    rw [runPure_eq, he] at hrun
    cases hrun

end EthCLSpecs.Proofs.Fulu
