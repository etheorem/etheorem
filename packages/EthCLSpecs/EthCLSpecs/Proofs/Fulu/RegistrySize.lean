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
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config State Deposit Gwei Bytes32 BLSPubkey BLSSignature
  processDeposit applyDeposit addValidatorToRegistry getValidatorFromDeposit
  isValidDepositSignature)
open SizzLean.Repr
open SizzLean.Cache

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
theorem addValidatorToRegistry_run_eq (s : State) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) :
    (addValidatorToRegistry (StateTransition := FuluRun) pubkey wc amount).run s =
      .ok ((), sszUpdate s with
        validators := (sszGet s validators).push (getValidatorFromDeposit pubkey wc amount),
        balances := (sszGet s balances).push amount,
        previousEpochParticipation := (sszGet s previousEpochParticipation).push 0,
        currentEpochParticipation := (sszGet s currentEpochParticipation).push 0,
        inactivityScores := (sszGet s inactivityScores).push 0) :=
  rfl

/-- `addValidatorToRegistry` keeps `validators` and `balances` equal in length. -/
theorem addValidatorToRegistry_registry_sizes (s : State) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) :
    (sszGet s validators).size = (sszGet s balances).size →
      ∃ s' : State,
        (addValidatorToRegistry (StateTransition := FuluRun) pubkey wc amount).run s
            = .ok ((), s') ∧
          (sszGet s' validators).size = (sszGet s' balances).size := by
  intro h
  have hpush := push_size_congr (sszGet s validators) (sszGet s balances)
    (getValidatorFromDeposit pubkey wc amount) amount h
  refine ⟨_, addValidatorToRegistry_run_eq s pubkey wc amount, ?_⟩
  -- `State` is `SSZ.Box`'s two-constructor sum. Both flavours' views reduce the two field
  -- reads to the pushes.
  rcases s with t | t <;> exact hpush

variable [Config] [CryptoBackend]

/-- `applyDeposit` never rejects, and it keeps `validators` and `balances` equal in length. A
known pubkey only queues a pending deposit. A new pubkey with a valid signature goes through
`addValidatorToRegistry`, then queues. A new pubkey with an invalid signature changes
nothing. -/
theorem applyDeposit_registry_sizes (s : State) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : Gwei) (sig : BLSSignature) :
    (sszGet s validators).size = (sszGet s balances).size →
      ∃ s' : State,
        (applyDeposit (StateTransition := FuluRun) pubkey wc amount sig).run s = .ok ((), s') ∧
          (sszGet s' validators).size = (sszGet s' balances).size := by
  intro h
  -- `applyDeposit` registers the validator with amount `0`, and queues the real amount.
  have hpush := push_size_congr (sszGet s validators) (sszGet s balances)
    (getValidatorFromDeposit pubkey wc 0) 0 h
  -- `simp` reduces the body's `get` bind, and it rewrites the `.any` test into an `∃` on the
  -- way. So each hypothesis goes into that same `simp` normal form before `simp` uses it.
  by_cases hknown : (sszGet s validators).any (·.pubkey == pubkey) = true
  · have hk := hknown
    simp at hk
    refine ⟨_, by simp [applyDeposit, hk]; rfl, ?_⟩
    rcases s with t | t <;> exact h
  · -- The goal's `if` reads the `∃` form, so state the negation in that form.
    have hk : ¬ ∃ i, ∃ hi : i < (sszGet s validators).val.size,
        ((sszGet s validators).val[i]'hi).pubkey = pubkey := by
      intro ⟨i, hi, he⟩
      apply hknown
      simp
      exact ⟨i, hi, he⟩
    by_cases hsig : isValidDepositSignature pubkey wc amount sig = true
    · refine ⟨_, by simp [applyDeposit, hk, hsig]; rfl, ?_⟩
      rcases s with t | t <;> exact hpush
    · refine ⟨s, by simp [applyDeposit, hk, hsig]; rfl, h⟩

/-- **`processDeposit` keeps the registry aligned.** Every successful run ends with
`validators` and `balances` equal in length, when they started equal. The index write touches
neither list, and `applyDeposit_registry_sizes` covers the rest. -/
theorem processDeposit_registry_sizes (s s' : State) (d : Deposit) :
    (sszGet s validators).size = (sszGet s balances).size →
      (processDeposit (StateTransition := FuluRun) d).run s = .ok ((), s') →
      (sszGet s' validators).size = (sszGet s' balances).size := by
  intro h hrun
  by_cases hvalid : isValidMerkleBranch (htr d.data) d.proof.toArray
      (EthCLSpecs.Fulu.Const.depositContractTreeDepth + 1)
      (sszGet s eth1DepositIndex).toNat (sszGet s eth1Data).depositRoot = true
  · by_cases hlt : (sszGet s eth1DepositIndex).toNat + 1 < 2 ^ 64
    · -- The index write leaves both lists as they were.
      obtain ⟨s₁, hrun₁, hsizes⟩ := applyDeposit_registry_sizes
        (sszUpdate s with eth1DepositIndex := sszGet s eth1DepositIndex + 1) d.data.pubkey
        d.data.withdrawalCredentials d.data.amount d.data.signature
        (by rcases s with t | t <;> exact h)
      -- `Eq.trans` compares the two runs up to defeq. The two elaborations of the index write
      -- differ in form, so a syntactic `rw` would not match.
      have hfinal := hrun.symm.trans ((processDeposit_run_of_valid s d hvalid hlt).trans hrun₁)
      cases hfinal
      exact hsizes
    · have heq : (sszGet s eth1DepositIndex).toNat + 1 = 2 ^ 64 := by
        have := UInt64.toNat_lt (sszGet s eth1DepositIndex)
        omega
      rw [processDeposit_run_overflow s d hvalid heq] at hrun
      cases hrun
  · obtain ⟨e, he⟩ := processDeposit_run_invalid s d (by simpa using hvalid)
    rw [he] at hrun
    cases hrun

end EthCLSpecs.Proofs.Fulu
