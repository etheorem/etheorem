import EthCLSpecs.Gloas.Withdrawals
import EthCLSpecs.Proofs.Gloas.Run
import SizzLean.Proofs.SSZListSet

/-!
# `EthCLSpecs.Proofs.Gloas.ApplyWithdrawals`: builder withdrawals never raise a builder balance

`apply_withdrawals` (`gloas/beacon-chain.md:1389`) takes a builder-flagged withdrawal from the
builder's balance as `balance -= min(withdrawal.amount, balance)`. The `min` makes the
subtraction safe: the new balance is the truncating difference, never a wrap. The Lean body
writes the same expression.

The theorem here covers the whole loop over any withdrawals array. On every successful run, the
builder registry keeps its size, and no builder balance ends higher than it started. A
validator withdrawal goes through `decreaseBalance`, which never touches `builders`. A builder
withdrawal lowers one balance by at most its own value.

The proof carries a preorder over the loop's accumulator through a generic `forIn` induction.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLSpecs.Gloas (Preset State Withdrawal applyWithdrawals)
open SizzLean.Repr
open SizzLean.Cache
open SizzLean.Proofs (sszListSet!_size sszListSet!_getElem!_self sszListSet!_getElem!_ne)

/-- A successful `Except` bind splits into its two successful halves. -/
private theorem except_bind_eq_ok {ε α β : Type} (x : Except ε α) (g : α → Except ε β) (v : β)
    (h : (x >>= g) = .ok v) : ∃ a, x = .ok a ∧ g a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **The loop carries a preorder.** When every step of a `forIn` body relates its input
accumulator to its output by `R`, and `R` is reflexive and transitive, a successful run of the
whole loop relates the start value to the result by `R`. -/
private theorem forIn_rel {σ ε α β : Type} (R : β → β → Prop)
    (hrefl : ∀ b, R b b) (htrans : ∀ a b c, R a b → R b c → R a c)
    (f : α → β → StateT σ (Except ε) (ForInStep β))
    (hstep : ∀ x b st r st', (f x b).run st = .ok (r, st') → R b r.value) :
    ∀ (l : List α) (b : β) (st : σ) (rf : β) (st' : σ),
      (forIn l b f).run st = .ok (rf, st') → R b rf := by
  intro l
  induction l with
  | nil =>
    intro b st rf st' h
    rw [List.forIn_nil, GloasRun.run_pure] at h
    cases h
    exact hrefl b
  | cons x xs ih =>
    intro b st rf st' h
    rw [List.forIn_cons, GloasRun.run_bind] at h
    obtain ⟨⟨r, st₁⟩, hf, hrest⟩ := except_bind_eq_ok _ _ _ h
    have hR := hstep x b st r st₁ hf
    cases r with
    | done b' =>
      rw [GloasRun.run_pure] at hrest
      cases hrest
      exact hR
    | yield b' => exact htrans _ _ _ hR (ih b' st₁ rf st' hrest)

/-- The `min` keeps the builder subtraction at or below the balance. -/
private theorem sub_umin_le (a b : UInt64) : b - umin a b ≤ b := by
  have hmin : umin a b ≤ b := by
    unfold umin
    split
    · exact UInt64.le_of_lt (by assumption)
    · exact UInt64.le_refl _
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hmin]
  omega

variable [Preset] [HasherTag]

/-- The builder registry keeps its size, and no builder balance goes up. -/
def BuildersShrink (r r' : State) : Prop :=
  (sszGet r' builders).size = (sszGet r builders).size ∧
    ∀ i, i < (sszGet r builders).size →
      (sszGet r' builders)[i]!.balance ≤ (sszGet r builders)[i]!.balance

private theorem buildersShrink_refl (r : State) : BuildersShrink r r :=
  ⟨rfl, fun _ _ => UInt64.le_refl _⟩

private theorem buildersShrink_trans (a b c : State) :
    BuildersShrink a b → BuildersShrink b c → BuildersShrink a c := by
  rintro ⟨hab, hab'⟩ ⟨hbc, hbc'⟩
  refine ⟨hbc.trans hab, fun i hi => ?_⟩
  exact UInt64.le_trans (hbc' i (by rw [hab]; exact hi)) (hab' i hi)

/-- A state whose builder registry did not change stands in the relation. -/
private theorem buildersShrink_of_eq (r r' : State)
    (h : sszGet r' builders = sszGet r builders) : BuildersShrink r r' := by
  rw [BuildersShrink, h]
  exact buildersShrink_refl r

/-- One builder write that does not raise the written balance stands in the relation. -/
private theorem buildersShrink_of_set (r : State) (k : Nat) (v : EthCLSpecs.Gloas.Builder)
    (hle : v.balance ≤ (sszGet r builders)[k]!.balance) :
    BuildersShrink r (sszUpdate r with builders[k]! := v) := by
  -- Both `SSZ.Box` flavours read the write back as one `SSZList.set!`.
  have hview : sszGet (sszUpdate r with builders[k]! := v) builders
      = (sszGet r builders).set! k v := by
    rcases r with t | t <;> rfl
  refine ⟨by rw [hview, sszListSet!_size], fun i hi => ?_⟩
  rw [hview]
  by_cases hik : k = i
  · subst hik
    rw [sszListSet!_getElem!_self _ _ _ hi]
    exact hle
  · rw [sszListSet!_getElem!_ne _ _ _ _ hik]
    exact UInt64.le_refl _

/-- **Builder withdrawals never raise a builder balance.** On every successful run of
`applyWithdrawals`, over any withdrawals array, the builder registry keeps its size, and every
builder's final balance is at most its starting balance. -/
theorem applyWithdrawals_buildersShrink (ws : Array Withdrawal) (s s' : State) :
    (applyWithdrawals (StateTransition := GloasRun) ws).run s = .ok ((), s') →
      BuildersShrink s s' := by
  intro h
  unfold applyWithdrawals at h
  rw [GloasRun.run_bind] at h
  obtain ⟨⟨s₀, st₀⟩, hget, h⟩ := except_bind_eq_ok _ _ _ h
  cases hget
  rw [GloasRun.run_bind] at h
  obtain ⟨⟨rf, st₁⟩, hloop, hset⟩ := except_bind_eq_ok _ _ _ h
  cases hset
  rw [← Array.forIn_toList] at hloop
  refine forIn_rel BuildersShrink buildersShrink_refl buildersShrink_trans _ ?_ _ _ _ _ _ hloop
  intro w b st r st' hf
  by_cases hb : EthCLSpecs.Gloas.isBuilderIndex w.validatorIndex = true
  · -- A builder withdrawal: read the builder, then write `balance - min(amount, balance)`.
    simp only [hb, ite_true] at hf
    cases hv : (sszGet b builders).val[(EthCLSpecs.Gloas.toBuilderIndex w.validatorIndex).toNat]?
      with
    | none =>
      simp [sszGetIdx, hv, liftErr, Except.mapError, MonadExcept.ofExcept] at hf
      cases hf
    | some bb =>
      simp [sszGetIdx, hv, liftErr, Except.mapError, MonadExcept.ofExcept] at hf
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, -⟩ := hf
      -- The read found `bb`, so `bb` is the in-range element `[k]!` reads.
      have hbb : (sszGet b builders)[(EthCLSpecs.Gloas.toBuilderIndex w.validatorIndex).toNat]!
          = bb := by
        -- `SSZList`'s `[k]?` is its array's `[k]?`, definitionally.
        have hv' : (sszGet b builders)[(EthCLSpecs.Gloas.toBuilderIndex w.validatorIndex).toNat]?
            = some bb := hv
        rw [getElem!_def, hv']
      apply buildersShrink_of_set
      rw [hbb]
      exact sub_umin_le _ _
  · -- A validator withdrawal goes through `decreaseBalance`, which leaves `builders` alone.
    simp only [hb, Bool.false_eq_true, ite_false] at hf
    unfold EthCLSpecs.Gloas.decreaseBalance at hf
    cases hv : (sszGet b balances).val[w.validatorIndex.toNat]? with
    | none =>
      simp [sszGetIdx, hv, liftErr, Except.mapError, MonadExcept.ofExcept] at hf
      cases hf
    | some bal =>
      simp [sszGetIdx, hv, liftErr, Except.mapError, MonadExcept.ofExcept] at hf
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, -⟩ := hf
      apply buildersShrink_of_eq
      rcases b with t | t <;> rfl

end EthCLSpecs.Proofs.Gloas
