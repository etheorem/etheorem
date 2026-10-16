import EthCLSpecs.Gloas.Withdrawals
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run
import SizzLean.Proofs.SSZListSet
import SizzLean.Proofs.UncachedBox

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
The relation and the theorem bind plain `BeaconState` values. The loop's accumulator is a boxed
state, so the induction relates the views of the accumulators, and the run reads through
`runPure`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLSpecs.Gloas (Preset BeaconState Withdrawal applyWithdrawals)
open EthCLLib.Proofs (run_bind run_pure pureState runPure runPure_eq)
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
    rw [List.forIn_nil, run_pure] at h
    cases h
    exact hrefl b
  | cons x xs ih =>
    intro b st rf st' h
    rw [List.forIn_cons, run_bind] at h
    obtain ⟨⟨r, st₁⟩, hf, hrest⟩ := except_bind_eq_ok _ _ _ h
    have hR := hstep x b st r st₁ hf
    cases r with
    | done b' =>
      rw [run_pure] at hrest
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

variable [Preset]

/-- The builder registry keeps its size, and no builder balance goes up. -/
def BuildersShrink (r r' : BeaconState) : Prop :=
  r'.builders.size = r.builders.size ∧
    ∀ i, i < r.builders.size → r'.builders[i]!.balance ≤ r.builders[i]!.balance

private theorem buildersShrink_refl (r : BeaconState) : BuildersShrink r r :=
  ⟨rfl, fun _ _ => UInt64.le_refl _⟩

private theorem buildersShrink_trans (a b c : BeaconState) :
    BuildersShrink a b → BuildersShrink b c → BuildersShrink a c := by
  rintro ⟨hab, hab'⟩ ⟨hbc, hbc'⟩
  refine ⟨hbc.trans hab, fun i hi => ?_⟩
  exact UInt64.le_trans (hbc' i (by rw [hab]; exact hi)) (hab' i hi)

/-- A state whose builder registry did not change stands in the relation. -/
private theorem buildersShrink_of_eq (r r' : BeaconState) (h : r'.builders = r.builders) :
    BuildersShrink r r' := by
  rw [BuildersShrink, h]
  exact buildersShrink_refl r

/-- One builder write that does not raise the written balance stands in the relation. -/
private theorem buildersShrink_of_set (r : BeaconState) (k : Nat) (v : EthCLSpecs.Gloas.Builder)
    (hle : v.balance ≤ r.builders[k]!.balance) :
    BuildersShrink r { r with builders := r.builders.set! k v } := by
  refine ⟨sszListSet!_size _ _ _, fun i hi => ?_⟩
  by_cases hik : k = i
  · subst hik
    show (r.builders.set! k v)[k]!.balance ≤ _
    rw [sszListSet!_getElem!_self _ _ _ hi]
    exact hle
  · show (r.builders.set! k v)[i]!.balance ≤ _
    rw [sszListSet!_getElem!_ne _ _ _ _ hik]
    exact UInt64.le_refl _

/-- **Builder withdrawals never raise a builder balance.** On every successful run of
`applyWithdrawals`, over any withdrawals array, the builder registry keeps its size, and every
builder's final balance is at most its starting balance. -/
theorem applyWithdrawals_buildersShrink [HasherTag] (ws : Array Withdrawal)
    (s s' : BeaconState) :
    runPure (applyWithdrawals (StateTransition := GloasRun) ws) s = .ok ((), s') →
      BuildersShrink s s' := by
  intro h
  rw [runPure_eq] at h
  -- Split the boxed run, and name its post-state's view as `s'`.
  cases hrun : (applyWithdrawals (StateTransition := GloasRun) ws).run (pureState s) with
  | error e =>
    rw [hrun] at h
    cases h
  | ok p =>
    rw [hrun] at h
    obtain ⟨u, st⟩ := p
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    unfold applyWithdrawals at hrun
    rw [run_bind] at hrun
    obtain ⟨⟨s₀, st₀⟩, hget, hrun⟩ := except_bind_eq_ok _ _ _ hrun
    cases hget
    rw [run_bind] at hrun
    obtain ⟨⟨rf, st₁⟩, hloop, hset⟩ := except_bind_eq_ok _ _ _ hrun
    cases hset
    rw [← Array.forIn_toList] at hloop
    -- The loop's accumulator is the boxed state, so the relation reads the two views.
    refine forIn_rel (fun b b' => BuildersShrink b.view b'.view)
      (fun b => buildersShrink_refl b.view)
      (fun a b c => buildersShrink_trans a.view b.view c.view) _ ?_ _ _ _ _ _ hloop
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
        have hbb : b.view.builders[(EthCLSpecs.Gloas.toBuilderIndex w.validatorIndex).toNat]!
            = bb := by
          -- `SSZList`'s `[k]?` is its array's `[k]?`, definitionally.
          have hv' : b.view.builders[(EthCLSpecs.Gloas.toBuilderIndex w.validatorIndex).toNat]?
              = some bb := hv
          rw [getElem!_def, hv']
        -- Both `SSZ.Box` flavours read the write back as one `SSZList.set!` on the view.
        have hview : ∀ (k : Nat) (v : EthCLSpecs.Gloas.Builder),
            (sszUpdate b with builders[k]! := v).view =
              { b.view with builders := b.view.builders.set! k v } := by
          intro k v
          rcases b with t | t <;> rfl
        show BuildersShrink b.view (sszUpdate b with builders[_]! := _).view
        rw [hview]
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
