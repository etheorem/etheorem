import EthCLSpecs.Proofs.Heze.EbUpdates

/-!
# `EthCLSpecs.Proofs.Heze.DriftDefs`: the reads and the move of the stake drift

The drift bound follows each validator of a list `vals` along a chain run. This module names
the per-validator reads on a plain state, in `Nat`, and the move that the balance writers
cause.

- `balN`, `ebN`, `maxN`: the balance, the effective balance and the cap of the effective
  balance (`get_max_effective_balance`) of index `i`. An index past the registry reads zero.
- `capN`: the balance capped at `maxN`. `process_effective_balance_updates` rounds this value
  (`EbUpdates.lean`).
- `liveB st₀ E i`: index `i` can still count at epoch `E`. Either `st₀` has no validator at
  `i`, or its withdrawable epoch lies after `E + 1`. A validator outside this set has exited by
  epoch `E - 1`, so it is not active at `E - 1` or `E`.
- `moveN vals st₀ E a b`: the sum, over the live indices of `vals`, of the distance of the
  capped balances in `a` and `b`. It meets the triangle inequality (`moveN_triangle`), and a
  change of one balance moves it by at most the change (`moveN_balance_le`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset BeaconState ValidatorIndex Validator Gwei)

/-! ## A lower bound on `isqrt` -/

/-- Two numbers that add to `2 s`, the smaller one `a`, multiply to at most `s * s`. -/
theorem mul_two_sub_le {a s : Nat} (ha : a ≤ s) : a * (2 * s - a) ≤ s * s := by
  have e1 : 2 * s - a = s + (s - a) := by omega
  rw [e1, Nat.mul_add]
  have h1 : a * (s - a) ≤ s * (s - a) := Nat.mul_le_mul_right _ ha
  have h2 : a * s + s * (s - a) = s * s := by
    rw [Nat.mul_comm a s, ← Nat.mul_add, Nat.add_sub_cancel' ha]
  omega

/-- `x (2 s - x) ≤ s * s` for every `x`. -/
theorem mul_two_sub_le' (x s : Nat) : x * (2 * s - x) ≤ s * s := by
  rcases Nat.le_total x s with h | h
  · exact mul_two_sub_le h
  · rcases Nat.le_total x (2 * s) with h' | h'
    · have e : 2 * s - (2 * s - x) = x := by omega
      have := mul_two_sub_le (a := 2 * s - x) (s := s) (by omega)
      rw [e, Nat.mul_comm] at this
      exact this
    · rw [show 2 * s - x = 0 by omega, Nat.mul_zero]
      exact Nat.zero_le _

/-- One Newton step from `x > 0` stays at least any `s` with `s * s ≤ n`. -/
theorem newton_step_ge {n x s : Nat} (hx : 0 < x) (hs : s * s ≤ n) : s ≤ (x + n / x) / 2 := by
  rcases Nat.lt_or_ge ((x + n / x) / 2) s with h | h
  · exfalso
    -- `x + n / x ≤ 2 s - 1`, so `n < x (n / x + 1) ≤ x (2 s - x) ≤ s * s`.
    have h1 : x + n / x + 1 ≤ 2 * s := by omega
    have h2 : n < x * (n / x + 1) := Nat.lt_mul_div_succ n hx
    have h3 : x * (n / x + 1) ≤ x * (2 * s - x) := Nat.mul_le_mul_left _ (by omega)
    have h4 := mul_two_sub_le' x s
    omega
  · exact h

/-- Every iterate of the Newton loop from `x > 0` stays at least `s`. -/
theorem isqrtAux_ge {n s : Nat} (hs : s * s ≤ n) :
    ∀ (fuel x : Nat), 0 < x → s ≤ x → s ≤ isqrtAux n fuel x
  | 0, x, _, hx => by unfold isqrtAux; exact hx
  | fuel + 1, x, hx0, hx => by
    unfold isqrtAux
    dsimp only
    split
    · rename_i hy
      have hy0 : 0 < (x + n / x) / 2 ∨ s = 0 := by
        rcases Nat.eq_zero_or_pos s with h | h
        · exact .inr h
        · exact .inl (Nat.lt_of_lt_of_le h (newton_step_ge hx0 hs))
      rcases hy0 with hy0 | rfl
      · exact isqrtAux_ge hs fuel _ hy0 (newton_step_ge hx0 hs)
      · exact Nat.zero_le _
    · exact hx

/-- `isqrt n` is at least any `s` with `s * s ≤ n`. -/
theorem le_isqrt {n s : Nat} (hs : s * s ≤ n) : s ≤ isqrt n := by
  unfold isqrt
  split
  · rename_i h
    subst h
    have : s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact h
      · have := Nat.mul_le_mul h h; omega
    omega
  · rename_i h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    have hsn : s ≤ n := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · omega
      · exact Nat.le_trans (Nat.le_mul_of_pos_left s h0) hs
    exact isqrtAux_ge hs 200 n hn hsn

/-- `umin` is the smaller value. -/
theorem umin_toNat (a b : UInt64) : (umin a b).toNat = min a.toNat b.toNat := by
  unfold umin
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt] at h
    omega
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt] at h
    omega

section
variable [Preset]

/-- The balance of index `i`, or zero past the end. -/
def balN (u : BeaconState) (i : Nat) : Nat := (u.balances.val[i]?.getD 0).toNat

/-- The effective balance of index `i`, or zero past the registry. -/
def ebN (u : BeaconState) (i : Nat) : Nat :=
  match u.validators.val[i]? with
  | some v => v.effectiveBalance.toNat
  | none => 0

/-- The cap of the effective balance of index `i`, or zero past the registry. -/
def maxN (u : BeaconState) (i : Nat) : Nat :=
  match u.validators.val[i]? with
  | some v => (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat
  | none => 0

/-- The balance of index `i` capped at the cap of its effective balance. -/
def capN (u : BeaconState) (i : Nat) : Nat := min (balN u i) (maxN u i)

/-- Index `i` can still count at epoch `E`: `st₀` has no validator there, or its withdrawable
epoch lies after `E + 1`. -/
def liveB (st₀ : BeaconState) (E : Nat) (i : Nat) : Bool :=
  match st₀.validators.val[i]? with
  | some v => decide (E + 1 < v.withdrawableEpoch.toNat)
  | none => true

/-- The move of the capped balances from `a` to `b`, over the live indices of `vals`. -/
def moveN (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat) (a b : BeaconState) :
    Nat :=
  ((vals.filter fun i => liveB st₀ E i.toNat).map fun i =>
    absDiff (capN b i.toNat) (capN a i.toNat)).sum

theorem moveN_self (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat) (a : BeaconState) :
    moveN vals st₀ E a a = 0 := by
  unfold moveN
  induction (vals.filter fun i => liveB st₀ E i.toNat) with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, absDiff_self] at ih ⊢
    rw [ih]

theorem moveN_triangle (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat)
    (a b c : BeaconState) :
    moveN vals st₀ E a c ≤ moveN vals st₀ E a b + moveN vals st₀ E b c := by
  unfold moveN
  rw [← sum_map_add]
  exact sum_map_le_sum_map _ _ (fun i => by
    have := absDiff_triangle (capN c i.toNat) (capN b i.toNat) (capN a i.toNat)
    omega) _

omit [Preset] in
/-- A sum over a list of distinct indices, whose summand vanishes away from one index `j` and
is at most `d` there, is at most `d`. -/
theorem sum_le_of_single (f : ValidatorIndex → Nat) (j : Nat) (d : Nat) :
    ∀ l : List ValidatorIndex, l.Nodup → (∀ i ∈ l, i.toNat ≠ j → f i = 0) →
      (∀ i ∈ l, f i ≤ d) → (l.map f).sum ≤ d
  | [], _, _, _ => Nat.zero_le _
  | x :: l, hnd, h0, h1 => by
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    by_cases hxj : x.toNat = j
    · -- The other indices differ from `x`, so they differ from `j`.
      have hz : (l.map f).sum = 0 := by
        have : ∀ y ∈ l, f y = 0 := fun y hy => h0 y (List.mem_cons_of_mem _ hy) (fun hyj => hx
          (by rw [UInt64.toNat_inj.mp (hxj.trans hyj.symm)]; exact hy))
        clear h0 h1 hnd hnd' hx
        induction l with
        | nil => rfl
        | cons y l ih =>
          simp only [List.map_cons, List.sum_cons, this y List.mem_cons_self, Nat.zero_add]
          exact ih (fun z hz => this z (List.mem_cons_of_mem _ hz))
      rw [hz]
      exact h1 x List.mem_cons_self
    · rw [h0 x List.mem_cons_self hxj, Nat.zero_add]
      exact sum_le_of_single f j d l hnd' (fun i hi => h0 i (List.mem_cons_of_mem _ hi))
        (fun i hi => h1 i (List.mem_cons_of_mem _ hi))

/-- A write of one balance moves `moveN` by at most the change of that balance. -/
theorem moveN_balance_le (vals : List ValidatorIndex) (hnd : vals.Nodup) (st₀ : BeaconState)
    (E : Nat) (a : BeaconState) (j : Nat) (x : Gwei) :
    moveN vals st₀ E a { a with balances := a.balances.set! j x } ≤
      absDiff x.toNat (balN a j) := by
  unfold moveN
  refine sum_le_of_single _ j _ _ (hnd.filter _) (fun i _ hij => ?_) (fun i _ => ?_)
  · have : capN { a with balances := a.balances.set! j x } i.toNat = capN a i.toNat := by
      unfold capN balN maxN
      show min ((a.balances.val.setIfInBounds j x)[i.toNat]?.getD 0).toNat _ = _
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm hij)]
    rw [this, absDiff_self]
  · unfold capN maxN
    refine Nat.le_trans (absDiff_min_le _ _ _ _) ?_
    rw [absDiff_self, Nat.add_zero]
    unfold balN
    show absDiff ((a.balances.val.setIfInBounds j x)[i.toNat]?.getD 0).toNat _ ≤ _
    by_cases hij : i.toNat = j
    · rw [hij, Array.getElem?_setIfInBounds_self]
      split
      · exact Nat.le_refl _
      · rename_i hge
        rw [Array.getElem?_eq_none (by omega)]
        simp only [Option.getD_none, UInt64.toNat_zero, absDiff_self]
        exact Nat.zero_le _
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hij), absDiff_self]
      exact Nat.zero_le _

end

end EthCLSpecs.Proofs.Heze
