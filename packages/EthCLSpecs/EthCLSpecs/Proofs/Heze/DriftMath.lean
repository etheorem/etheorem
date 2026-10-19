/-!
# `EthCLSpecs.Proofs.Heze.DriftMath`: the arithmetic of the stake drift

The stake drift of a chain run compares the link stake of each validator at the end of the run
with its link stake at the fork point (`StakeDrift.lean`). This module holds the `Nat` facts
that the comparison needs, apart from any beacon state.

- `absDiff a b` is the distance `|a - b|` in `Nat`. It is symmetric and it meets the triangle
  inequality. `min` with a cap moves it by at most the move of the cap.
- `absDiff_gate_le`: the distance of two gated values. A validator counts its effective
  balance only when it is active, so the distance splits into the distance of the effective
  balances and a term for a change of the gate.
- The hysteresis rule of `process_effective_balance_updates`. `ebUpdate` restates it on `Nat`.
  After an update, the effective balance lies within `max up inc` of the capped balance
  (`ebUpdate_near`). An update that changes the effective balance needs a capped balance
  more than `down` away from it (`ebUpdate_far`).
- `EbTrack`: the invariant of one validator along a run. Its effective balance is still the
  one of the fork point, or the capped balance has moved by more than `down` and the effective
  balance stays within a known distance. `EbTrack.step` keeps it over an update, and
  `EbTrack.bound` turns it into a bound on the distance.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

/-! ## Updates of a ghost -/

/-- The function `f` with the value `y` at `j`. -/
def fupd {β : Type} (f : Nat → β) (j : Nat) (y : β) : Nat → β := fun k => if k = j then y else f k

theorem fupd_ne {β : Type} (f : Nat → β) {j k : Nat} (y : β) (h : k ≠ j) : fupd f j y k = f k := by
  unfold fupd; rw [if_neg h]

theorem fupd_self {β : Type} (f : Nat → β) (j : Nat) (y : β) : fupd f j y j = y := by
  unfold fupd; rw [if_pos rfl]

/-! ## Distances in `Nat` -/

/-- The distance of two natural numbers. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

theorem absDiff_comm (a b : Nat) : absDiff a b = absDiff b a := by
  unfold absDiff; omega

theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  unfold absDiff; omega

theorem absDiff_triangle (a b c : Nat) : absDiff a c ≤ absDiff a b + absDiff b c := by
  unfold absDiff; omega

theorem le_add_absDiff (a b : Nat) : a ≤ b + absDiff a b := by
  unfold absDiff; omega

/-- A cap moves the distance by at most the move of the cap. -/
theorem absDiff_min_le (a b m m' : Nat) :
    absDiff (min a m) (min b m') ≤ absDiff a b + absDiff m m' := by
  unfold absDiff; omega

/-- The distance of two gated values: the distance of the values when the first gate is open,
plus the second value when the gates differ. -/
theorem absDiff_gate_le (p q : Bool) (x y : Nat) :
    absDiff (if p then x else 0) (if q then y else 0) ≤
      (if p then absDiff x y else 0) + (if p = q then 0 else y) := by
  cases p <;> cases q <;> simp [absDiff] <;> omega

/-- The distance from zero is the value. -/
theorem absDiff_zero_right (a : Nat) : absDiff a 0 = a := by
  unfold absDiff; omega

/-! ## Sums -/

/-- Two floors of quotients add to at most the floor of the quotient of the sum. -/
theorem add_div_le_div_add (a b d : Nat) : a / d + b / d ≤ (a + b) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.le_div_iff_mul_le hd, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a d) (Nat.div_mul_le_self b d)

/-- A sum of floors of quotients is at most the floor of the quotient of the sum. -/
theorem sum_map_div_le {α : Type} (f : α → Nat) (d : Nat) :
    ∀ l : List α, (l.map fun x => f x / d).sum ≤ (l.map f).sum / d
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    have ih := sum_map_div_le f d l
    exact Nat.le_trans (Nat.add_le_add_left ih _) (add_div_le_div_add _ _ _)

/-- A sum is monotone in its summand. -/
theorem sum_map_le_sum_map {α : Type} (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    ∀ l : List α, (l.map f).sum ≤ (l.map g).sum
  | [] => Nat.le_refl _
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x) (sum_map_le_sum_map f g h l)

/-- A sum is monotone in its summand on the list. -/
theorem sum_map_le_sum_map_mem {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self)
      (sum_map_le_sum_map_mem f g l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A sum of two summands is the sum of the two sums. -/
theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ l : List α, (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_add f g l]
    omega

/-- A constant factor comes out of a sum. -/
theorem sum_map_mul_left {α : Type} (a : Nat) (f : α → Nat) :
    ∀ l : List α, (l.map fun x => a * f x).sum = a * (l.map f).sum
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_mul_left a f l, Nat.mul_add]

/-! ## The hysteresis rule -/

/-- The update of one effective balance `eb` with the balance `b` and the cap `m`, on `Nat`.
The thresholds are `down` and `up`, and the floor rounds to a multiple of `inc`. -/
def ebUpdate (inc down up eb b m : Nat) : Nat :=
  if b + down < eb ∨ eb + up < b then min (b - b % inc) m else eb

/-- The capped balance. -/
def capBal (b m : Nat) : Nat := min b m

/-- After an update, the effective balance lies within `max up inc` of the capped balance.
It needs the effective balance at most the cap. -/
theorem ebUpdate_near {inc down up eb b m : Nat} (hinc : 0 < inc) (hdu : down ≤ up)
    (hm : eb ≤ m) :
    absDiff (ebUpdate inc down up eb b m) (capBal b m) ≤ max up inc := by
  have hmod := Nat.mod_lt b hinc
  have hle := Nat.mod_le b inc
  unfold ebUpdate capBal absDiff
  split <;> rename_i h
  · rcases Nat.le_total b m with hbm | hbm
    · rw [Nat.min_eq_left hbm, Nat.min_eq_left (Nat.le_trans (Nat.sub_le _ _) hbm)]
      omega
    · rw [Nat.min_eq_right hbm]
      omega
  · omega

/-- An update keeps the effective balance at most the cap. -/
theorem ebUpdate_le_cap (inc down up : Nat) {eb b m : Nat} (hm : eb ≤ m) :
    ebUpdate inc down up eb b m ≤ m := by
  unfold ebUpdate
  split
  · exact Nat.min_le_right _ _
  · exact hm

/-- An update that changes the effective balance needs a capped balance more than `down` away
from it. It needs the effective balance and the cap to be multiples of `inc`, and `down` below
`inc`. -/
theorem ebUpdate_far {inc down up eb b m : Nat} (hdu : down ≤ up)
    (hdi : down < inc) (hm : eb ≤ m) (heb : eb % inc = 0) (hmi : m % inc = 0)
    (hne : ebUpdate inc down up eb b m ≠ eb) : down < absDiff eb (capBal b m) := by
  unfold ebUpdate at hne
  unfold capBal absDiff
  split at hne
  · rename_i h
    rcases h with h | h
    · omega
    · rcases Nat.le_total b m with hbm | hbm
      · rw [Nat.min_eq_left hbm]; omega
      · rw [Nat.min_eq_right hbm]
        -- Above the cap the floor stays at the cap, so a change needs `eb` below the cap.
        have hfl : m ≤ b - b % inc := by
          have h1 : b - b % inc = inc * (b / inc) := by
            have := Nat.div_add_mod b inc; omega
          have h2 : m = inc * (m / inc) := by
            have := Nat.div_add_mod m inc; omega
          rw [h1, h2]
          exact Nat.mul_le_mul_left _ (Nat.div_le_div_right hbm)
        rw [Nat.min_eq_right hfl] at hne
        -- Two distinct multiples of `inc` lie at least `inc` apart.
        have h3 : eb + inc ≤ m := by
          have h4 : eb = inc * (eb / inc) := by
            have := Nat.div_add_mod eb inc; omega
          have h5 : m = inc * (m / inc) := by
            have := Nat.div_add_mod m inc; omega
          have h6 : eb / inc < m / inc := by
            rcases Nat.lt_or_ge (eb / inc) (m / inc) with h7 | h7
            · exact h7
            · exfalso
              have : m ≤ eb := by rw [h4, h5]; exact Nat.mul_le_mul_left _ h7
              omega
          rw [h4, h5]
          have := Nat.mul_le_mul_left inc (Nat.succ_le_of_lt h6)
          rw [Nat.mul_succ] at this
          omega
        omega
  · exact absurd rfl hne

/-! ## The invariant of one validator -/

/-- The effective balance `eb` of one validator, against its effective balance `eb₀` at the
fork point. `e₀` is the distance of the capped balance from the effective balance at the fork
point, and `v` bounds the move of the capped balance since then. `a` is the distance after an
update (`max up inc`). -/
def EbTrack (down a eb eb₀ e₀ v : Nat) : Prop :=
  eb = eb₀ ∨ (down < e₀ + v ∧ absDiff eb eb₀ ≤ a + e₀ + v)

/-- The invariant holds at the fork point. -/
theorem EbTrack.init (down a eb₀ e₀ v : Nat) : EbTrack down a eb₀ eb₀ e₀ v := .inl rfl

/-- A larger move bound keeps the invariant. -/
theorem EbTrack.mono {down a eb eb₀ e₀ v v' : Nat} (h : EbTrack down a eb eb₀ e₀ v)
    (hv : v ≤ v') : EbTrack down a eb eb₀ e₀ v' := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨by omega, by omega⟩

/-- The invariant survives an update of the effective balance `eb` to `eb'`. The update leaves
`eb'` within `a` of the capped balance `c`, and it keeps `eb` when `c` lies within `down` of
`eb`. The capped balance has moved by at most `v` from its value `c₀` at the fork point. -/
theorem EbTrack.step {down a eb eb' eb₀ c c₀ v : Nat}
    (h : EbTrack down a eb eb₀ (absDiff c₀ eb₀) v)
    (hnear : absDiff eb' c ≤ a) (hfar : eb' ≠ eb → down < absDiff eb c)
    (hv : absDiff c c₀ ≤ v) : EbTrack down a eb' eb₀ (absDiff c₀ eb₀) v := by
  by_cases hne : eb' = eb
  · rw [hne]; exact h
  · have hf := hfar hne
    have t1 := absDiff_triangle eb' c c₀
    have t2 := absDiff_triangle eb' c₀ eb₀
    refine .inr ⟨?_, by omega⟩
    rcases h with rfl | ⟨h1, -⟩
    · have t3 := absDiff_triangle eb c₀ c
      rw [absDiff_comm eb c₀] at t3
      rw [absDiff_comm c c₀] at hv
      omega
    · exact h1

/-- The invariant bounds the distance of the effective balances. The second summand is the
cost of the first change, spread over the move. -/
theorem EbTrack.bound {down a eb eb₀ e₀ v : Nat} (h : EbTrack down a eb eb₀ e₀ v) :
    absDiff eb eb₀ ≤ (e₀ + v) + a * (e₀ + v) / (down + 1) := by
  rcases h with rfl | ⟨h1, h2⟩
  · rw [absDiff_self]; exact Nat.zero_le _
  · have : a ≤ a * (e₀ + v) / (down + 1) :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (Nat.mul_le_mul_left _ h1)
    omega

end EthCLSpecs.Proofs.Heze
