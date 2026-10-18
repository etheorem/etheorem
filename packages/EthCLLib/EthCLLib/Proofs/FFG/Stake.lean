import EthCLLib.Proofs.FFG.Model

/-!
# `EthCLLib.Proofs.FFG.Stake`: stake sums over validator lists

Each chain weighs a link with its own stake at the weigh epoch. Accountable safety compares
the weights of the two chains through a reference stake `stake₀` and a reference total
`total₀`. In the refinement, the reference is the stake of the state at the fork point.
`StakeClose` bounds how far the stake of a chain moves from the reference: the sum of the
differences over the validators is at most `d`, and the total falls short by at most `d`.

Every sum here is a sum over a filter of one validator list. Three lemmas carry the proof:

- `stakeSum_filter_or_add_and`: the voters of either link and the voters of both links have
  the same sum as the voters of each link.
- `stakeSum_filter_le`: a filter sums to at most the list.
- `stakeSum_le_add_absDiffSum`: a sum under one stake is at most the sum under the reference,
  plus the drift.

`link_bound_of_close` joins them for one link. Its voters hold two thirds of the reference
total, less `5/3` of the drift. `overlap_bound` then gives a third for the voters of two links.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs.FFG

variable {V R : Type} [DecidableEq V] [DecidableEq R]

/-- The sum of the differences of two weights over a list. -/
def absDiffSum (w w₀ : V → Nat) (xs : List V) : Nat :=
  (xs.map fun v => (w v - w₀ v) + (w₀ v - w v)).sum

/-- The stake of the chain stays within `d` of the reference stake at the epochs from `L` to
`E`. The validator list has no duplicate, and its reference stake is at most the reference
total. -/
def StakeClose (stake₀ : V → Nat) (total₀ : Nat) (c : Chain V R) (L E d : Nat) : Prop :=
  c.vals.Nodup ∧ stakeSum stake₀ c.vals ≤ total₀ ∧
    ∀ e, L ≤ e → e ≤ E → absDiffSum (c.stake e) stake₀ c.vals ≤ d ∧ total₀ ≤ c.total e + d

omit [DecidableEq V] in
/-- The sum over the elements in either filter, plus the sum over the elements in both, is
the sum over each filter. -/
theorem stakeSum_filter_or_add_and (w : V → Nat) (p q : V → Bool) (xs : List V) :
    stakeSum w (xs.filter fun v => p v || q v) + stakeSum w (xs.filter fun v => p v && q v)
      = stakeSum w (xs.filter p) + stakeSum w (xs.filter q) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    unfold stakeSum at ih ⊢
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons, hp, hq, Bool.or_true, Bool.or_false, Bool.and_true,
        Bool.and_false, if_true, Bool.false_eq_true, if_false, List.map_cons, List.sum_cons] <;> omega

omit [DecidableEq V] in
/-- A filter sums to at most the list. -/
theorem stakeSum_filter_le (w : V → Nat) (p : V → Bool) (xs : List V) :
    stakeSum w (xs.filter p) ≤ stakeSum w xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    unfold stakeSum at ih ⊢
    cases hp : p a <;>
      simp only [List.filter_cons, hp, if_true, Bool.false_eq_true, if_false, List.map_cons,
        List.sum_cons] <;> omega

omit [DecidableEq V] in
/-- A sum over a filter under `w` is at most the sum under `w₀`, plus the differences over the
whole list. -/
theorem stakeSum_le_add_absDiffSum (w w₀ : V → Nat) (p : V → Bool) (xs : List V) :
    stakeSum w (xs.filter p) ≤ stakeSum w₀ (xs.filter p) + absDiffSum w w₀ xs := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
    unfold stakeSum absDiffSum at ih ⊢
    cases hp : p a <;>
      simp only [List.filter_cons, hp, if_true, Bool.false_eq_true, if_false, List.map_cons,
        List.sum_cons] <;> omega

/-- The overlap arithmetic: two supermajorities within the drift share a third. `a` and `b` are
the sums of the two voter sets, `u` the sum of their union, and `i` the sum of their
intersection. -/
theorem overlap_bound (a b u i T d₁ d₂ : Nat) (hA : 3 * a + 5 * d₁ ≥ 2 * T)
    (hB : 3 * b + 5 * d₂ ≥ 2 * T) (hu : u ≤ T) (hie : u + i = a + b) :
    3 * i + 5 * (d₁ + d₂) ≥ T := by
  omega

/-- One link within the drift: the voters hold two thirds of the reference total, less `5/3`
of the drift. -/
theorem link_bound (sA sA₀ t t₀ d : Nat) (hl : 3 * sA ≥ 2 * t) (hs : sA ≤ sA₀ + d)
    (ht : t₀ ≤ t + d) : 3 * sA₀ + 5 * d ≥ 2 * t₀ := by
  omega

/-- A link of a chain whose stake stays close to the reference, weighed between `L` and `E`.
Its voters hold two thirds of the reference total under the reference stake, less `5/3` of the
drift. -/
theorem link_bound_of_close {stake₀ : V → Nat} {total₀ L E d : Nat} {c : Chain V R}
    {s t : Checkpoint R} (hl : Link c s t) (hc : StakeClose stake₀ total₀ c L E d)
    (hL : L ≤ t.epoch) (hE : t.epoch + 1 ≤ E) :
    3 * stakeSum stake₀ (linkVoters c s t) + 5 * d ≥ 2 * total₀ := by
  obtain ⟨-, -, -, e, he₁, he₂, hw⟩ := hl
  obtain ⟨hd, ht⟩ := hc.2.2 e (Nat.le_trans hL he₁) (Nat.le_trans he₂ hE)
  have hs := stakeSum_le_add_absDiffSum (c.stake e) stake₀ (voted c s t) c.vals
  exact link_bound _ _ _ _ d hw (by unfold linkVoters; omega) ht

end EthCLLib.Proofs.FFG
