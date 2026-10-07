import EthCLSpecs.Proofs.Heze.PayloadRace

/-!
# `EthCLSpecs.Proofs.Heze.PayloadRaceBounds`: the honesty bound of the payload race

`race_empty_persists` takes a counting inequality per slot. This module derives that
inequality from two common assumptions.

* **Uniform committees.** Each slot of the window adds at least `h` honest and at most
  `W - h` adversarial balance. One committee with `W + boost < 2 * h` is enough for every
  slot of a window of at most one epoch (`race_empty_persists_of_fraction`). With
  `W = 100 * u` and the boost `40 * u` of `PROPOSER_SCORE_BOOST = 40`, the condition is
  `h > 70 * u`, the 70 % bound (`seventy_percent`).
* **Honest proposers.** No boost reaches FULL, so `boost = 0`. The honest balance only
  has to be more than the adversarial balance (`race_empty_persists_honest_proposers`).

At the first slot, `N + 2`, one committee of honest votes meets the whole boost. At slot
`N + 1 + j` alone the uniform condition is `j * (2 * h - W) > boost`, which is weaker. The
theorem needs the condition at every slot, so the first slot sets the bound.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze.PayloadRace

/-- One committee with `W + boost < 2 * h` gives the counting inequality for `j ≥ 1`
committees. -/
theorem count_of_fraction (j h W boost : Nat) (hj : 1 ≤ j) (hhW : h ≤ W)
    (hone : W + boost < 2 * h) :
    j * (W - h) + boost < j * h := by
  have hd : h = (W - h) + (2 * h - W) := by omega
  have hpos : 2 * h - W ≤ j * (2 * h - W) := Nat.le_mul_of_pos_left _ hj
  have hsplit : j * h = j * (W - h) + j * (2 * h - W) := by
    conv => lhs; rw [hd]
    rw [Nat.mul_add]
  omega

/-- The 70 % bound: a committee of balance `100 * u` and a boost of `40 * u`. -/
theorem seventy_percent (u h : Nat) :
    100 * u + 40 * u < 2 * h ↔ 70 * u < h := by
  omega

/-- `race_empty_persists` under uniform committees. In `[lo, s)`, the honest balance that
has voted is at least `(s - lo) * h`. The adversarial balance is at most
`(s - lo) * (W - h)`.

`honestVoted` counts each validator once, and a validator votes once per epoch. So
`hhonest` can hold only while `hi - lo` is at most one epoch of slots. -/
theorem race_empty_persists_of_fraction (vs : List Validator)
    (choice : Validator → Nat → Side) (lo hi boost W h : Nat)
    (view : Validator → Nat → Validator → Side)
    (hrace : RaceHypotheses vs choice lo hi boost view)
    (hhW : h ≤ W) (hone : W + boost < 2 * h)
    (hhonest : ∀ s, lo < s → s ≤ hi → (s - lo) * h ≤ honestVoted vs lo s)
    (hadv : ∀ s, lo < s → s ≤ hi → advVoted vs lo s ≤ (s - lo) * (W - h)) :
    RaceOutcome vs choice lo hi boost := by
  refine race_empty_persists vs choice lo hi boost view hrace ?_
  intro s hs hsh
  have hc := count_of_fraction (s - lo) h W boost (by omega) hhW hone
  have h1 := hhonest s hs hsh
  have h2 := hadv s hs hsh
  omega

/-- `race_empty_persists` with honest proposers: no boost reaches FULL. -/
theorem race_empty_persists_honest_proposers (vs : List Validator)
    (choice : Validator → Nat → Side) (lo hi : Nat)
    (view : Validator → Nat → Validator → Side)
    (hrace : RaceHypotheses vs choice lo hi 0 view)
    (hcount : ∀ s, lo < s → s ≤ hi → advVoted vs lo s < honestVoted vs lo s) :
    RaceOutcome vs choice lo hi 0 :=
  race_empty_persists vs choice lo hi 0 view hrace
    (fun s hs hsh => by simpa using hcount s hs hsh)

end EthCLSpecs.Proofs.Heze.PayloadRace
