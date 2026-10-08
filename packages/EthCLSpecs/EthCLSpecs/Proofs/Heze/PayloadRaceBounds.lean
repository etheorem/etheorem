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
* **Per-slot committees.** When each validator votes in at most one slot of the window
  (`OneVoteIn`), each slot adds the balance of that slot (`votedBalance_succ`). So two
  conditions give the inequality (`count_of_slots`). In the first slot, the honest balance
  beats the adversarial balance plus the boost. In each later slot, the honest balance is
  at least the adversarial balance. `first_of_fraction` gives the first condition from
  more than 70 % honest balance in that committee.

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

/-- The balance of the validators with the honesty flag `honest` that vote in slot `t`. -/
def slotBalance (vs : List Validator) (honest : Bool) (t : Nat) : Nat :=
  balanceSum (vs.filter fun v => v.honest == honest && v.votes t)

/-- Each validator of `vs` votes in at most one slot of `[lo, hi)`. -/
def OneVoteIn (vs : List Validator) (lo hi : Nat) : Prop :=
  ∀ v ∈ vs, ∀ t t', lo ≤ t → t < hi → lo ≤ t' → t' < hi → v.votes t = true →
    v.votes t' = true → t = t'

/-- A filter by `p || q` splits into the filters by `p` and by `q` when no validator meets
both. -/
theorem balanceSum_filter_or (vs : List Validator) (p q : Validator → Bool)
    (h : ∀ v ∈ vs, ¬ (p v = true ∧ q v = true)) :
    balanceSum (vs.filter fun v => p v || q v)
      = balanceSum (vs.filter p) + balanceSum (vs.filter q) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have ih' := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hv := h v (List.mem_cons_self ..)
    cases hp : p v <;> cases hq : q v <;>
      simp_all [balanceSum, List.foldr_cons] <;> omega

/-- No vote falls in `[lo, s)` when `s ≤ lo`. -/
theorem votedIn_of_le (votes : Nat → Bool) (lo s : Nat) (h : s ≤ lo) :
    votedIn votes lo s = false :=
  Bool.eq_false_iff.mpr fun hv => by
    obtain ⟨t, h1, h2, -⟩ := (votedIn_iff votes lo s).mp hv
    omega

/-- Nothing has voted in the empty window `[lo, lo)`. -/
theorem votedBalance_lo (vs : List Validator) (honest : Bool) (lo : Nat) :
    votedBalance vs honest lo lo = 0 := by
  unfold votedBalance
  rw [List.filter_eq_nil_iff.mpr (fun v _ => by simp [votedIn_of_le v.votes lo lo (Nat.le_refl _)])]
  rfl

/-- One more slot of the window adds the balance of that slot, when each validator votes
in at most one slot of the window. -/
theorem votedBalance_succ (vs : List Validator) (honest : Bool) (lo hi s : Nat)
    (hone : OneVoteIn vs lo hi) (hlo : lo ≤ s) (hs : s < hi) :
    votedBalance vs honest lo (s + 1) = votedBalance vs honest lo s + slotBalance vs honest s := by
  unfold votedBalance slotBalance
  have hsplit : (vs.filter fun v => v.honest == honest && votedIn v.votes lo (s + 1))
      = vs.filter fun v => (v.honest == honest && votedIn v.votes lo s) ||
          (v.honest == honest && v.votes s) := by
    apply List.filter_congr
    intro v _
    simp only [votedIn, decide_eq_true hlo, Bool.true_and]
    cases v.honest == honest <;> cases v.votes s <;> simp
  rw [hsplit, balanceSum_filter_or]
  intro v hv ⟨h1, h2⟩
  simp only [Bool.and_eq_true] at h1 h2
  obtain ⟨t, hlt, hts, hvt⟩ := (votedIn_iff v.votes lo s).mp h1.2
  have := hone v hv t s hlt (by omega) hlo hs hvt h2.2
  omega

/-- The counting inequality from per-slot conditions. The first slot carries the boost. Each
later slot adds at least as much honest as adversarial balance. -/
theorem count_of_slots (vs : List Validator) (lo hi boost : Nat) (hone : OneVoteIn vs lo hi)
    (hfirst : slotBalance vs false lo + boost < slotBalance vs true lo)
    (hlater : ∀ t, lo < t → t < hi → slotBalance vs false t ≤ slotBalance vs true t) :
    ∀ s, lo < s → s ≤ hi → advVoted vs lo s + boost < honestVoted vs lo s := by
  intro s
  induction s with
  | zero => intro h; omega
  | succ s ih =>
    intro hlt hle
    unfold advVoted honestVoted
    rw [votedBalance_succ vs false lo hi s hone (by omega) (by omega),
      votedBalance_succ vs true lo hi s hone (by omega) (by omega)]
    by_cases hs : s = lo
    · subst hs
      rw [votedBalance_lo, votedBalance_lo]
      omega
    · have h1 := ih (by omega) (by omega)
      unfold advVoted honestVoted at h1
      have := hlater s (by omega) (by omega)
      omega

/-- The 70 % form of the first-slot condition. The committee has honest balance `H` and
adversarial balance `A`. The committee weight `cw` is at most `H + A`, and the boost
percentage `pct` is at most `40`. Then more than 70 % honest balance beats the adversarial
balance plus the proposer score `cw * pct / 100`. -/
theorem first_of_fraction (H A cw pct : Nat) (hpct : pct ≤ 40) (hcw : cw ≤ H + A)
    (h70 : 70 * (H + A) < 100 * H) :
    A + cw * pct / 100 < H := by
  have h1 : cw * pct ≤ cw * 40 := Nat.mul_le_mul_left _ hpct
  have h2 : cw * pct / 100 ≤ cw * 40 / 100 := Nat.div_le_div_right h1
  omega

end EthCLSpecs.Proofs.Heze.PayloadRace
