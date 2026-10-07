/-!
# `EthCLSpecs.Proofs.Heze.PayloadRace`: the race between EMPTY and FULL at one block

Tier T2 of the censorship-resistance argument. A block `r` at slot `N` has a payload
whose inclusion-list answer is `false`. In slot `N + 1` the payload tiebreak takes every
honest head to the EMPTY node of `r` (`Proofs/Heze/HeadAvoidsFull.lean`). From slot
`N + 2` on, `get_weight` decides between the EMPTY and the FULL node of `r`. This module
models that comparison. It proves that EMPTY stays strictly ahead while the honest
balance that has voted exceeds the adversarial balance plus the proposer boost.

The model does not read the store. A validator has a balance, an honesty flag, and
the slots where it votes. A vote puts the validator on one side of `r`: `empty`, `full`,
or `neither`. A node's view assigns each validator the side of its latest message as that
node sees it. `sideWeight` sums the balances on one side, the same filtered sum as
`get_attestation_score`. The adversary chooses its own votes, every view's entry for an
adversarial validator, and the boost up to the bound `boost`.

The setting: every honest head of slots `N + 1 .. N + k` reaches `pending r`. Then an
honest vote is on `empty` or on `full`. An honest head off the subtree of `r` votes
`neither`, and the model does not cover that case.

Three facts of the pinned fork choice fix the shape of the model:

* A vote of slot `N` or earlier supports no child of `pending r`. So the window of
  counted votes starts at `lo = N + 1`.
* A tie goes to FULL, because the tiebreak off the decision slot is the raw status
  (`FULL = 1 > EMPTY = 0`). So EMPTY must win strictly (`EmptyAhead`).
* The boost always reaches FULL when the adversary builds its block on FULL, because the
  parent `r` is two slots back. So the model charges the full `boost` at every slot.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze.PayloadRace

/-- The side of `r` that a latest message supports. `neither` covers a message for an
ancestor of `r`, for `pending r` itself, or for another branch. It also covers an
equivocator. -/
inductive Side
  | empty
  | full
  | neither
  deriving DecidableEq, Repr

/-- A validator of the abstract race. `votes t` says whether it attests in slot `t`.
`index` is the validator index. It keeps two validators with the same balance, flag, and
vote slots apart, so that each one has its own vote and its own entry in a view. -/
structure Validator where
  index : Nat
  balance : Nat
  honest : Bool
  votes : Nat → Bool

/-- The sum of the balances of a list of validators. -/
def balanceSum (vs : List Validator) : Nat :=
  vs.foldr (fun v acc => v.balance + acc) 0

/-- `votedIn votes lo s` says whether the validator votes in some slot of `[lo, s)`. -/
def votedIn (votes : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => false
  | s + 1 => (decide (lo ≤ s) && votes s) || votedIn votes lo s

/-- The side of the latest vote in `[lo, s)`, or `neither` when there is no such vote.
`choice t` is the side of the vote in slot `t`. -/
def latestSide (votes : Nat → Bool) (choice : Nat → Side) (lo : Nat) : Nat → Side
  | 0 => .neither
  | s + 1 => if decide (lo ≤ s) && votes s then choice s else latestSide votes choice lo s

/-- The balance on one side of `r` in a view. -/
def sideWeight (vs : List Validator) (view : Validator → Side) (side : Side) : Nat :=
  balanceSum (vs.filter fun v => decide (view v = side))

/-- The balance of the validators with the honesty flag `honest` that vote in
`[lo, s)`. -/
def votedBalance (vs : List Validator) (honest : Bool) (lo s : Nat) : Nat :=
  balanceSum (vs.filter fun v => v.honest == honest && votedIn v.votes lo s)

/-- The honest balance that votes in `[lo, s)`. -/
abbrev honestVoted (vs : List Validator) (lo s : Nat) : Nat := votedBalance vs true lo s

/-- The adversarial balance that votes in `[lo, s)`. -/
abbrev advVoted (vs : List Validator) (lo s : Nat) : Nat := votedBalance vs false lo s

/-- EMPTY wins in a view against FULL plus a boost of `boost`. The comparison is strict,
because a tie goes to FULL. -/
def EmptyAhead (vs : List Validator) (view : Validator → Side) (boost : Nat) : Prop :=
  sideWeight vs view .full + boost < sideWeight vs view .empty

/-- `EmptyAhead` is a comparison of two `Nat` values, so `decide` evaluates it. -/
instance (vs : List Validator) (view : Validator → Side) (boost : Nat) :
    Decidable (EmptyAhead vs view boost) :=
  inferInstanceAs (Decidable (_ < _))

/-- A view of slot `s` that synchrony allows. The view holds the latest vote in `[lo, s)` of
every honest validator. A validator sits on `full` only after a vote in `[lo, s)`. -/
def ViewOk (vs : List Validator) (choice : Validator → Nat → Side) (lo s : Nat)
    (view : Validator → Side) : Prop :=
  ∀ w ∈ vs, (w.honest = true → view w = latestSide w.votes (choice w) lo s) ∧
    (view w = .full → votedIn w.votes lo s = true)

/-- Every honest vote in `[lo, s)` is on `empty`. -/
def HonestEmpty (vs : List Validator) (choice : Validator → Nat → Side) (lo s : Nat) : Prop :=
  ∀ w ∈ vs, w.honest = true → ∀ t, lo ≤ t → t < s → w.votes t = true → choice w t = .empty

/-- A filter that keeps more validators has at least the same balance. -/
theorem balanceSum_filter_mono (vs : List Validator) (p q : Validator → Bool)
    (h : ∀ v ∈ vs, p v = true → q v = true) :
    balanceSum (vs.filter p) ≤ balanceSum (vs.filter q) := by
  induction vs with
  | nil => exact Nat.le_refl _
  | cons v vs ih =>
    have ih' := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    by_cases hp : p v = true
    · have hq := h v (List.mem_cons_self ..) hp
      simp only [List.filter_cons, hp, hq, if_true, balanceSum, List.foldr_cons]
      exact Nat.add_le_add_left ih' _
    · cases hq : q v <;> simp_all [balanceSum, List.foldr_cons] <;> omega

/-- `votedIn` holds exactly when a vote exists in the window. -/
theorem votedIn_iff (votes : Nat → Bool) (lo : Nat) :
    ∀ s, votedIn votes lo s = true ↔ ∃ t, lo ≤ t ∧ t < s ∧ votes t = true
  | 0 => by simp [votedIn]
  | s + 1 => by
    rw [votedIn, Bool.or_eq_true, votedIn_iff votes lo s]
    constructor
    · rintro (h | ⟨t, h1, h2, h3⟩)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨s, h.1, Nat.lt_succ_self _, h.2⟩
      · exact ⟨t, h1, Nat.lt_succ_of_lt h2, h3⟩
    · rintro ⟨t, h1, h2, h3⟩
      by_cases ht : t = s
      · subst ht; left; simp [h1, h3]
      · right; exact ⟨t, h1, by omega, h3⟩

/-- When every vote in `[lo, s)` is on `empty` and one exists, the latest side is
`empty`. -/
theorem latestSide_empty (votes : Nat → Bool) (choice : Nat → Side) (lo : Nat) :
    ∀ s, (∀ t, lo ≤ t → t < s → votes t = true → choice t = .empty) →
      votedIn votes lo s = true → latestSide votes choice lo s = .empty
  | 0, _, hv => by simp [votedIn] at hv
  | s + 1, h, hv => by
    rw [latestSide]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact h s hc.1 (Nat.lt_succ_self _) hc.2
    · rename_i hc
      have hv' : votedIn votes lo s = true := by
        rw [votedIn, Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact absurd hv hc
        · exact hv
      exact latestSide_empty votes choice lo s
        (fun t h1 h2 h3 => h t h1 (Nat.lt_succ_of_lt h2) h3) hv'

/-- When every vote in `[lo, s)` is on `empty`, the latest side is not `full`. -/
theorem latestSide_ne_full (votes : Nat → Bool) (choice : Nat → Side) (lo : Nat) :
    ∀ s, (∀ t, lo ≤ t → t < s → votes t = true → choice t = .empty) →
      latestSide votes choice lo s ≠ .full
  | 0, _ => by simp [latestSide]
  | s + 1, h => by
    rw [latestSide]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [h s hc.1 (Nat.lt_succ_self _) hc.2]; decide
    · exact latestSide_ne_full votes choice lo s
        (fun t h1 h2 h3 => h t h1 (Nat.lt_succ_of_lt h2) h3)

end EthCLSpecs.Proofs.Heze.PayloadRace
