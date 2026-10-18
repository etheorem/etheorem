import EthCLLib.Proofs.FFG.Stake

/-!
# `EthCLLib.Proofs.FFG.Safety`: accountable safety with stake drift

Chain 1 finalizes a checkpoint `b`. Chain 2 justifies a checkpoint `t` at the epoch of `b` or
later, and `b` is not on chain 2. Then a set of validators cast slashable votes, and their
reference stake is at least one third of the reference total, less `5/3` of the two drifts
(`ffg_accountable_safety`). With no drift, this is the accountable safety theorem of Casper
FFG (Buterin and Griffith 2017, theorem 1).

## The proof

`link_pair_slashable` takes a link of each chain whose votes meet a slashing condition.
Both links carry two thirds of the reference total, less `5/3` of the drift of their chain. So
the voters of both links carry one third, less `5/3` of the two drifts (`overlap_bound`).

`Justified.first_past` finds the first link of chain 2 past the epoch of `b`. Its source is at
or before the epoch of `b`. The case split compares that link with the links that finalized
`b` on chain 1:

- `t` at the epoch of `b`: the links to `b` and to `t` are double votes.
- The source of the first link at the epoch of `b`: the links to `b` and to that source are
  double votes.
- The source before the epoch of `b`: the first link is a double vote with a link of the
  finalization of `b` at the same target epoch. Otherwise, it surrounds the link from `b`.

Two targets at one epoch differ, because `b` is not on chain 2 and the chains agree below a
common checkpoint (`ne_of_agree`).
-/

set_option autoImplicit false

namespace EthCLLib.Proofs.FFG

variable {V R : Type} [DecidableEq V] [DecidableEq R]

/-- A link of chain 1 and a link of chain 2, both weighed between `L` and `E`, whose votes meet
a slashing condition. The voters of both links are slashable. Their reference stake is at
least one third of the reference total, less `5/3` of the two drifts. -/
theorem link_pair_slashable {stake₀ : V → Nat} {total₀ L E d₁ d₂ : Nat} {c₁ c₂ : Chain V R}
    (hvals : c₁.vals = c₂.vals)
    (hc₁ : StakeClose stake₀ total₀ c₁ L E d₁) (hc₂ : StakeClose stake₀ total₀ c₂ L E d₂)
    {s₁ t₁ s₂ t₂ : Checkpoint R} (hl₁ : Link c₁ s₁ t₁) (hl₂ : Link c₂ s₂ t₂)
    (hL₁ : L ≤ t₁.epoch) (hE₁ : t₁.epoch + 1 ≤ E) (hL₂ : L ≤ t₂.epoch) (hE₂ : t₂.epoch + 1 ≤ E)
    (hrel : (t₁.epoch = t₂.epoch ∧ t₁ ≠ t₂) ∨ (s₁.epoch < s₂.epoch ∧ t₂.epoch < t₁.epoch) ∨
      (s₂.epoch < s₁.epoch ∧ t₁.epoch < t₂.epoch)) :
    ∃ X : List V, X.Nodup ∧ (∀ v ∈ X, Slashable c₁.votes c₂.votes v) ∧
      3 * stakeSum stake₀ X + 5 * (d₁ + d₂) ≥ total₀ := by
  refine ⟨c₁.vals.filter (fun v => voted c₁ s₁ t₁ v && voted c₂ s₂ t₂ v),
    hc₁.1.filter _, ?_, ?_⟩
  · -- Each voter of both links has a vote in each link.
    intro v hv
    rw [List.mem_filter, Bool.and_eq_true] at hv
    obtain ⟨-, h₁, h₂⟩ := hv
    obtain ⟨x, hx, hx'⟩ := List.any_eq_true.mp h₁
    obtain ⟨y, hy, hy'⟩ := List.any_eq_true.mp h₂
    simp only [decide_eq_true_eq] at hx' hy'
    obtain ⟨hxv, hxs, hxt⟩ := hx'
    obtain ⟨hyv, hys, hyt⟩ := hy'
    have hxy : x.val = y.val := hxv.trans hyv.symm
    refine ⟨x, hx, y, hy, hxv, hyv, ?_⟩
    rcases hrel with ⟨he, hne⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨hxy, by rw [hxt, hyt]; exact he, by rw [hxt, hyt]; exact hne⟩
    · exact .inr (.inl ⟨hxy, by rw [hxs, hys]; exact h1, by rw [hxt, hyt]; exact h2⟩)
    · exact .inr (.inr ⟨hxy.symm, by rw [hys, hxs]; exact h1, by rw [hyt, hxt]; exact h2⟩)
  · -- The two link bounds, the union below the total, and the overlap arithmetic.
    have hA := link_bound_of_close hl₁ hc₁ hL₁ hE₁
    have hB := link_bound_of_close hl₂ hc₂ hL₂ hE₂
    unfold linkVoters at hA hB
    rw [← hvals] at hB
    have hie := stakeSum_filter_or_add_and stake₀ (voted c₁ s₁ t₁) (voted c₂ s₂ t₂) c₁.vals
    have hu := stakeSum_filter_le stake₀ (fun v => voted c₁ s₁ t₁ v || voted c₂ s₂ t₂ v) c₁.vals
    exact overlap_bound _ _ _ _ _ d₁ d₂ hA hB (Nat.le_trans hu hc₁.2.1) hie

/-- The first link past the epoch `k` on the way to `t`. Every start checkpoint is at or before
`k`, and `t` is after `k`. Then a link from a justified `s` at or before `k` reaches a `t'`
after `k`, at or before `t`. -/
theorem Justified.first_past {c : Chain V R} {k : Nat} (hbase : ∀ x ∈ c.base, x.epoch ≤ k)
    {t : Checkpoint R} (ht : Justified c t) (hk : k < t.epoch) :
    ∃ s t', Justified c s ∧ Link c s t' ∧ s.epoch ≤ k ∧ k < t'.epoch ∧ t'.epoch ≤ t.epoch := by
  induction ht with
  | base hb => exact absurd (hbase _ hb) (by omega)
  | @link s t hs hl ih =>
    by_cases hsk : s.epoch ≤ k
    · exact ⟨s, t, hs, hl, hsk, hk, Nat.le_refl _⟩
    · obtain ⟨s', t', h1, h2, h3, h4, h5⟩ := ih (by omega)
      exact ⟨s', t', h1, h2, h3, h4, by have := hl.1; omega⟩

/-- Accountable safety with stake drift. Chain 1 finalizes `b`. Chain 2 justifies `t` at the
epoch of `b` or later, and `b` is not on chain 2. The chains share their start checkpoints
and agree below a common checkpoint. The stake of each chain stays close to the reference from
the epoch `L` to the epoch `E`.

Then a list `X` of validators, with no duplicate, cast slashable votes: each validator of `X`
has a vote on each chain, and the two votes meet a slashing condition. Their reference stake is
at least one third of the reference total, less `5/3` of the two drifts. -/
theorem ffg_accountable_safety (stake₀ : V → Nat) (total₀ L E d₁ d₂ : Nat) (c₁ c₂ : Chain V R)
    (hvals : c₁.vals = c₂.vals) {b t : Checkpoint R}
    (hb : Finalized c₁ b) (ht : Justified c₂ t) (hep : b.epoch ≤ t.epoch)
    (hconf : ¬ c₂.OnChain b)
    (hshared : CommonBase c₁ c₂ b) (hagree : Agree c₁ c₂)
    (hc₁ : StakeClose stake₀ total₀ c₁ L E d₁) (hc₂ : StakeClose stake₀ total₀ c₂ L E d₂)
    (hL : L ≤ b.epoch) (hE : t.epoch + 1 ≤ E ∧ b.epoch + 3 ≤ E) :
    ∃ X : List V, X.Nodup ∧ (∀ v ∈ X, Slashable c₁.votes c₂.votes v) ∧
      3 * stakeSum stake₀ X + 5 * (d₁ + d₂) ≥ total₀ := by
  obtain ⟨hE₁, hE₂⟩ := hE
  -- The start checkpoints: on both chains, before the epoch of `b`.
  have hbase₁ : ∀ x ∈ c₁.base, c₁.OnChain x := fun x hx => (hshared.2 x hx).2.1
  have hlt₁ : ∀ x ∈ c₁.base, x.epoch < b.epoch := fun x hx => (hshared.2 x hx).1
  have hmem : ∀ x ∈ c₂.base, x ∈ c₁.base := fun x hx => by rw [hshared.1]; exact hx
  have hlt₂ : ∀ x ∈ c₂.base, x.epoch < b.epoch := fun x hx => hlt₁ x (hmem x hx)
  -- `b` is justified on chain 1 by a link, since it is after every start checkpoint.
  have hbJ : Justified c₁ b := match hb with
    | .one h _ _ _ => h
    | .two h _ _ _ _ _ => h
  have hb₁ : c₁.OnChain b := hbJ.onChain hbase₁
  obtain ⟨s₁, -, hl₁⟩ := hbJ.link_of_not_base fun h => absurd (hlt₁ b h) (Nat.lt_irrefl _)
  have pair := @link_pair_slashable V R _ _ stake₀ total₀ L E d₁ d₂ c₁ c₂ hvals hc₁ hc₂
  rcases Nat.eq_or_lt_of_le hep with heq | hgt
  · -- `t` at the epoch of `b`: double votes on `b` and `t`.
    obtain ⟨s₂, -, hl₂⟩ := ht.link_of_not_base fun h => by have := hlt₂ t h; omega
    have hne : b ≠ t := fun h => hconf (h ▸ hl₂.2.2.1)
    exact pair hl₁ hl₂ hL (by omega) (by omega) (by omega) (.inl ⟨heq, hne⟩)
  · -- The first link `s → t'` of chain 2 past the epoch of `b`.
    obtain ⟨s, t', hsJ, hl, hsb, hbt', ht't⟩ :=
      ht.first_past (fun x hx => Nat.le_of_lt (hlt₂ x hx)) hgt
    have ht'₂ : c₂.OnChain t' := hl.2.2.1
    rcases Nat.eq_or_lt_of_le hsb with hseq | hslt
    · -- `s` at the epoch of `b`: double votes on `b` and `s`.
      obtain ⟨s₃, -, hl₃⟩ := hsJ.link_of_not_base fun h => by have := hlt₂ s h; omega
      have hne : b ≠ s := fun h => hconf (h ▸ hl.2.1)
      exact pair hl₁ hl₃ hL (by omega) (by omega) (by omega) (.inl ⟨hseq.symm, hne⟩)
    · -- `s` before the epoch of `b`: compare with the finalizing link from `b`.
      cases hb with
      | @one b₁ _ _ hb1e hlb =>
        rcases Nat.eq_or_lt_of_le (show b.epoch + 1 ≤ t'.epoch by omega) with h1 | h1
        · have hne : b₁ ≠ t' := ne_of_agree hagree hb₁ hconf hlb.2.2.1 ht'₂ (by omega)
          exact pair hlb hl (by omega) (by omega) (by omega) (by omega)
            (.inl ⟨by omega, hne⟩)
        · exact pair hlb hl (by omega) (by omega) (by omega) (by omega)
            (.inr (.inr ⟨hslt, by omega⟩))
      | @two m t₂ _ hmJ _ hme ht2e hlb =>
        rcases Nat.eq_or_lt_of_le (show b.epoch + 1 ≤ t'.epoch by omega) with h1 | h1
        · -- `t'` at the epoch of `m`: double votes on `m` and `t'`.
          obtain ⟨sm, -, hlm⟩ := hmJ.link_of_not_base fun h => by have := hlt₁ m h; omega
          have hne : m ≠ t' := ne_of_agree hagree hb₁ hconf hlm.2.2.1 ht'₂ (by omega)
          exact pair hlm hl (by omega) (by omega) (by omega) (by omega)
            (.inl ⟨by omega, hne⟩)
        · rcases Nat.eq_or_lt_of_le (show b.epoch + 2 ≤ t'.epoch by omega) with h2 | h2
          · -- `t'` at the epoch of `t₂`: double votes on `t₂` and `t'`.
            have hne : t₂ ≠ t' := ne_of_agree hagree hb₁ hconf hlb.2.2.1 ht'₂ (by omega)
            exact pair hlb hl (by omega) (by omega) (by omega) (by omega)
              (.inl ⟨by omega, hne⟩)
          · -- `s → t'` surrounds `b → t₂`.
            exact pair hlb hl (by omega) (by omega) (by omega) (by omega)
              (.inr (.inr ⟨hslt, by omega⟩))

end EthCLLib.Proofs.FFG
