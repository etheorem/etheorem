import EthCLSpecs.Fulu.Balances
import EthCLLib.Proofs.CLUint
import EthCLLib.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Fulu.TotalBalance`: the `get_total_balance` contract

`get_total_balance` (`phase0/beacon-chain.md:1563`) sums the effective balances of the given
indices and floors the sum at one `EFFECTIVE_BALANCE_INCREMENT`. Like `compute_time_at_slot`,
the function accepts the raise in its own text: the sum is "safe up to ~10B ETH, after which
this overflows" (`phase0/beacon-chain.md:1563`). The body models that with the checked `+` on
`Gwei` (`CLUint64`), so `getTotalBalance` returns a `Checked Gwei` and rejects with the
`.arithmetic` fault exactly where the pyspec would raise.

`getTotalBalance` is a plain `forkdef` over `Checked Gwei`, no `StateTransition` wrapper, so
its contract states the `Checked` value directly at `pureState state`, the same pure box the
sibling mutator proofs read through. The read of `validators` is the body's own total `[i]!`
read, so an out-of-range index contributes the default validator's balance and the contract
carries no side condition on `indices`.

The fold-vs-total equivalence is the one fact the checked fold needs: a sum of naturals fits
in `2 ^ 64` exactly when every partial sum does, because each summand is nonnegative. The
helper lemmas are generic over `CLUint64`, so `EthCLLib/Proofs/CLUint.lean` is their canonical
home; they stay private here until that move, which is a tracked follow-up (the task's scope
held edits to this file and the coverage refresh).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec (Checked CLUint64 HasherTag)
open EthCLLib.Proofs (pureState add_eq_ok toPlainInt_ofNat_val toPlainInt_inj)
open EthCLSpecs.Fulu (Preset BeaconState ValidatorIndex Gwei getTotalBalance)

/-- The `max` the floor reads back through `toPlainInt`: the `Ord`-instance max is an
`if`-then-else on the native `UInt64` order, so each branch's plain value is the plain `max`. -/
private theorem gweiMax_toPlainInt (a b : Gwei) :
    (max a b : Gwei).toPlainInt = max a.toPlainInt b.toPlainInt := by
  have hdef : (max a b : Gwei) = if a < b then b else a := rfl
  rw [hdef]
  split
  · rename_i h
    have h' : a.val < b.val := h
    rw [UInt64.lt_iff_toNat_lt] at h'
    show b.val.toNat = max a.val.toNat b.val.toNat
    rw [Nat.max_eq_right (Nat.le_of_lt h')]
  · rename_i h
    have h' : ¬ a.val < b.val := h
    rw [UInt64.lt_iff_toNat_lt] at h'
    show a.val.toNat = max a.val.toNat b.val.toNat
    rw [Nat.max_eq_left (Nat.le_of_not_lt h')]

private theorem gweiZero_toPlainInt : (0 : Gwei).toPlainInt = 0 := rfl

/-- A fold that only adds never drops below its start: each step adds a plain value, so the
running total only grows. This is the per-step-fits-iff-total-fits direction the reverse
fold proof needs. -/
private theorem foldl_ge_init {α : Type} (xs : List α) (f : α → Gwei) (init : Nat) :
    init ≤ List.foldl (fun s x => s + (f x).toPlainInt) init xs := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h1 := ih (init + (f x).toPlainInt)
    omega

/-- The checked-add fold over a list, at a general start: it returns `.ok r` exactly when the
plain sum from `acc` fits in `2 ^ 64`, and then `r` reads back as that sum. Every step's
plain summand is nonnegative, so the fold's per-step fit tests hold together exactly when the
total fits; `foldl_ge_init` extracts each step's fit from the total's. -/
private theorem foldlM_checkedAdd_gen {α : Type} :
    ∀ (xs : List α) (f : α → Gwei) (acc r : Gwei),
      (xs.foldlM (fun a x => (a + f x : Checked Gwei)) acc) = .ok r ↔
        List.foldl (fun s x => s + (f x).toPlainInt) acc.toPlainInt xs < 2 ^ 64 ∧
          r.toPlainInt = List.foldl (fun s x => s + (f x).toPlainInt) acc.toPlainInt xs := by
  intro xs
  induction xs with
  | nil =>
    intro f acc r
    simp only [List.foldlM_nil, List.foldl_nil]
    constructor
    · intro h
      have h' : Except.ok acc = Except.ok r := h
      injection h' with h'
      subst h'
      exact ⟨UInt64.toNat_lt acc.val, rfl⟩
    · intro h
      have : acc = r := toPlainInt_inj h.2.symm
      subst this
      rfl
  | cons x xs ih =>
    intro f acc r
    rw [List.foldlM_cons]
    constructor
    · intro h
      cases hax : (acc + f x : Checked Gwei) with
      | error e =>
        rw [hax] at h
        have h' : Except.error e = Except.ok r := h
        simp at h'
      | ok s =>
        rw [hax] at h
        have h' : xs.foldlM (fun a x => (a + f x : Checked Gwei)) s = .ok r := h
        obtain ⟨hfit, hval⟩ := (add_eq_ok acc (f x) s).mp hax
        obtain ⟨hfit2, hval2⟩ := (ih f s r).mp h'
        rw [List.foldl_cons]
        refine ⟨?_, ?_⟩
        · rw [← hval]; exact hfit2
        · rw [← hval]; exact hval2
    · rintro ⟨hfit, hval⟩
      rw [List.foldl_cons] at hfit hval
      have hfitp : acc.toPlainInt + (f x).toPlainInt < 2 ^ 64 := by
        have hge := foldl_ge_init xs f (acc.toPlainInt + (f x).toPlainInt)
        omega
      have hfitstep : acc.val.toNat + (f x).val.toNat < 2 ^ 64 := hfitp
      have hax : (acc + f x : Checked Gwei)
          = .ok (CLUint64.trustedOfUInt64 (acc.val + (f x).val)) :=
        (add_eq_ok acc (f x) _).mpr ⟨hfitp, by
          show (acc.val + (f x).val).toNat = acc.toPlainInt + (f x).toPlainInt
          rw [UInt64.toNat_add, Nat.mod_eq_of_lt hfitstep]
          rfl⟩
      have hwit : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (acc.val + (f x).val))
          = acc.toPlainInt + (f x).toPlainInt := by
        show (acc.val + (f x).val).toNat = acc.toPlainInt + (f x).toPlainInt
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt hfitstep]
        rfl
      simp only [hax]
      rw [← hwit] at hfit hval
      exact (ih f _ r).mpr ⟨hfit, hval⟩

/-- The zero-start form the body folds with. -/
private theorem foldlM_checkedAdd_ok {α : Type} (xs : List α) (f : α → Gwei) (r : Gwei) :
    (xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei)) = .ok r ↔
      List.foldl (fun s x => s + (f x).toPlainInt) 0 xs < 2 ^ 64 ∧
        r.toPlainInt = List.foldl (fun s x => s + (f x).toPlainInt) 0 xs := by
  have h := foldlM_checkedAdd_gen xs f (0 : Gwei) r
  simpa [gweiZero_toPlainInt] using h

/-- The whole `get_total_balance` shape over a list: the checked-add fold from zero, then the
floor at `floor`. It succeeds exactly when the plain sum fits, and then the result reads back
as the sum floored at `floor`. The bind peel names the fold's intermediate sum once, so both
directions state their facts over one `s`. -/
private theorem foldFloor_ok {α : Type} :
    ∀ (xs : List α) (f : α → Gwei) (floor c : Gwei),
      ((xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei)).bind
          fun total => .ok (max total floor)) = .ok c ↔
        xs.foldl (fun s x => s + (f x).toPlainInt) 0 < 2 ^ 64 ∧
          c.toPlainInt = max (xs.foldl (fun s x => s + (f x).toPlainInt) 0) floor.toPlainInt := by
  intro xs f floor c
  have hfoldiff : ∀ r : Gwei,
      (xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei)) = .ok r ↔
        xs.foldl (fun s x => s + (f x).toPlainInt) 0 < 2 ^ 64 ∧
          r.toPlainInt = xs.foldl (fun s x => s + (f x).toPlainInt) 0 :=
    fun r => foldlM_checkedAdd_ok xs f r
  have hpeel : ((xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei)).bind
        fun total => .ok (max total floor)) = .ok c
      ↔ ∃ s : Gwei, xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei) = .ok s ∧
          (Except.ok (max s floor) : Checked Gwei) = Except.ok c := by
    cases h : xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei) with
    | error e =>
      constructor
      · intro hh
        have h' : Except.error e = Except.ok c := hh
        simp at h'
      · rintro ⟨s, hs, -⟩
        have h' : Except.error e = Except.ok s := hs
        simp at h'
    | ok s =>
      constructor
      · intro hh
        exact ⟨s, rfl, hh⟩
      · rintro ⟨s', hs', hk⟩
        injection hs' with hss'
        rw [hss']
        exact hk
  rw [hpeel]
  constructor
  · rintro ⟨s, hfold, hk⟩
    obtain ⟨hfitS, hvalS⟩ := (hfoldiff s).mp hfold
    have hk' : Except.ok (max s floor) = (Except.ok c : Checked Gwei) := hk
    simp only [Except.ok.injEq] at hk'
    exact ⟨hfitS, by rw [← hk', gweiMax_toPlainInt, hvalS]⟩
  · rintro ⟨hfit, hval⟩
    refine ⟨CLUint64.trustedOfUInt64
        (UInt64.ofNat (xs.foldl (fun s x => s + (f x).toPlainInt) 0)), ?_, ?_⟩
    · exact (hfoldiff _).mpr ⟨hfit, toPlainInt_ofNat_val _ hfit⟩
    · have heq : max (CLUint64.trustedOfUInt64
            (UInt64.ofNat (xs.foldl (fun s x => s + (f x).toPlainInt) 0))) floor = c :=
        toPlainInt_inj (by rw [gweiMax_toPlainInt, toPlainInt_ofNat_val _ hfit]; exact hval.symm)
      rw [heq]

/-- The array form the body folds over. -/
private theorem foldFloor_ok_array {α : Type} (xs : Array α) (f : α → Gwei) (floor c : Gwei) :
    ((xs.foldlM (fun a x => (a + f x : Checked Gwei)) (0 : Gwei)).bind
        fun total => .ok (max total floor)) = .ok c ↔
      xs.foldl (fun s x => s + (f x).toPlainInt) 0 < 2 ^ 64 ∧
        c.toPlainInt = max (xs.foldl (fun s x => s + (f x).toPlainInt) 0) floor.toPlainInt := by
  rw [← Array.foldlM_toList, ← Array.foldl_toList]
  exact foldFloor_ok xs.toList f floor c

/-- **The `get_total_balance` contract.** `getTotalBalance (pureState state) indices` returns
`.ok c` exactly when the plain sum of the effective balances fits in `2 ^ 64`, the point the
pyspec's own text calls out ("safe up to ~10B ETH, after which this overflows",
`phase0/beacon-chain.md:1563`); past it the checked `+` rejects a step with the `.arithmetic`
fault where the pyspec raises. On success `c.toPlainInt` reads back as the plain sum floored
at one `EFFECTIVE_BALANCE_INCREMENT`, the pyspec's `max(total, EFFECTIVE_BALANCE_INCREMENT)`.
The floor is a `Gwei` preset value, so the statement spells `EFFECTIVE_BALANCE_INCREMENT` as
`Const.effectiveBalanceIncrementG.toPlainInt` (`10 ^ 9` at both shipped presets). The index
reads are the body's own total `[i]!` reads, so an out-of-range index contributes the default
validator's balance and no side condition on `indices` appears. -/
@[characterizes EthCLSpecs.Fulu.getTotalBalance]
theorem getTotalBalance_eq [Preset] [HasherTag] :
    ∀ (state : BeaconState) (indices : Array ValidatorIndex) (c : Gwei),
      getTotalBalance (pureState state) indices = .ok c ↔
        indices.foldl (fun acc i => acc + state.validators[i.toPlainInt]!.effectiveBalance.toPlainInt) 0
              < 2 ^ 64 ∧
          c.toPlainInt =
            max (indices.foldl (fun acc i => acc + state.validators[i.toPlainInt]!.effectiveBalance.toPlainInt) 0)
              EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG.toPlainInt :=
  fun state indices c => foldFloor_ok_array indices
    (fun i => state.validators[i.toPlainInt]!.effectiveBalance)
    EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG c

end EthCLSpecs.Proofs.Fulu
