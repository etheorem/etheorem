import EthCLLib.Spec.State
import EthCLLib.Proofs.Run

/-!
# `EthCLLib.Proofs.IndexRead`: the indexed reads, box-free

What the pure read `EthCLLib.Spec.getAt` computes — at a `CLUint64` index, whose
`ToIndex` range test agrees with the collection's own on any collection whose
`IdxRead` instance misses past its size, at a `Nat` index, and over the two list
shapes the forks hold (`SSZList`, `ProgressiveList`, stated over the list's
array) — and how the machine read `EthCLLib.Spec.sszGetIdx` runs: a hit returns
the element and leaves the state alone, a miss raises the converted
`IndexError`.

No statement here names the uncached box: the lemmas quantify over the monadic
state `σ`, so both spec modes — boxed and plain — read them. The box-flavour
lemma about `sszGetIdx` (`keepsUncached_sszGetIdx`, in
`EthCLLib.Proofs.KeepsUncached`) is stated over these run equations, which is
why this module sits beside it.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec
open SizzLean.Cache

/-- `getAt` at a `CLUint64` index is the collection's `get?` at the index's value, with the
reject carrying that value and the collection's size, on any collection whose `get?` misses
past its size. The `ToIndex CLUint64` range test then agrees with the collection's own. -/
theorem getAt_clUint64_eq {α ρ : Type} [EthCLLib.Spec.IdxRead ρ α] (xs : ρ)
    (i : EthCLLib.Spec.CLUint64)
    (hlaw : ∀ k, EthCLLib.Spec.IdxRead.size xs ≤ k → EthCLLib.Spec.IdxRead.get? xs k = none) :
    (EthCLLib.Spec.getAt xs i : Except IndexError α) =
      (match EthCLLib.Spec.IdxRead.get? xs i.toPlainNat with
        | some a => .ok a
        | none => .error (IndexError.indexError i.toPlainNat
            (EthCLLib.Spec.IdxRead.size xs))) := by
  unfold EthCLLib.Spec.getAt
  simp only [EthCLLib.Spec.ToIndex.pos?, EthCLLib.Spec.ToIndex.idx?]
  by_cases h : i.toPlainNat < EthCLLib.Spec.IdxRead.size xs
  · simp only [h, ↓reduceIte]
    try rfl
  · simp only [h, ↓reduceIte, hlaw _ (Nat.le_of_not_lt h)]

/-- `getAt_clUint64_eq` on an SSZ list, stated over the list's array. -/
theorem getAt_sszList_clUint64 {α : Type} {cap : Nat} (xs : SizzLean.Repr.SSZList α cap)
    (i : EthCLLib.Spec.CLUint64) :
    (EthCLLib.Spec.getAt xs i : Except IndexError α) =
      (match xs.val[i.toPlainNat]? with
        | some a => .ok a
        | none => .error (IndexError.indexError i.toPlainNat xs.val.size)) :=
  getAt_clUint64_eq xs i (fun _ hk => Array.getElem?_eq_none_iff.mpr hk)

/-- `getAt_clUint64_eq` on a progressive list, stated over the list's array. -/
theorem getAt_progressiveList_clUint64 {α : Type} (xs : SizzLean.Repr.ProgressiveList α)
    (i : EthCLLib.Spec.CLUint64) :
    (EthCLLib.Spec.getAt xs i : Except IndexError α) =
      (match xs.val[i.toPlainNat]? with
        | some a => .ok a
        | none => .error (IndexError.indexError i.toPlainNat xs.val.size)) :=
  getAt_clUint64_eq xs i (fun _ hk => Array.getElem?_eq_none_iff.mpr hk)

/-- `getAt` at a `Nat` index is the collection's `get?` at that index, with the reject
carrying the index and the collection's size, on any collection whose `get?` misses past
its size. -/
theorem getAt_nat_eq {α ρ : Type} [EthCLLib.Spec.IdxRead ρ α] (xs : ρ) (i : Nat)
    (hlaw : ∀ k, EthCLLib.Spec.IdxRead.size xs ≤ k → EthCLLib.Spec.IdxRead.get? xs k = none) :
    (EthCLLib.Spec.getAt xs i : Except IndexError α) =
      (match EthCLLib.Spec.IdxRead.get? xs i with
        | some a => .ok a
        | none => .error (IndexError.indexError i (EthCLLib.Spec.IdxRead.size xs))) := by
  unfold EthCLLib.Spec.getAt
  simp only [EthCLLib.Spec.ToIndex.pos?, EthCLLib.Spec.ToIndex.idx?]
  by_cases h : i < EthCLLib.Spec.IdxRead.size xs
  · simp only [h, ↓reduceIte]
    try rfl
  · simp only [h, ↓reduceIte, hlaw _ (Nat.le_of_not_lt h)]

/-- `getAt_nat_eq` on a progressive list, stated over the list's array. -/
theorem getAt_progressiveList_nat {α : Type} (xs : SizzLean.Repr.ProgressiveList α) (i : Nat) :
    (EthCLLib.Spec.getAt xs i : Except IndexError α) =
      (match xs.val[i]? with
        | some a => .ok a
        | none => .error (IndexError.indexError i xs.val.size)) :=
  getAt_nat_eq xs i (fun _ hk => Array.getElem?_eq_none_iff.mpr hk)

/-- A hit of `sszGetIdx`: when the pure read `getAt` returns an element, the run returns
it and leaves the state unchanged. Any `ToIndex` kind. -/
theorem run_sszGetIdx_some {α ρ ι : Type} {σ ε : Type}
    [EthCLLib.Spec.IdxRead ρ α] [EthCLLib.Spec.ToIndex ι] [ErrorConv IndexError ε] {y : α}
    (xs : ρ) (i : ι) (sb : σ)
    (hq : EthCLLib.Spec.getAt xs i = .ok y) :
    (EthCLLib.Spec.sszGetIdx (E := ε) (m := StateT σ (Except ε)) xs i).run sb = .ok (y, sb) := by
  unfold EthCLLib.Spec.sszGetIdx EthCLLib.Spec.liftErr
  rw [hq]
  exact run_ofExcept_ok sb

/-- A miss of `sszGetIdx`: when the pure read `getAt` rejects, the run raises the
converted `IndexError`. -/
theorem run_sszGetIdx_none {α ρ ι : Type} {σ ε : Type}
    [EthCLLib.Spec.IdxRead ρ α] [EthCLLib.Spec.ToIndex ι] [ErrorConv IndexError ε]
    (xs : ρ) (i : ι) (sb : σ) (e : IndexError)
    (hq : (EthCLLib.Spec.getAt xs i : Except IndexError α) = .error e) :
    (EthCLLib.Spec.sszGetIdx (E := ε) (m := StateT σ (Except ε)) xs i).run sb
      = .error (ErrorConv.conv e) := by
  unfold EthCLLib.Spec.sszGetIdx EthCLLib.Spec.liftErr
  rw [hq]
  exact run_ofExcept_error sb
end EthCLLib.Proofs
