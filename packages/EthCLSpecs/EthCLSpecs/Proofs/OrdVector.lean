import EthCLLib.Spec.FiniteMap

/-!
# `EthCLSpecs.Proofs.OrdVector`: the byte-vector order is reflexive

`instOrdVectorUInt8` (`EthCLLib/Spec/FiniteMap.lean`) orders `Root` and every other
`Vector UInt8 n` in lexicographic order. Its byte loop returns at the first byte that
differs. Fork choice compares node roots with this order in the `betterOf` step of
`getHead`. A block's EMPTY node and FULL node have the same root. The comparison
reaches the payload tiebreaker only if `compare r r = .eq`. This module proves that
fact.

The module is about a framework instance, but it lives in the fork-proof tree. The
fork bodies do not import this tree. So a change here rebuilds only the proof modules,
not every fork body.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec

/-- The byte-vector order is reflexive. No byte is less than itself or greater than
itself. So the loop runs to its end and returns `.eq`. -/
theorem compare_vectorUInt8_self {n : Nat} (a : Vector UInt8 n) :
    compare a a = Ordering.eq := by
  show (instOrdVectorUInt8 (n := n)).compare a a = Ordering.eq
  unfold instOrdVectorUInt8
  -- The early `return` threads an `MProd (Option Ordering) PUnit` state through the loop.
  -- Both byte guards compare a byte with itself, so each step yields the start state.
  have hloop : ∀ l : List Nat,
      (forIn l (⟨none, PUnit.unit⟩ : MProd (Option Ordering) PUnit)
        fun _ _ => (pure (ForInStep.yield ⟨none, PUnit.unit⟩) : Id _))
        = pure ⟨none, PUnit.unit⟩ := by
    intro l
    induction l with
    | nil => rfl
    | cons i rest ih => simpa [List.forIn_cons] using ih
  have hirrefl : ∀ x : UInt8, (x < x) = False := fun x => eq_false (UInt8.lt_irrefl x)
  simp only [hirrefl, if_false, bind_pure_comp, map_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', hloop]
  rfl

end EthCLSpecs.Proofs
