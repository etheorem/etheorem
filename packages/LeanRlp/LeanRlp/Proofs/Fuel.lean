import LeanRlp.Spec.Decode

/-!
# `LeanRlp.Proofs.Fuel`: the decoder's fuel and header theorems

The theorems about `Spec.Decode`. The layout of ARCHITECTURE.md §9
keeps them in their own module, so `Spec.Decode` holds definitions
only, and `Proofs/Axioms.lean` gates them with the rest
(ARCHITECTURE.md §5):

* a successful header names a payload fully inside the input
  (`decodeHeader_ok_bytes`, `decodeHeader_ok_list`);
* the header reader never fails with `outOfFuel`
  (`decodeHeader_not_outOfFuel`);
* every decoded item covers at least one input byte
  (`decodeItem_end_gt`);
* the fuel `Spec.fuelFor` certifies keeps `outOfFuel` out of both
  public entry points (`decode_fuelSufficient`, and the corollaries
  `decodePrefix_not_outOfFuel` and `decode_not_outOfFuel`).

Stage 3's item proofs stand on these.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

open LeanRlp.Spec

/-! ## What a header result guarantees -/

-- The header lemmas of this file share one proof script: unfold,
-- split on every canonical check, then a pinned-lemma leaf pass
-- (`injEq` for injection, `reduceCtorEq` for the impossible
-- branches). If a toolchain bump changes these lemmas' statements,
-- revisit all three.

/-- A successful string header names a payload that starts after the
header byte and ends inside the input. -/
theorem decodeHeader_ok_bytes (input : ByteArray) (offset : Nat)
    (start len : Nat)
    (hok : decodeHeader input offset = Except.ok (Header.bytes start len)) :
    offset + 1 ≤ start ∧ start + len ≤ input.size := by
  unfold decodeHeader decodeLongHeader at hok
  repeat' split at hok
  all_goals
    first
      | (simp only [Except.ok.injEq, Header.bytes.injEq] at hok;
         obtain ⟨rfl, rfl⟩ := hok; omega)
      | simp only [Except.ok.injEq, reduceCtorEq] at hok

/-- A successful list header names a payload that starts after the
header byte and ends inside the input. -/
theorem decodeHeader_ok_list (input : ByteArray) (offset : Nat)
    (start len : Nat)
    (hok : decodeHeader input offset = Except.ok (Header.list start len)) :
    offset + 1 ≤ start ∧ start + len ≤ input.size := by
  unfold decodeHeader decodeLongHeader at hok
  repeat' split at hok
  all_goals
    first
      | (simp only [Except.ok.injEq, Header.list.injEq] at hok;
         obtain ⟨rfl, rfl⟩ := hok; omega)
      | simp only [Except.ok.injEq, reduceCtorEq] at hok

/-- The header reader never fails with `outOfFuel`: every branch
returns its own reason or a result. -/
theorem decodeHeader_not_outOfFuel (input : ByteArray) (offset : Nat)
    (e : DecodeError)
    (he : decodeHeader input offset = Except.error e) :
    ∀ off, e ≠ DecodeError.outOfFuel off := by
  unfold decodeHeader decodeLongHeader at he
  repeat' split at he
  all_goals
    first
      | (simp only [Except.error.injEq] at he; subst he; simp)
      | simp only [reduceCtorEq] at he

/-- A decoded item covers at least one input byte: the element loop
advances, so the fuel accounting terminates. -/
theorem decodeItem_end_gt (input : ByteArray) (offset fuel depth : Nat) (t : Item)
    (stop : Nat)
    (hok : decodeItem input offset fuel depth = Except.ok (t, stop)) :
    offset < stop := by
  unfold decodeItem at hok
  split at hok
  · simp only [reduceCtorEq] at hok
  · cases hv : decodeHeader input offset with
    | error e =>
      simp only [hv, reduceCtorEq] at hok
    | ok h =>
      cases h with
      | byte v =>
        simp only [hv, Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        omega
      | bytes start len =>
        simp only [hv, Except.ok.injEq, Prod.mk.injEq] at hok
        have hb := decodeHeader_ok_bytes input offset start len hv
        obtain ⟨-, rfl⟩ := hok
        omega
      | list start len =>
        simp only [hv] at hok
        have hb := decodeHeader_ok_list input offset start len hv
        split at hok
        · simp only [reduceCtorEq] at hok
        · split at hok
          · simp only [reduceCtorEq] at hok
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨-, rfl⟩ := hok
            omega

/-! ## Fuel sufficiency -/

/-- Fuel sufficiency (ARCHITECTURE.md §2.1): with the fuel
`fuelFor` certifies, the decoder never fails with `outOfFuel`. Each
item node and each list element spends one unit, and every decoded
item covers at least one input byte, so two units per byte suffice.
The element loop carries one more unit of slack, because it hands
the element's own node its fuel after spending the element slot. The
statement carries both functions of the decoder family, because the
recursion is mutual. -/
theorem decode_fuelSufficient (input : ByteArray) :
    ∀ fuel,
      (∀ offset depth, fuelFor input offset ≤ fuel → ∀ off,
        decodeItem input offset fuel depth ≠ Except.error (.outOfFuel off)) ∧
      (∀ cursor stop depth acc, stop ≤ input.size →
        2 * (input.size - cursor) + 3 ≤ fuel → ∀ off,
        decodeListElemsAux input cursor stop fuel depth acc ≠
          Except.error (.outOfFuel off)) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro offset depth h _
      exact absurd h (by simp only [fuelFor]; omega)
    · intro cursor stop _ _ _ h _
      exact absurd h (by omega)
  | succ fuel ih =>
    constructor
    · intro offset depth h off
      have hf : 2 * (input.size - offset) + 1 ≤ fuel := by
        simp only [fuelFor] at h; omega
      simp only [decodeItem]
      split
      · next e he =>
        intro hcon
        exact decodeHeader_not_outOfFuel input offset e he off
          (Except.error.inj hcon)
      · next _ _ => simp
      · next _ _ => simp
      · next start len hv =>
        have hb := decodeHeader_ok_list input offset start len hv
        split
        · simp
        · have hno :=
            ih.2 start (start + len) (depth - 1) [] (by omega)
              (by omega) off
          split
          · next e he =>
            intro hcon
            apply hno
            rw [← Except.error.inj hcon]
            exact he
          · next _ _ => simp
    · intro cursor stop depth acc hstop h off
      have hf : 2 * (input.size - cursor) + 2 ≤ fuel := by omega
      have hitem := ih.1 cursor depth hf off
      cases hdec : decodeItem input cursor fuel depth with
      | error e =>
        simp only [decodeListElemsAux, hdec]
        split
        · simp
        · intro hcon
          apply hitem
          rw [← Except.error.inj hcon]
          exact hdec
      | ok p =>
        obtain ⟨t, next⟩ := p
        have hgt : cursor < next :=
          decodeItem_end_gt input cursor fuel depth t next hdec
        simp only [decodeListElemsAux, hdec]
        split
        · simp
        · split
          · simp
          · exact ih.2 next stop depth (t :: acc) hstop (by omega) off

/-- `outOfFuel` is a dead branch for `decodePrefix`
(ARCHITECTURE.md §2.1): it passes the certified fuel. -/
theorem decodePrefix_not_outOfFuel (input : ByteArray) (offset maxDepth : Nat) :
    ∀ off, decodePrefix input offset maxDepth ≠ Except.error (.outOfFuel off) := by
  have h := decode_fuelSufficient input (fuelFor input offset)
  unfold decodePrefix
  intro off
  exact h.1 offset maxDepth (Nat.le_refl _) off

/-- `outOfFuel` is a dead branch for `decode` (ARCHITECTURE.md
§2.1): it passes the certified fuel. -/
theorem decode_not_outOfFuel (input : ByteArray) (maxDepth : Nat) :
    ∀ off, decode input maxDepth ≠ Except.error (.outOfFuel off) := by
  have h := decode_fuelSufficient input (fuelFor input 0)
  unfold decode
  intro off
  split
  · next e he =>
    intro hcon
    apply h.1 0 maxDepth (Nat.le_refl _) off
    rw [← Except.error.inj hcon]
    exact he
  · next _ _ => split <;> simp

end LeanRlp.Proofs
