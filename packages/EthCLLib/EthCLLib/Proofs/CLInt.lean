import EthCLLib.Proofs.CLUint

/-!
# `EthCLLib.Proofs.CLInt`: the plain-kind laws

Success conditions and value laws for the plain `int` primitives
(`SPEC_ARITHMETIC.md` §4.9). `+`, `-`, and `*` on `CLInt` never raise, so
their laws are pure value equations. `/` and `%` raise on the zero divisor
only, and floor as Python does through `Int.fdiv` / `Int.fmod` (§5.2). The
checked narrowing `toCLUint64?` carries the one range test into `CLUint64`
and shares its laws with `CLUint64.ofInt?`, the canonical home of the
`Uint64(n)` test.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-! ## Total operators: value laws only -/

/-- Plain addition computes the underlying sum. -/
theorem int_add_value (a b : CLInt) :
    (a + b).toPlainInt = a.toPlainInt + b.toPlainInt := rfl

/-- Plain subtraction computes the underlying difference. -/
theorem int_sub_value (a b : CLInt) :
    (a - b).toPlainInt = a.toPlainInt - b.toPlainInt := rfl

/-- Plain multiplication computes the underlying product. -/
theorem int_mul_value (a b : CLInt) :
    (a * b).toPlainInt = a.toPlainInt * b.toPlainInt := rfl

/-! ## Floor division and modulo -/

/-- `//` succeeds exactly off the zero divisor, and floors as Python does. -/
theorem fdiv_eq_ok (a b c : CLInt) :
    CLInt.fdiv a b = .ok c ↔
      b.val ≠ 0 ∧ c.toPlainInt = Int.fdiv a.val b.val := by
  rw [CLInt.fdiv]
  split
  · rename_i hz
    have hb0 : b.val = 0 := hz
    refine ⟨fun hc => ?_, fun hn => absurd hn.1 (fun hne => hne hb0)⟩
    simp at hc
  · rename_i hz
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · refine ⟨fun h0 => hz h0, ?_⟩
      rw [← Except.ok.inj hc]
      rfl
    · obtain ⟨h0, hv⟩ := hn
      exact congrArg Except.ok (congrArg CLInt.mk hv.symm)

/-- `//` succeeds exactly off the zero divisor. -/
theorem fdiv_ok_iff (a b : CLInt) :
    (∃ c, CLInt.fdiv a b = .ok c) ↔ b.val ≠ 0 := by
  constructor
  · rintro ⟨c, hc⟩
    exact (fdiv_eq_ok a b c).mp hc |>.1
  · intro hn
    exact ⟨_, fdiv_eq_ok a b _ |>.mpr ⟨hn, rfl⟩⟩

/-- The value of a successful `//`. -/
theorem fdiv_value (a b c : CLInt) (h : CLInt.fdiv a b = .ok c) :
    c.toPlainInt = Int.fdiv a.val b.val :=
  (fdiv_eq_ok a b c).mp h |>.2

/-- `%` succeeds exactly off the zero divisor, with the sign of the divisor. -/
theorem fmod_eq_ok (a b c : CLInt) :
    CLInt.fmod a b = .ok c ↔
      b.val ≠ 0 ∧ c.toPlainInt = Int.fmod a.val b.val := by
  rw [CLInt.fmod]
  split
  · rename_i hz
    have hb0 : b.val = 0 := hz
    refine ⟨fun hc => ?_, fun hn => absurd hn.1 (fun hne => hne hb0)⟩
    simp at hc
  · rename_i hz
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · refine ⟨fun h0 => hz h0, ?_⟩
      rw [← Except.ok.inj hc]
      rfl
    · obtain ⟨h0, hv⟩ := hn
      exact congrArg Except.ok (congrArg CLInt.mk hv.symm)

/-- `%` succeeds exactly off the zero divisor. -/
theorem fmod_ok_iff (a b : CLInt) :
    (∃ c, CLInt.fmod a b = .ok c) ↔ b.val ≠ 0 := by
  constructor
  · rintro ⟨c, hc⟩
    exact (fmod_eq_ok a b c).mp hc |>.1
  · intro hn
    exact ⟨_, fmod_eq_ok a b _ |>.mpr ⟨hn, rfl⟩⟩

/-- The value of a successful `%`. -/
theorem fmod_value (a b c : CLInt) (h : CLInt.fmod a b = .ok c) :
    c.toPlainInt = Int.fmod a.val b.val :=
  (fmod_eq_ok a b c).mp h |>.2

/-! ## The checked narrowing

`toCLUint64?` delegates to `CLUint64.ofInt?`, so its laws are the narrowing
laws of `Proofs/CLUint.lean` read through the projection. -/

/-- `Uint64(n)` from a plain value succeeds exactly on `[0, 2^64)`. -/
theorem toCLUint64_ok_iff (v : CLInt) :
    (∃ u, v.toCLUint64? = .ok u) ↔
      0 ≤ v.toPlainInt ∧ v.toPlainInt < 18446744073709551616 :=
  ofInt_ok_iff v.val

/-- A successful narrowing returns the exact value. -/
theorem toCLUint64_value (v : CLInt) (u : CLUint64) (h : v.toCLUint64? = .ok u) :
    u.toPlainNat = v.toPlainInt.toNat :=
  ofInt_value v.val u h

end EthCLLib.Proofs
