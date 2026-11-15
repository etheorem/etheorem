import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Proofs.CLUint`: the success and value facts for `CLUint64`

The ten-lemma set the fork proofs of Stage 3 build on
(`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §4.5, §5.1, and open work item 2).
Each of the five operators gets a pair. The success lemma says when the
operator returns `.ok`, in the plain-`int` terms of the pyspec's range test:
`add` and `mul` succeed exactly when the sum or product fits in `[0, 2^64)`,
`sub` when it cannot go below zero, and `div` and `mod` when the divisor is
not zero. The value lemma says what the returned value reads back as through
`toPlainInt`: the `Nat` result of the same operation on the plain integers.

The success lemmas are stated over the syntax form a fork body writes
(`(a + b : Checked CLUint64)`) and unfold through one `rfl` bridge to the
named operator (`add_eq` and friends). Behind that bridge the proofs are
`omega` over the native widths: `UInt64` is `BitVec 64`, so `toNat_add`,
`toNat_mul`, `toNat_div`, and friends reduce every operator to `Nat`
arithmetic modulo `2 ^ 64`. Only `mul` needs more: its overflow test
`a * b / a != b` divides back after a wrapping multiply, and
`mul_div_mod_eq_mul_iff` below shows that test says "the product did not fit"
exactly when the `Nat` product reaches `2 ^ 64`. Task 1.4 leaves that bridge
private: the simp set at the end of this file works on `Checked` equations,
and the native-width test stays behind `mul_ok_iff`, which already reads it.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-! ## The syntax bridges

Each bridge unfolds the operator instance to the named function. All five are
`rfl`, so no law is assumed anywhere in this file. -/

/-- `a + b` on values goes through the named `add`. -/
theorem add_eq (a b : CLUint64) : (a + b : Checked CLUint64) = CLUint64.add a b := rfl

/-- `a - b` on values goes through the named `sub`. -/
theorem sub_eq (a b : CLUint64) : (a - b : Checked CLUint64) = CLUint64.sub a b := rfl

/-- `a * b` on values goes through the named `mul`. -/
theorem mul_eq (a b : CLUint64) : (a * b : Checked CLUint64) = CLUint64.mul a b := rfl

/-- `a / b` on values goes through the named `div`. -/
theorem div_eq (a b : CLUint64) : (a / b : Checked CLUint64) = CLUint64.div a b := rfl

/-- `a % b` on values goes through the named `mod`. -/
theorem mod_eq (a b : CLUint64) : (a % b : Checked CLUint64) = CLUint64.mod a b := rfl

/-! ## The `mul` test bridge

`mul` detects overflow by dividing the wrapped product back by `a` and
comparing with `b`. The two lemmas here reduce that test to one `Nat`
comparison, which the success and value proofs then hand to `omega`. -/

/-- Dividing a product back by one factor returns the other factor exactly
when the product fit in `2 ^ 64`. -/
private theorem mul_div_mod_eq_mul_iff (A B : Nat) (hA : 0 < A) :
    (A * B % 2 ^ 64) / A = B ↔ A * B < 2 ^ 64 := by
  constructor
  · intro heq
    have h1 : A * ((A * B % 2 ^ 64) / A) ≤ A * B % 2 ^ 64 := Nat.mul_div_le _ _
    rw [heq] at h1
    have h2 := Nat.mod_lt (A * B) (by omega)
    omega
  · intro hlt
    have hmod : A * B % 2 ^ 64 = A * B := by omega
    rw [hmod, Nat.mul_div_cancel_left _ hA]

/-- `mul`'s native-width test is false exactly when the `Nat` product fits
in `2 ^ 64`. With `a = 0` the test is false and the product is zero, so both
directions reduce to the `a ≠ 0` case, where the wrapped product is
`a.toNat * b.toNat % 2 ^ 64` and `UInt64` division reads back as `Nat`
division. -/
private theorem mul_test_false_iff {a b : UInt64} :
    (a != 0 && a * b / a != b) = false ↔ a.toNat * b.toNat < 2 ^ 64 := by
  by_cases ha : a = 0
  · simp [ha]
  · have hA : 0 < a.toNat := by
      have h0 : a.toNat ≠ 0 := by
        intro h0
        exact ha (UInt64.toNat_inj.mp (by rw [h0]; decide))
      omega
    constructor
    · intro h
      have h1 : (a != 0) = true := by simp [ha]
      rw [h1, Bool.true_and, bne_eq_false_iff_eq] at h
      have hkey : (a * b / a).toNat = a.toNat * b.toNat % 2 ^ 64 / a.toNat := by
        rw [UInt64.toNat_div, UInt64.toNat_mul]
      rw [h] at hkey
      exact (mul_div_mod_eq_mul_iff _ _ hA).mp hkey.symm
    · intro hlt
      have h1 : (a != 0) = true := by simp [ha]
      rw [h1, Bool.true_and, bne_eq_false_iff_eq]
      have hmod : a.toNat * b.toNat % 2 ^ 64 = a.toNat * b.toNat := by omega
      have hkey : (a * b / a).toNat = b.toNat := by
        rw [UInt64.toNat_div, UInt64.toNat_mul, hmod, Nat.mul_div_cancel_left _ hA]
      exact UInt64.toNat_inj.mp hkey

/-- When `mul`'s test returns true, the `Nat` product reached `2 ^ 64`. -/
private theorem mul_test_true {a b : UInt64} (h : (a != 0 && a * b / a != b) = true) :
    ¬ (a.toNat * b.toNat < 2 ^ 64) := by
  have h1 : (a != 0) = true := by
    cases hb : (a != 0) with
    | true => rfl
    | false => rw [hb, Bool.false_and] at h; simp at h
  have ha : a ≠ 0 := bne_iff_ne.mp h1
  have hA : 0 < a.toNat := by
    have h0 : a.toNat ≠ 0 := by
      intro h0
      exact ha (UInt64.toNat_inj.mp (by rw [h0]; decide))
    omega
  rw [h1, Bool.true_and, bne_iff_ne] at h
  intro hlt
  have hmod : a.toNat * b.toNat % 2 ^ 64 = a.toNat * b.toNat := by omega
  have hkey : (a * b / a).toNat = b.toNat := by
    rw [UInt64.toNat_div, UInt64.toNat_mul, hmod, Nat.mul_div_cancel_left _ hA]
  exact h (UInt64.toNat_inj.mp hkey)

/-! ## Success

`add` and `mul` raise exactly at the top of the range, `sub` exactly below
zero, `div` and `mod` on a zero divisor alone. This is §5.1 of the design:
the checked operators raise where the pyspec raises, and nowhere else. -/

/-- `+` succeeds exactly when the plain-`int` sum fits in `[0, 2^64)`. -/
theorem add_ok_iff (a b : CLUint64) :
    (∃ c, (a + b : Checked CLUint64) = .ok c) ↔ a.toPlainInt + b.toPlainInt < 2 ^ 64 := by
  rw [add_eq]
  unfold CLUint64.add CLUint64.toPlainInt
  have ha := a.val.toNat_lt
  have hb := b.val.toNat_lt
  constructor
  · rintro ⟨c, h⟩
    split at h
    · simp at h
    · rename_i hlt
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hlt
      omega
  · intro h
    refine ⟨(CLUint64.trustedOfUInt64 (a.val + b.val)), ?_⟩
    split
    · rename_i hlt
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hlt
      exfalso
      omega
    · rfl

/-- `-` succeeds exactly when the plain-`int` result cannot go below zero. -/
theorem sub_ok_iff (a b : CLUint64) :
    (∃ c, (a - b : Checked CLUint64) = .ok c) ↔ b.toPlainInt ≤ a.toPlainInt := by
  rw [sub_eq]
  unfold CLUint64.sub CLUint64.toPlainInt
  constructor
  · rintro ⟨c, h⟩
    split at h
    · simp at h
    · rename_i hlt
      rw [UInt64.lt_iff_toNat_lt] at hlt
      omega
  · intro h
    refine ⟨(CLUint64.trustedOfUInt64 (a.val - b.val)), ?_⟩
    split
    · rename_i hlt
      rw [UInt64.lt_iff_toNat_lt] at hlt
      exfalso
      omega
    · rfl

/-- `*` succeeds exactly when the plain-`int` product fits in `[0, 2^64)`. -/
theorem mul_ok_iff (a b : CLUint64) :
    (∃ c, (a * b : Checked CLUint64) = .ok c) ↔ a.toPlainInt * b.toPlainInt < 2 ^ 64 := by
  rw [mul_eq]
  unfold CLUint64.mul CLUint64.toPlainInt
  constructor
  · rintro ⟨c, h⟩
    split at h
    · simp at h
    · rename_i hcond
      rw [Bool.not_eq_true] at hcond
      exact mul_test_false_iff.mp hcond
  · intro h
    refine ⟨(CLUint64.trustedOfUInt64 (a.val * b.val)), ?_⟩
    split
    · rename_i hcond
      exact absurd h (mul_test_true hcond)
    · rfl

/-- `//` succeeds for every dividend and raises on a zero divisor alone. -/
theorem div_ok_iff (a b : CLUint64) :
    (∃ c, (a / b : Checked CLUint64) = .ok c) ↔ b.toPlainInt ≠ 0 := by
  rw [div_eq]
  unfold CLUint64.div CLUint64.toPlainInt
  constructor
  · rintro ⟨c, h⟩
    split at h
    · simp at h
    · rename_i hz
      intro hzero
      refine hz ?_
      have hb0 : b.val = 0 := by
        have hz' : (0 : UInt64).toNat = 0 := by decide
        exact UInt64.toNat_inj.mp (hzero.trans hz')
      rw [hb0]
      decide
  · intro h
    refine ⟨(CLUint64.trustedOfUInt64 (a.val / b.val)), ?_⟩
    split
    · rename_i hz
      have hb0 : b.val = 0 := beq_iff_eq.mp hz
      exact absurd (by rw [hb0]; decide) h
    · rfl

/-- `%` succeeds for every dividend and raises on a zero divisor alone. -/
theorem mod_ok_iff (a b : CLUint64) :
    (∃ c, (a % b : Checked CLUint64) = .ok c) ↔ b.toPlainInt ≠ 0 := by
  rw [mod_eq]
  unfold CLUint64.mod CLUint64.toPlainInt
  constructor
  · rintro ⟨c, h⟩
    split at h
    · simp at h
    · rename_i hz
      intro hzero
      refine hz ?_
      have hb0 : b.val = 0 := by
        have hz' : (0 : UInt64).toNat = 0 := by decide
        exact UInt64.toNat_inj.mp (hzero.trans hz')
      rw [hb0]
      decide
  · intro h
    refine ⟨(CLUint64.trustedOfUInt64 (a.val % b.val)), ?_⟩
    split
    · rename_i hz
      have hb0 : b.val = 0 := beq_iff_eq.mp hz
      exact absurd (by rw [hb0]; decide) h
    · rfl

/-! ## Value

When an operator succeeds, the value it returns reads back through
`toPlainInt` as the `Nat` result of the same operation on the plain integers.
`Nat` subtraction, division, and modulo already floor the way the checked
operators need, so each statement is one equation. -/

/-- A successful `+` returns the plain-`int` sum. -/
theorem add_value (a b c : CLUint64) (h : (a + b : Checked CLUint64) = .ok c) :
    c.toPlainInt = a.toPlainInt + b.toPlainInt := by
  rw [add_eq] at h
  unfold CLUint64.toPlainInt
  unfold CLUint64.add at h
  split at h
  · simp at h
  · rename_i hcond
    have ha := a.val.toNat_lt
    have hb := b.val.toNat_lt
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hcond
    injection h with hc
    subst hc
    rw [UInt64.toNat_add]
    omega

/-- A successful `-` returns the truncating `Nat` difference. -/
theorem sub_value (a b c : CLUint64) (h : (a - b : Checked CLUint64) = .ok c) :
    c.toPlainInt = a.toPlainInt - b.toPlainInt := by
  rw [sub_eq] at h
  unfold CLUint64.toPlainInt
  unfold CLUint64.sub at h
  split at h
  · simp at h
  · rename_i hcond
    rw [UInt64.lt_iff_toNat_lt] at hcond
    have hle : b.val.toNat ≤ a.val.toNat := by omega
    injection h with hc
    subst hc
    exact UInt64.toNat_sub_of_le a.val b.val (UInt64.le_iff_toNat_le.mpr hle)

/-- A successful `*` returns the plain-`int` product; the success side of
`mul_ok_iff` is what keeps it inside `2 ^ 64`, where `Nat` and the native
width agree. -/
theorem mul_value (a b c : CLUint64) (h : (a * b : Checked CLUint64) = .ok c) :
    c.toPlainInt = a.toPlainInt * b.toPlainInt := by
  rw [mul_eq] at h
  unfold CLUint64.toPlainInt
  unfold CLUint64.mul at h
  split at h
  · simp at h
  · rename_i hcond
    rw [Bool.not_eq_true] at hcond
    have hlt : a.val.toNat * b.val.toNat < 2 ^ 64 := mul_test_false_iff.mp hcond
    injection h with hc
    subst hc
    rw [UInt64.toNat_mul]
    omega

/-- A successful `//` returns the truncating `Nat` quotient. -/
theorem div_value (a b c : CLUint64) (h : (a / b : Checked CLUint64) = .ok c) :
    c.toPlainInt = a.toPlainInt / b.toPlainInt := by
  rw [div_eq] at h
  unfold CLUint64.toPlainInt
  unfold CLUint64.div at h
  split at h
  · simp at h
  · injection h with hc
    subst hc
    exact UInt64.toNat_div a.val b.val

/-- A successful `%` returns the `Nat` remainder. -/
theorem mod_value (a b c : CLUint64) (h : (a % b : Checked CLUint64) = .ok c) :
    c.toPlainInt = a.toPlainInt % b.toPlainInt := by
  rw [mod_eq] at h
  unfold CLUint64.toPlainInt
  unfold CLUint64.mod at h
  split at h
  · simp at h
  · injection h with hc
    subst hc
    exact UInt64.toNat_mod a.val b.val

/-! ## The chain simp set

A fork body writes a whole arithmetic chain under one bind, so a proof about it
faces one equation of the form `(a * b / c : Checked CLUint64) = .ok r`. Per
SPEC_ARITHMETIC §3.2 the pyspec tests each step, so the success condition of a
chain is a conjunction over the steps, and §4.3 says a plain expression binds
once. The lemmas in this section turn such an equation into that conjunction
in one `simp_arith` call: each step's range or zero-divisor fact, plus the
value equation. The atoms are the §Success and §Value pairs above, one per
operator; the chain lemmas are proved from them, so the set adds no law of its
own. The chain lemmas cover the numerator shapes `a * b * c` and `a * n * b`
(plain-`int` factor first, as the reward sites write it) over the divisor
shapes `c` and `d * n`, with the plain-`int` operand in the first product,
as the reward sites write it. The penalty arm `a * n / m` and a bare-`Nat`
divisor are later work.

A `register_simp_attr` set cannot live in the file that uses it: the attribute
becomes visible only to importers (`SizzLean/Proofs/Simp.lean` records the
same quirk). The set is therefore a `simp_arith` macro over one `simp only`
call, which keeps it in this module and equally available to importers. -/

/-- The wrapped `Nat` product reads back as the plain product once the fit is
known: `% 2 ^ 64` is the identity below the bound. -/
theorem toPlainInt_mul_val (a b : CLUint64) (h : a.toPlainInt * b.toPlainInt < 2 ^ 64) :
    CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (a.val * b.val)) = a.toPlainInt * b.toPlainInt := by
  show (a.val * b.val).toNat = a.toPlainInt * b.toPlainInt
  rw [UInt64.toNat_mul]
  exact Nat.mod_eq_of_lt h

/-- A `Nat` inside the range reads back unchanged through `UInt64.ofNat`. -/
theorem toPlainInt_ofNat_val (n : Nat) (h : n < 2 ^ 64) :
    CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat n)) = n := by
  show (UInt64.ofNat n).toNat = n
  exact UInt64.toNat_ofNat_of_lt' h

/-- `toPlainInt` separates the values: a `CLUint64` is its native `UInt64`. -/
theorem toPlainInt_inj {a b : CLUint64} (h : a.toPlainInt = b.toPlainInt) : a = b :=
  congrArg CLUint64.trustedOfUInt64 (UInt64.toNat_inj.mp h)

/-- A bind returns `.ok` exactly when the action and the continuation both do.
This is the one-step peel the chain lemmas apply from the outside in. -/
theorem bind_ok_iff {e : Checked CLUint64} {k : CLUint64 → Checked CLUint64} {r : CLUint64} :
    (e.bind k = .ok r) ↔ (∃ x, e = .ok x ∧ k x = .ok r) := by
  cases e with
  | error f => simp [Except.bind]
  | ok x => simp [Except.bind]

/-- Two binds in a row peel together, one existential per step. -/
theorem bind2_ok_iff {e₁ e₂ : Checked CLUint64}
    {k : CLUint64 → CLUint64 → Checked CLUint64} {r : CLUint64} :
    (e₁.bind (fun x => e₂.bind (fun y => k x y)) = .ok r) ↔
      (∃ x y, e₁ = .ok x ∧ e₂ = .ok y ∧ k x y = .ok r) := by
  rw [bind_ok_iff]
  cases e₂ with
  | error f => simp [Except.bind]
  | ok y => simp [Except.bind]

/-! The atoms: one equation lemma per operator, in the shape a proof meets,
`(a op b) = .ok r` on the left and plain-`Nat` facts on the right. -/

/-- `+` in equation form: the sum fits, and the result reads back as it. -/
theorem add_eq_ok (a b r : CLUint64) :
    ((a + b : Checked CLUint64) = .ok r) ↔
      a.toPlainInt + b.toPlainInt < 2 ^ 64 ∧ r.toPlainInt = a.toPlainInt + b.toPlainInt := by
  constructor
  · intro h
    exact ⟨(add_ok_iff a b).mp ⟨r, h⟩, add_value a b r h⟩
  · rintro ⟨hfit, hval⟩
    obtain ⟨x, hx⟩ := (add_ok_iff a b).mpr hfit
    have hxr : x = r := toPlainInt_inj (by rw [add_value a b x hx]; exact hval.symm)
    rw [hx, hxr]

/-- `-` in equation form: no underflow, and the result reads back as the
truncating difference. -/
theorem sub_eq_ok (a b r : CLUint64) :
    ((a - b : Checked CLUint64) = .ok r) ↔
      b.toPlainInt ≤ a.toPlainInt ∧ r.toPlainInt = a.toPlainInt - b.toPlainInt := by
  constructor
  · intro h
    exact ⟨(sub_ok_iff a b).mp ⟨r, h⟩, sub_value a b r h⟩
  · rintro ⟨hle, hval⟩
    obtain ⟨x, hx⟩ := (sub_ok_iff a b).mpr hle
    have hxr : x = r := toPlainInt_inj (by rw [sub_value a b x hx]; exact hval.symm)
    rw [hx, hxr]

/-- `*` in equation form: the product fits, and the result reads back as it. -/
theorem mul_eq_ok (a b r : CLUint64) :
    ((a * b : Checked CLUint64) = .ok r) ↔
      a.toPlainInt * b.toPlainInt < 2 ^ 64 ∧ r.toPlainInt = a.toPlainInt * b.toPlainInt := by
  constructor
  · intro h
    exact ⟨(mul_ok_iff a b).mp ⟨r, h⟩, mul_value a b r h⟩
  · rintro ⟨hfit, hval⟩
    obtain ⟨x, hx⟩ := (mul_ok_iff a b).mpr hfit
    have hxr : x = r := toPlainInt_inj (by rw [mul_value a b x hx]; exact hval.symm)
    rw [hx, hxr]

/-- `//` in equation form: the divisor is nonzero, and the result reads back
as the truncating quotient. -/
theorem div_eq_ok (a b r : CLUint64) :
    ((a / b : Checked CLUint64) = .ok r) ↔
      b.toPlainInt ≠ 0 ∧ r.toPlainInt = a.toPlainInt / b.toPlainInt := by
  constructor
  · intro h
    exact ⟨(div_ok_iff a b).mp ⟨r, h⟩, div_value a b r h⟩
  · rintro ⟨hnz, hval⟩
    obtain ⟨x, hx⟩ := (div_ok_iff a b).mpr hnz
    have hxr : x = r := toPlainInt_inj (by rw [div_value a b x hx]; exact hval.symm)
    rw [hx, hxr]

/-- `%` in equation form: the divisor is nonzero, and the result reads back as
the remainder. -/
theorem mod_eq_ok (a b r : CLUint64) :
    ((a % b : Checked CLUint64) = .ok r) ↔
      b.toPlainInt ≠ 0 ∧ r.toPlainInt = a.toPlainInt % b.toPlainInt := by
  constructor
  · intro h
    exact ⟨(mod_ok_iff a b).mp ⟨r, h⟩, mod_value a b r h⟩
  · rintro ⟨hnz, hval⟩
    obtain ⟨x, hx⟩ := (mod_ok_iff a b).mpr hnz
    have hxr : x = r := toPlainInt_inj (by rw [mod_value a b x hx]; exact hval.symm)
    rw [hx, hxr]

/-- A plain-`int` operand: `Uint64 * n` computes unbounded and then tests, so
the result fits exactly when the product does. -/
theorem natMul_eq_ok (d : CLUint64) (n : Nat) (e : CLUint64) :
    ((d * n : Checked CLUint64) = .ok e) ↔
      d.toPlainInt * n < 2 ^ 64 ∧ e.toPlainInt = d.toPlainInt * n := by
  show (CLUint64.natMul d.toPlainInt n = .ok e) ↔ _
  unfold CLUint64.natMul CLUint64.ofNat?
  constructor
  · intro h
    split at h
    · injection h with hval
      refine ⟨by assumption, ?_⟩
      rw [← hval]
      exact toPlainInt_ofNat_val _ (by assumption)
    · simp at h
  · rintro ⟨hfit, hval⟩
    have he : e = (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))) :=
      toPlainInt_inj (by rw [hval]; exact (toPlainInt_ofNat_val _ hfit).symm)
    rw [ite_eq_left (show d.toPlainInt * n < UInt64.size from hfit), he]
    -- `rw`'s automatic `rfl` runs at reducible transparency, so it does not unfold the named
    -- constructor; this one does.
    rfl

/-! The chain lemmas: the shapes a fork body binds in one `let ← `. -/

/-- A three-factor product binds once and raises when any factor step
overflows: `a * b` must fit, and the product with `c` must fit. -/
theorem mul3_eq_ok (a b c m : CLUint64) :
    ((a * b * c : Checked CLUint64) = .ok m) ↔
      a.toPlainInt * b.toPlainInt < 2 ^ 64 ∧
      a.toPlainInt * b.toPlainInt * c.toPlainInt < 2 ^ 64 ∧
      m.toPlainInt = a.toPlainInt * b.toPlainInt * c.toPlainInt := by
  show ((a * b).bind (fun x => CLUint64.mul x c) = .ok m) ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨x, hx, hxc⟩
    obtain ⟨h1, hvalx⟩ := (mul_eq_ok a b x).mp hx
    obtain ⟨h2, hvalm⟩ := (mul_eq_ok x c m).mp hxc
    refine ⟨h1, ?_, ?_⟩
    · rw [← hvalx]
      exact h2
    · rw [hvalm, hvalx]
  · rintro ⟨h1, h2, hvalm⟩
    exact ⟨(CLUint64.trustedOfUInt64 (a.val * b.val)),
      (mul_eq_ok a b (CLUint64.trustedOfUInt64 (a.val * b.val))).mpr ⟨h1, toPlainInt_mul_val a b h1⟩,
      (mul_eq_ok (CLUint64.trustedOfUInt64 (a.val * b.val)) c m).mpr ⟨by rw [toPlainInt_mul_val a b h1]; exact h2,
        by rw [hvalm, toPlainInt_mul_val a b h1]⟩⟩

/-- The three-factor product whose first step is a `natMul`: the reward
sites take `base_reward * weight` with `weight` a plain `int`
(`participationFlagWeights`), so the first step computes unbounded and tests,
and the second is a checked `mul`. -/
theorem natMul_mul_eq_ok (a : CLUint64) (w : Nat) (c m : CLUint64) :
    ((a * w * c : Checked CLUint64) = .ok m) ↔
      a.toPlainInt * w < 2 ^ 64 ∧
      a.toPlainInt * w * c.toPlainInt < 2 ^ 64 ∧
      m.toPlainInt = a.toPlainInt * w * c.toPlainInt := by
  show ((CLUint64.natMul a.toPlainInt w).bind (fun x => CLUint64.mul x c) = .ok m) ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨x, hx, hxc⟩
    obtain ⟨h1, hvalx⟩ := (natMul_eq_ok a w x).mp hx
    obtain ⟨h2, hvalm⟩ := (mul_eq_ok x c m).mp hxc
    refine ⟨h1, ?_, ?_⟩
    · rw [← hvalx]
      exact h2
    · rw [hvalm, hvalx]
  · rintro ⟨h1, h2, hvalm⟩
    exact ⟨(CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w))),
      (natMul_eq_ok a w _).mpr ⟨h1, toPlainInt_ofNat_val _ h1⟩,
      (mul_eq_ok (CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w))) c m).mpr
        ⟨by rw [toPlainInt_ofNat_val _ h1]; exact h2,
          by rw [hvalm, toPlainInt_ofNat_val _ h1]⟩⟩

/-- The two-step chain the pyspec writes as `a * b // c`: the product must
fit, the divisor must be nonzero, and the value is the `Nat` quotient. -/
theorem mul_div_eq_ok (a b c r : CLUint64) :
    ((a * b / c : Checked CLUint64) = .ok r) ↔
      a.toPlainInt * b.toPlainInt < 2 ^ 64 ∧ c.toPlainInt ≠ 0 ∧
        r.toPlainInt = a.toPlainInt * b.toPlainInt / c.toPlainInt := by
  show ((a * b).bind (fun x => CLUint64.div x c) = .ok r) ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨x, hx, hxc⟩
    exact ⟨(mul_ok_iff a b).mp ⟨x, hx⟩, (div_ok_iff x c).mp ⟨r, hxc⟩,
      by rw [div_value x c r hxc, mul_value a b x hx]⟩
  · rintro ⟨hfit, hnz, hval⟩
    refine ⟨(CLUint64.trustedOfUInt64 (a.val * b.val)),
      (mul_eq_ok a b (CLUint64.trustedOfUInt64 (a.val * b.val))).mpr ⟨hfit, toPlainInt_mul_val a b hfit⟩, ?_⟩
    exact (div_eq_ok (CLUint64.trustedOfUInt64 (a.val * b.val)) c r).mpr ⟨hnz, by rw [hval, toPlainInt_mul_val a b hfit]⟩

/-- The reward formula of `get_flag_index_deltas`
(`phase0/beacon-chain.md`, `WEIGHT_DENOMINATOR = 64`): a three-factor
numerator over a product divisor. Each step is tested in order, so the
condition is five facts: `a * b` fits, the product with `c` fits, `d * n`
fits and is nonzero, and the value is the `Nat` quotient. -/
theorem mul3_div_mulNat_eq_ok (a b c d : CLUint64) (n : Nat) (r : CLUint64) :
    (((a * b * c) / (d * n) : Checked CLUint64) = .ok r) ↔
      a.toPlainInt * b.toPlainInt < 2 ^ 64 ∧
      a.toPlainInt * b.toPlainInt * c.toPlainInt < 2 ^ 64 ∧
      d.toPlainInt * n < 2 ^ 64 ∧
      d.toPlainInt * n ≠ 0 ∧
      r.toPlainInt = a.toPlainInt * b.toPlainInt * c.toPlainInt / (d.toPlainInt * n) := by
  show (((a * b).bind (fun x => CLUint64.mul x c)).bind
      (fun m => (CLUint64.natMul d.toPlainInt n).bind (fun y => CLUint64.div m y)) = .ok r) ↔ _
  rw [bind2_ok_iff]
  constructor
  · rintro ⟨m, y, hm, hy, hdiv⟩
    obtain ⟨h1, h2, hvalm⟩ := (mul3_eq_ok a b c m).mp hm
    obtain ⟨h3, hvale⟩ := (natMul_eq_ok d n y).mp hy
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · have hnz := (div_ok_iff m y).mp ⟨r, hdiv⟩
      have hdn : d.toPlainInt * n = y.toPlainInt := hvale.symm
      rw [hdn]
      exact hnz
    · rw [div_value m y r hdiv, hvalm, hvale]
  · rintro ⟨h1, h2, h3, hnz, hval⟩
    have h1' : a.val.toNat * b.val.toNat < 2 ^ 64 := h1
    have h2' : (a.val.toNat * b.val.toNat) * c.val.toNat < 2 ^ 64 := h2
    have hmv : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (a.val * b.val * c.val)) =
        a.toPlainInt * b.toPlainInt * c.toPlainInt := by
      show ((a.val * b.val) * c.val).toNat = _
      rw [UInt64.toNat_mul, UInt64.toNat_mul, Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt h2']
      rfl
    have hyv : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))) = d.toPlainInt * n :=
      toPlainInt_ofNat_val _ h3
    refine ⟨(CLUint64.trustedOfUInt64 (a.val * b.val * c.val)), (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))), ?_, ?_, ?_⟩
    · exact (mul3_eq_ok a b c _).mpr ⟨h1, h2, hmv⟩
    · exact (natMul_eq_ok d n _).mpr ⟨h3, hyv⟩
    · exact (div_eq_ok (CLUint64.trustedOfUInt64 (a.val * b.val * c.val)) (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))) r).mpr
        ⟨by rw [hyv]; exact hnz, by rw [hval, hmv, hyv]⟩

/-- The reward formula as the fork body writes it: the weight is a plain
`Nat` (`participationFlagWeights`), so the numerator's first product goes
through `natMul`. The condition and value are the same five `Nat` facts as
`mul3_div_mulNat_eq_ok`. -/
theorem natMul_mul_div_mulNat_eq_ok (a : CLUint64) (w : Nat) (c d : CLUint64) (n : Nat)
    (r : CLUint64) :
    (((a * w * c) / (d * n) : Checked CLUint64) = .ok r) ↔
      a.toPlainInt * w < 2 ^ 64 ∧
      a.toPlainInt * w * c.toPlainInt < 2 ^ 64 ∧
      d.toPlainInt * n < 2 ^ 64 ∧
      d.toPlainInt * n ≠ 0 ∧
      r.toPlainInt = a.toPlainInt * w * c.toPlainInt / (d.toPlainInt * n) := by
  show (((CLUint64.natMul a.toPlainInt w).bind (fun x => CLUint64.mul x c)).bind
      (fun m => (CLUint64.natMul d.toPlainInt n).bind (fun y => CLUint64.div m y)) = .ok r) ↔ _
  rw [bind2_ok_iff]
  constructor
  · rintro ⟨m, y, hm, hy, hdiv⟩
    obtain ⟨h1, h2, hvalm⟩ := (natMul_mul_eq_ok a w c m).mp hm
    obtain ⟨h3, hvale⟩ := (natMul_eq_ok d n y).mp hy
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · have hnz := (div_ok_iff m y).mp ⟨r, hdiv⟩
      have hdn : d.toPlainInt * n = y.toPlainInt := hvale.symm
      rw [hdn]
      exact hnz
    · rw [div_value m y r hdiv, hvalm, hvale]
  · rintro ⟨h1, h2, h3, hnz, hval⟩
    have hXv : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w))) = a.toPlainInt * w :=
      toPlainInt_ofNat_val _ h1
    have hfit2 : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w))) * c.toPlainInt
        < 2 ^ 64 := by
      rw [hXv]
      exact h2
    have hmv : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w) * c.val)) =
        a.toPlainInt * w * c.toPlainInt :=
      (toPlainInt_mul_val (CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w))) c hfit2).trans (by rw [hXv])
    have hyv : CLUint64.toPlainInt (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))) = d.toPlainInt * n :=
      toPlainInt_ofNat_val _ h3
    refine ⟨(CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w) * c.val)), (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))),
      ?_, ?_, ?_⟩
    · exact (natMul_mul_eq_ok a w c _).mpr ⟨h1, h2, hmv⟩
    · exact (natMul_eq_ok d n _).mpr ⟨h3, hyv⟩
    · exact (div_eq_ok (CLUint64.trustedOfUInt64 (UInt64.ofNat (a.toPlainInt * w) * c.val))
          (CLUint64.trustedOfUInt64 (UInt64.ofNat (d.toPlainInt * n))) r).mpr
        ⟨by rw [hyv]; exact hnz, by rw [hval, hmv, hyv]⟩

/-- The chain simp set. One `simp_arith` call reduces a bound chain equation
to the per-step `Nat` facts and the value equation; see `mul3_div_mulNat_eq_ok`
for the conjunction of the reward shape. -/
macro "simp_arith" : tactic =>
  `(tactic| simp only [add_eq_ok, sub_eq_ok, mul_eq_ok, div_eq_ok, mod_eq_ok,
      natMul_eq_ok, mul_div_eq_ok, mul3_div_mulNat_eq_ok, natMul_mul_eq_ok,
      natMul_mul_div_mulNat_eq_ok])

/-- One `simp_arith` call reduces the two-step chain to three `Nat` facts. -/
example (a b c r : CLUint64) :
    ((a * b / c : Checked CLUint64) = .ok r) ↔
      a.toPlainInt * b.toPlainInt < 2 ^ 64 ∧ c.toPlainInt ≠ 0 ∧
        r.toPlainInt = a.toPlainInt * b.toPlainInt / c.toPlainInt := by
  simp_arith

/-- Stand-in for the fork package's `Const.weightDenominator`, which lives in
`EthCLSpecs` and is out of reach here. The pinned value is `64`
(`phase0/beacon-chain.md`, `get_flag_index_deltas`). -/
def weightDenominator : Nat := 64

/-- The success condition and value of the reward step in
`get_flag_index_deltas` (`phase0/beacon-chain.md`):

```
reward_numerator = base_reward * weight * unslashed_participating_increments
rewards[index] += reward_numerator // (active_increments * WEIGHT_DENOMINATOR)
```

`WEIGHT_DENOMINATOR` is `64`, held here by `weightDenominator`. Per
SPEC_ARITHMETIC §3.2 the pyspec tests each step, so a zero
`unslashedIncrements` does not rescue an overflowing `baseReward * weight`:
the condition is a conjunction, and the second conjunct states the
product-with-`unslashedIncrements` step on its own. Stated over the operands
abstractly; the fork-level statement lands in Stage 3. The fork site binds
`weight` as a plain `Nat`, so the shape it writes is
`flagRewardNatWeight_ok_iff` below. -/
theorem flagReward_ok_iff (baseReward weight unslashedIncrements activeIncrements r : CLUint64) :
    (((baseReward * weight * unslashedIncrements) /
        (activeIncrements * weightDenominator) : Checked CLUint64) = .ok r) ↔
      baseReward.toPlainInt * weight.toPlainInt < 2 ^ 64 ∧
      baseReward.toPlainInt * weight.toPlainInt * unslashedIncrements.toPlainInt < 2 ^ 64 ∧
      activeIncrements.toPlainInt * weightDenominator < 2 ^ 64 ∧
      activeIncrements.toPlainInt * weightDenominator ≠ 0 ∧
      r.toPlainInt =
        baseReward.toPlainInt * weight.toPlainInt * unslashedIncrements.toPlainInt /
          (activeIncrements.toPlainInt * weightDenominator) := by
  simp_arith

/-- The same reward step over the fork body's actual operand types: the site
binds `weight := Const.participationFlagWeights[flagIndex]!`, a plain `Nat`,
so the numerator's first product tests through `natMul`. The condition and
value are the same five facts. Stated over the operands abstractly; the
fork-level statement lands in Stage 3. -/
theorem flagRewardNatWeight_ok_iff (baseReward : CLUint64) (weight : Nat)
    (unslashedIncrements activeIncrements r : CLUint64) :
    (((baseReward * weight * unslashedIncrements) /
        (activeIncrements * weightDenominator) : Checked CLUint64) = .ok r) ↔
      baseReward.toPlainInt * weight < 2 ^ 64 ∧
      baseReward.toPlainInt * weight * unslashedIncrements.toPlainInt < 2 ^ 64 ∧
      activeIncrements.toPlainInt * weightDenominator < 2 ^ 64 ∧
      activeIncrements.toPlainInt * weightDenominator ≠ 0 ∧
      r.toPlainInt =
        baseReward.toPlainInt * weight * unslashedIncrements.toPlainInt /
          (activeIncrements.toPlainInt * weightDenominator) := by
  simp_arith

end EthCLLib.Proofs

