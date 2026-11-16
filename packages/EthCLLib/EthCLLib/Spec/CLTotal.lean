import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Spec.CLTotal`: the proved-total routes of the operation matrix

The operation matrix of `SPEC_ARITHMETIC.md` §4.2 leaves a few routes `Checked`
only because the *unguarded* form can raise. Where the guard is part of the
route itself, the route is total and returns the value directly
(`SPEC_ARITHMETIC.md` §4.2, "Total operations with a proof"):

- `PositiveDivisor`: a natural divisor with a kernel-checked `0 < n` proof.
  Division and modulo of a bound `CLUint64` dividend by the wrapper return
  `CLUint64` directly, because both results are at most the dividend.
- Same-width bitwise `&&&` / `|||` / `^^^` on `CLUint64`: the result of two
  in-range values cannot leave the range (§5.1, same-width bitwise row).
- Right shift `a >>> count` with a `Nat` count: total, zero for `count ≥ 64`
  (§5.1: the pinned `shr` is total and NOT modulo 64, so `7 >>> 64 = 0`).
- Checked power and checked left shift: `Checked` results with an early range
  decision. The decision never builds an unbounded intermediate: power
  decides through `powCapped`, which builds the unbounded power only for a
  base of at least `2` and an exponent below `64`, and left shift tests
  `a * 2^count` only for `count < 64`, where the factor is at most `2^63`.
  Both are proved equal to their unbounded definitions (§5.1).
- The checked mixed right shift for a plain left operand or a signed count
  (`Nat >>> CLUint64`): not total, per §5.1. `(2**64) >> Uint64(0)` raises,
  so the route keeps the result range test and the two routes stay distinct.

This module sits beside `Spec/CLUint.lean`: `CLUint.lean` owns
the raising operator matrix, this file owns the routes whose guard is a proof
the caller supplies. It stays elaborator-free like the rest of `Spec/`. The
value wrappers go through `ofNatLT` and `trustedOfUInt64`, the proof-carrying
and wire routes the contract admits for proved-total operations
(`SPEC_ARITHMETIC.md` §4.5).
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-! ## The positive divisor

A natural divisor plus its positivity proof. A named constant view
(`Const.slotsPerEpochDiv`, Stage 4) carries the proof once, so a formula that
divides by the constant stays pure. The wrapper has no literal instance and no
coercion: building one is an explicit `⟨n, h⟩`, so the proof is visible at
every construction site. The ordinary divisor routes on two `CLUint64` values
stay `Checked`; this wrapper adds a route, it does not change one. -/

/-- A natural divisor with a kernel-checked positivity proof. -/
structure PositiveDivisor where
  /-- The divisor value. -/
  n : Nat
  /-- The divisor is positive. -/
  positive : 0 < n

namespace CLUint64

/-- Division by a positive divisor: total. The quotient is at most the
dividend, which is in range, so no range test is needed
(`SPEC_ARITHMETIC.md` §4.2). -/
@[inline] def divPos (a : CLUint64) (d : PositiveDivisor) : CLUint64 :=
  ofNatLT (a.toPlainNat / d.n) (by
    have ha : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
    have hd : a.toPlainNat / d.n ≤ a.toPlainNat := Nat.div_le_self _ _
    show a.toPlainNat / d.n < 18446744073709551616
    omega)

/-- Modulo by a positive divisor: total. The remainder is at most the
dividend. -/
@[inline] def modPos (a : CLUint64) (d : PositiveDivisor) : CLUint64 :=
  ofNatLT (a.toPlainNat % d.n) (by
    have ha : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
    have hd : a.toPlainNat % d.n ≤ a.toPlainNat := Nat.mod_le _ _
    show a.toPlainNat % d.n < 18446744073709551616
    omega)

/-- The total division computes the plain quotient. -/
theorem divPos_toPlainNat (a : CLUint64) (d : PositiveDivisor) :
    (a.divPos d).toPlainNat = a.toPlainNat / d.n :=
  ofNatLT_toPlainNat _ _

/-- The total modulo computes the plain remainder. -/
theorem modPos_toPlainNat (a : CLUint64) (d : PositiveDivisor) :
    (a.modPos d).toPlainNat = a.toPlainNat % d.n :=
  ofNatLT_toPlainNat _ _

/-! ## Same-width bitwise operations

The `&&&`, `|||`, and `^^^` of two in-range values stay in range, so all three
return the value directly (§5.1, same-width bitwise row). The value laws below
say each computes the plain bitwise operation on `toPlainNat`. -/

/-- `&` on two checked values: total. -/
@[inline] def bitAnd (a b : CLUint64) : CLUint64 :=
  trustedOfUInt64 (a.val &&& b.val)

/-- `|` on two checked values: total. -/
@[inline] def bitOr (a b : CLUint64) : CLUint64 :=
  trustedOfUInt64 (a.val ||| b.val)

/-- `^` on two checked values: total. -/
@[inline] def bitXor (a b : CLUint64) : CLUint64 :=
  trustedOfUInt64 (a.val ^^^ b.val)

/-- `bitAnd` computes the plain `&&&`. -/
theorem bitAnd_toPlainNat (a b : CLUint64) :
    (a.bitAnd b).toPlainNat = a.toPlainNat &&& b.toPlainNat :=
  UInt64.toNat_and _ _

/-- `bitOr` computes the plain `|||`. -/
theorem bitOr_toPlainNat (a b : CLUint64) :
    (a.bitOr b).toPlainNat = a.toPlainNat ||| b.toPlainNat :=
  UInt64.toNat_or _ _

/-- `bitXor` computes the plain `^^^`. -/
theorem bitXor_toPlainNat (a b : CLUint64) :
    (a.bitXor b).toPlainNat = a.toPlainNat ^^^ b.toPlainNat :=
  UInt64.toNat_xor _ _

/-! ## Right shifts

`a >>> count` with a `Nat` count is total: the count is nonnegative and the
result is at most the dividend. The count is not taken modulo 64: for
`count ≥ 64` the result is zero, which is what the pinned pyspec `shr`
computes (`7 >> 64 = 0`, §5.1). A signed count or a plain left operand is NOT
total; those shapes go through `rshiftChecked` below, and §5.1 pins the
distinction: `(2**64) >> Uint64(0)` raises. -/

/-- The total right shift: `a >>> count` on the plain value. The count is NOT
taken modulo 64, so the result is zero from `count = 64` on. -/
@[inline] def rshift (a : CLUint64) (count : Nat) : CLUint64 :=
  ofNatLT (a.toPlainNat >>> count) (by
    show a.toPlainNat >>> count < 18446744073709551616
    rw [Nat.shiftRight_eq_div_pow]
    by_cases h : 64 ≤ count
    · have h2 : (18446744073709551616 : Nat) ≤ 2 ^ count :=
        Nat.pow_le_pow_right (n := 2) (by decide) h
      have ha : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
      rw [Nat.div_eq_of_lt (by omega)]
      decide
    · have hd : a.toPlainNat / 2 ^ count ≤ a.toPlainNat := Nat.div_le_self _ _
      have ha : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
      omega)

/-- `rshift` computes the plain `Nat` right shift: exact for `count < 64`,
zero from 64 on. -/
theorem rshift_toPlainNat (a : CLUint64) (count : Nat) :
    (a.rshift count).toPlainNat = a.toPlainNat >>> count :=
  ofNatLT_toPlainNat _ _

/-- The checked right shift: a plain left operand, or a signed count. A
negative count or a negative dividend raises; a nonnegative dividend
computes the plain shift on the natural value and runs the result range
test, exactly the pyspec shape §5.1 pins (`(2**64) >> Uint64(0)` raises).
Not total, and distinct from `rshift` on purpose. The shift runs on the
plain value, so no `2^count` is built for any input. The floor-division
route it restates: a negative dividend floors below zero, and a nonnegative
dividend's floor quotient by `2^count` is the plain shift
(`rshiftChecked_value`). -/
def rshiftChecked (a count : Int) : Checked CLUint64 :=
  if _hneg : count < 0 then
    .error (ArithFault.range ">>" 64 a count)
  else if _hn : a < 0 then
    -- The floor quotient of a negative dividend by `2^count` is negative,
    -- so the unbounded route's range test raises for every count
    -- (`Int.fdiv_neg_of_neg_of_pos`).
    .error (ArithFault.range ">>" 64 a count)
  else
    if _hc : a.toNat >>> count.toNat < UInt64.size then
      .ok (ofNatLT (a.toNat >>> count.toNat) _hc)
    else
      .error (ArithFault.range ">>" 64 a count)

/-- A negative shift count raises, before any range test. -/
theorem rshiftChecked_negCount (a count : Int) (h : count < 0) :
    rshiftChecked a count = .error (ArithFault.range ">>" 64 a count) :=
  dite_eq_left h

/-- A negative dividend raises for every nonnegative count: the floor
quotient by `2^count` is negative (`Int.fdiv_neg_of_neg_of_pos`), so the
unbounded route's range test rejects it. -/
theorem rshiftChecked_negDividend (a count : Int) (hn : ¬(count < 0))
    (ha : a < 0) :
    rshiftChecked a count = .error (ArithFault.range ">>" 64 a count) := by
  rw [rshiftChecked, dite_eq_right hn, dite_eq_left ha]

/-- A nonnegative in-range dividend shifted by `64` or more is zero, and the
route answers without building `2^count`. -/
theorem rshiftChecked_wide (a count : Int) (hn : ¬(count < 0))
    (hw : 0 ≤ a ∧ a < 18446744073709551616 ∧ 64 ≤ count.toNat) :
    rshiftChecked a count = .ok 0 := by
  rw [rshiftChecked, dite_eq_right hn, dite_eq_right (by omega)]
  have hz : a.toNat >>> count.toNat = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    refine Nat.div_eq_of_lt ?_
    have h1 : a.toNat < 18446744073709551616 := by omega
    have h64 : (18446744073709551616 : Nat) ≤ 2 ^ count.toNat :=
      Nat.pow_le_pow_right (n := 2) (by decide) hw.2.2
    exact Nat.lt_of_lt_of_le h1 h64
  rw [hz]
  rfl

/-- The value of a successful checked right shift is the plain shift. -/
theorem rshiftChecked_value (a count : Int) (hn : ¬(count < 0))
    (ha : 0 ≤ a) (c : CLUint64) (h : rshiftChecked a count = .ok c) :
    c.toPlainNat = a.toNat >>> count.toNat := by
  rw [rshiftChecked, dite_eq_right hn, dite_eq_right (by omega)] at h
  split at h
  · rename_i hc
    have hinj := Except.ok.inj h
    rw [← hinj]
    exact ofNatLT_toPlainNat _ _
  · exact absurd h (by simp)

/-- The checked right shift succeeds exactly when both operands are
nonnegative and the plain shift stays in range. -/
theorem rshiftChecked_ok_iff (a count : Int) :
    (∃ c, rshiftChecked a count = .ok c) ↔
      0 ≤ count ∧ 0 ≤ a ∧ a.toNat >>> count.toNat < UInt64.size := by
  constructor
  · rintro ⟨c, hc⟩
    rw [rshiftChecked] at hc
    split at hc
    · exact absurd hc (by simp)
    · split at hc
      · exact absurd hc (by simp)
      · rename_i h1 h2
        split at hc
        · rename_i h3
          exact ⟨by omega, by omega, h3⟩
        · exact absurd hc (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨CLUint64.ofNatLT (a.toNat >>> count.toNat) h3, ?_⟩
    rw [rshiftChecked, dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left h3]

/-! ## Checked power

`base ** exp` with a `Nat` exponent: a `Checked` result with an early range
decision. `powCapped` answers `min (base ^ exp) 2^64` in bounded time: a zero
or unit base is constant, and a base of at least `2` overflows by exponent
`64`, so the unbounded power is built only for an exponent below `64`.
`powCapped_eq` proves the capped value is `min (base ^ exp) 2^64`, which makes
the decision exact, including the zero base and `0 ** 0 = 1` (§5.1). -/

/-- `min (base ^ e) 2^64`, decided in bounded time: the unbounded power is
built only for a base of at least `2` and an exponent below `64`, so the
kernel reduces it and the pins in `Tests/CLTotalArith.lean` close by `decide`
for any exponent. The bounded-time claim covers the decision; the success
branch of `pow` still builds `base ^ exp` itself, which sits below `2^64`
whenever the test passes. -/
def powCapped (base e : Nat) : Nat :=
  if _h0 : base = 0 then
    if _hE : e = 0 then 1 else 0
  else if _h1 : base = 1 then 1
  else if _h64 : 64 ≤ e then UInt64.size
  else min (base ^ e) UInt64.size

/-- The bounded decision computes `min (base ^ e) 2^64`, the fact that makes
the early decision exact. -/
theorem powCapped_eq (base e : Nat) :
    powCapped base e = min (base ^ e) UInt64.size := by
  unfold powCapped
  split
  · rename_i h0
    subst h0
    split
    · rename_i hE
      subst hE
      rfl
    · rename_i hE
      rw [Nat.zero_pow (by omega), Nat.min_eq_left (by decide)]
  · rename_i h0
    split
    · rename_i h1
      subst h1
      rw [Nat.one_pow, Nat.min_eq_left (by decide)]
    · rename_i h1
      split
      · rename_i h64
        have hb : 2 ≤ base := by omega
        have hge : UInt64.size ≤ base ^ e := by
          calc UInt64.size = (2 : Nat) ^ 64 := rfl
            _ ≤ base ^ 64 := Nat.pow_le_pow_left hb 64
            _ ≤ base ^ e := Nat.pow_le_pow_right (n := base) (by omega) h64
        rw [Nat.min_eq_right hge]
      · rfl

/-- `min a 2^64 < 2^64` says exactly `a < 2^64`. -/
private theorem min_size_lt_iff {a : Nat} :
    (min a UInt64.size < UInt64.size) ↔ a < UInt64.size := by
  constructor
  · intro h
    rw [Nat.min_def] at h
    split at h
    · exact h
    · omega
  · intro h
    rw [Nat.min_eq_left (Nat.le_of_lt h)]
    exact h

/-- The capped loop is below the width exactly when the unbounded power is. -/
private theorem powCapped_lt_iff (base e : Nat) :
    (powCapped base e < UInt64.size) ↔ (base ^ e < UInt64.size) := by
  rw [powCapped_eq, min_size_lt_iff]

/-- The checked power: early decision through `powCapped`. The fault names `**`
with the base and the exponent. -/
def pow (base : CLUint64) (exp : Nat) : Checked CLUint64 :=
  if h : powCapped base.toPlainNat exp < UInt64.size then
    .ok (ofNatLT (base.toPlainNat ^ exp) ((powCapped_lt_iff _ _).mp h))
  else
    .error (ArithFault.range "**" 64 base.toPlainNat exp)

/-- The unbounded power, the definition `pow` is proved against: build
`base ^ exp` unbounded, then run the one range test. -/
def powUnbounded (base : CLUint64) (exp : Nat) : Checked CLUint64 :=
  if h : base.toPlainNat ^ exp < UInt64.size then
    .ok (ofNatLT _ h)
  else
    .error (ArithFault.range "**" 64 base.toPlainNat exp)

/-- The early decision decides the same condition as the unbounded
definition, and both return the same value. Zero bases and `0 ** 0 = 1`
included: the statement is unconditional in the operands. -/
theorem pow_eq_powUnbounded (base : CLUint64) (exp : Nat) :
    base.pow exp = powUnbounded base exp := by
  unfold pow powUnbounded
  simp only [powCapped_eq, min_size_lt_iff]

/-- `base ** exp` succeeds exactly when the unbounded power is in range. -/
theorem pow_ok_iff (base : CLUint64) (exp : Nat) :
    (∃ c, base.pow exp = .ok c) ↔ base.toPlainNat ^ exp < UInt64.size := by
  unfold pow
  split
  · rename_i h
    exact ⟨fun _ => (powCapped_lt_iff _ _).mp h, fun _ => ⟨_, rfl⟩⟩
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd ((powCapped_lt_iff _ _).mpr hn) h⟩
    rcases hc with ⟨c, hc'⟩
    simp at hc'

/-- The checked power returns the unbounded power. -/
theorem pow_value (base : CLUint64) (exp : Nat) (c : CLUint64)
    (hres : base.pow exp = .ok c) : c.toPlainNat = base.toPlainNat ^ exp := by
  unfold pow at hres
  split at hres
  · cases hres
    exact ofNatLT_toPlainNat _ _
  · cases hres

/-- The mixed power: a plain base with a checked exponent, the `2 ** Uint64(64)`
shape of §5.1. The exponent is a checked value, so it is already nonnegative;
the one raise is the result range test, decided early through `powCapped`. -/
def powNatChecked (base : Nat) (exp : CLUint64) : Checked CLUint64 :=
  if h : powCapped base exp.asInt.toNat < UInt64.size then
    .ok (ofNatLT (base ^ exp.asInt.toNat) ((powCapped_lt_iff _ _).mp h))
  else
    .error (ArithFault.range "**" 64 base exp.asInt)

/-- The unbounded mixed power, the definition `powNatChecked` is proved
against. -/
def powNatCheckedUnbounded (base : Nat) (exp : CLUint64) : Checked CLUint64 :=
  if h : base ^ exp.asInt.toNat < UInt64.size then
    .ok (ofNatLT _ h)
  else
    .error (ArithFault.range "**" 64 base exp.asInt)

/-- The early mixed decision decides the unbounded condition. -/
theorem powNatChecked_eq (base : Nat) (exp : CLUint64) :
    powNatChecked base exp = powNatCheckedUnbounded base exp := by
  unfold powNatChecked powNatCheckedUnbounded
  simp only [powCapped_eq, min_size_lt_iff]

/-- The mixed power succeeds exactly when the unbounded power is in range. -/
theorem powNatChecked_ok_iff (base : Nat) (exp : CLUint64) :
    (∃ c, powNatChecked base exp = .ok c) ↔ base ^ exp.asInt.toNat < UInt64.size := by
  unfold powNatChecked
  split
  · rename_i h
    exact ⟨fun _ => (powCapped_lt_iff _ _).mp h, fun _ => ⟨_, rfl⟩⟩
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd ((powCapped_lt_iff _ _).mpr hn) h⟩
    rcases hc with ⟨c, hc'⟩
    simp at hc'

/-- The mixed power returns the unbounded power. -/
theorem powNatChecked_value (base : Nat) (exp : CLUint64) (c : CLUint64)
    (hres : powNatChecked base exp = .ok c) : c.toPlainNat = base ^ exp.asInt.toNat := by
  unfold powNatChecked at hres
  split at hres
  · cases hres
    exact ofNatLT_toPlainNat _ _
  · cases hres

/-- The mixed power with a signed base: a negative base raises on an odd
exponent (the result is negative, never in range) and tests the magnitude on
an even one, so `(-2) ** Uint64(2) = 4` and `(-2) ** Uint64(3)` raises. The
decisions stay early: one parity test and the capped magnitude loop. -/
def powIntChecked (base : Int) (exp : CLUint64) : Checked CLUint64 :=
  if _hneg : base < 0 then
    if _hodd : exp.asInt.toNat % 2 = 1 then
      .error (ArithFault.range "**" 64 base exp.asInt)
    else
      if hm : powCapped base.natAbs exp.asInt.toNat < UInt64.size then
        .ok (ofNatLT (base.natAbs ^ exp.asInt.toNat) ((powCapped_lt_iff _ _).mp hm))
      else
        .error (ArithFault.range "**" 64 base exp.asInt)
  else
    powNatChecked base.toNat exp

/-- The signed-base power succeeds exactly when the unbounded result is in
range: a nonnegative base is `powNatChecked`, a negative base needs an even
exponent and an in-range magnitude. -/
theorem powIntChecked_ok_iff (base : Int) (exp : CLUint64) :
    (∃ c, powIntChecked base exp = .ok c) ↔
      (0 ≤ base ∧ base.toNat ^ exp.asInt.toNat < UInt64.size) ∨
      (base < 0 ∧ exp.asInt.toNat % 2 = 0 ∧ base.natAbs ^ exp.asInt.toNat < UInt64.size) := by
  unfold powIntChecked
  split
  · rename_i hneg
    split
    · rename_i hodd
      refine ⟨fun hc => ?_, fun h => ?_⟩
      · rcases hc with ⟨c, hc'⟩
        simp at hc'
      · exact Or.elim h (fun h1 => absurd h1.1 (by omega))
          (fun h2 => absurd hodd (by omega))
    · rename_i hodd
      split
      · rename_i hm
        refine ⟨fun _ => Or.inr ⟨hneg, (by omega), (powCapped_lt_iff _ _).mp hm⟩,
          fun _ => ⟨_, rfl⟩⟩
      · rename_i hm
        refine ⟨fun hc => ?_, fun h => ?_⟩
        · rcases hc with ⟨c, hc'⟩
          simp at hc'
        · exact Or.elim h (fun h1 => absurd h1.1 (by omega))
            (fun h2 => absurd ((powCapped_lt_iff _ _).mpr h2.2.2) hm)
  · rename_i hneg
    have hge : 0 ≤ base := by omega
    rw [powNatChecked_ok_iff]
    constructor
    · intro hc
      exact Or.inl ⟨hge, hc⟩
    · rintro (⟨_, hc⟩ | ⟨hlt, _, _⟩)
      · exact hc
      · exact absurd hlt (by omega)

/-- The signed-base power returns the unbounded magnitude power: `|base|^exp`,
which reads back the same value for a nonnegative base. -/
theorem powIntChecked_value (base : Int) (exp : CLUint64) (c : CLUint64)
    (hres : powIntChecked base exp = .ok c) :
    c.toPlainNat = base.natAbs ^ exp.asInt.toNat := by
  unfold powIntChecked at hres
  split at hres
  · rename_i hneg
    split at hres
    · simp at hres
    · rename_i hodd
      split at hres
      · cases hres
        exact ofNatLT_toPlainNat _ _
      · simp at hres
  · rename_i hneg
    have hge : 0 ≤ base := by omega
    have habs : base.natAbs = base.toNat :=
      Int.ofNat.inj ((Int.natAbs_of_nonneg hge).trans (Int.toNat_of_nonneg hge).symm)
    rw [habs]
    exact powNatChecked_value base.toNat exp c hres

/-! ## Checked left shift

`a << count` with a `Nat` count: a `Checked` result with an early range
decision (§5.1). The decision never builds `2^count` for `count ≥ 64`: there
the result is `a * 2^count`, in range only for `a = 0`, and the route reads
that off `a` alone. For `count < 64` the factor is at most `2^63`, so the
bound test is cheap. -/

/-- The checked left shift: early decision, no unbounded construction. -/
def lshift (a : CLUint64) (count : Nat) : Checked CLUint64 :=
  if _h : count < 64 then
    if hc : a.toPlainNat * 2 ^ count < UInt64.size then
      .ok (ofNatLT _ hc)
    else
      .error (ArithFault.range "<<" 64 a.toPlainNat count)
  else if _hz : a.toPlainNat = 0 then
    .ok 0
  else
    .error (ArithFault.range "<<" 64 a.toPlainNat count)

/-- The unbounded left shift, the definition `lshift` is proved against. -/
def lshiftUnbounded (a : CLUint64) (count : Nat) : Checked CLUint64 :=
  if h : a.toPlainNat * 2 ^ count < UInt64.size then
    .ok (ofNatLT _ h)
  else
    .error (ArithFault.range "<<" 64 a.toPlainNat count)

/-- A wide count leaves the range exactly when the value is nonzero, the fact
the early branch of `lshift` reads. -/
private theorem mul_pow_ge_size_of_ne_zero {a : Nat} (ha : 0 < a) {count : Nat}
    (h : 64 ≤ count) : UInt64.size ≤ a * 2 ^ count := by
  have h1 : 2 ^ count * 1 ≤ 2 ^ count * a := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_one] at h1
  calc (18446744073709551616 : Nat) = 2 ^ 64 := rfl
    _ ≤ 2 ^ count := Nat.pow_le_pow_right (n := 2) (by decide) h
    _ ≤ a * 2 ^ count := by rw [Nat.mul_comm]; exact h1

/-- A zero value equals the proof-carrying construction of zero. -/
private theorem zero_eq_ofNatLT {n : Nat} (h : n < UInt64.size) (h0 : n = 0) :
    (0 : CLUint64) = ofNatLT n h := by
  subst h0
  rfl

/-- The early decision decides the unbounded condition. -/
theorem lshift_eq (a : CLUint64) (count : Nat) :
    a.lshift count = a.lshiftUnbounded count := by
  unfold lshift lshiftUnbounded
  by_cases h : count < 64
  · rw [dite_eq_left h]
  · by_cases hz : a.toPlainNat = 0
    · have hcond : a.toPlainNat * 2 ^ count < UInt64.size := by
        rw [hz, Nat.zero_mul]
        exact Nat.zero_lt_of_lt (show (0 : Nat) < 18446744073709551616 by decide)
      rw [dite_eq_right h, dite_eq_left hz, dite_eq_left hcond]
      congr 1
      exact zero_eq_ofNatLT hcond (by rw [hz]; exact Nat.zero_mul _)
    · rw [dite_eq_right h, dite_eq_right hz,
        dite_eq_right (fun hc => hz (by
          have hge := mul_pow_ge_size_of_ne_zero (a := a.toPlainNat) (by omega)
            (Nat.not_lt.mp h)
          have hc' : a.toPlainNat * 2 ^ count < UInt64.size := hc
          omega))]

/-- The checked left shift succeeds exactly when the shifted value is in
range: for a count below `64` this is the plain range test, and from `64` on
the early branch reads it off a zero value alone. -/
theorem lshift_ok_iff (a : CLUint64) (count : Nat) :
    (∃ c, a.lshift count = .ok c) ↔ a.toPlainNat * 2 ^ count < UInt64.size := by
  rw [lshift_eq]
  unfold lshiftUnbounded
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd hn h⟩
    rcases hc with ⟨c, hc'⟩
    simp at hc'

/-- The checked left shift returns the shifted value. -/
theorem lshift_value (a : CLUint64) (count : Nat) (c : CLUint64)
    (h : a.lshift count = .ok c) : c.toPlainNat = a.toPlainNat * 2 ^ count := by
  rw [lshift_eq] at h
  unfold lshiftUnbounded at h
  split at h
  · cases h
    exact ofNatLT_toPlainNat _ _
  · cases h

end CLUint64

/-! ## The operator instances

One instance per supported shape, keyed on the operand types, never on a
hidden premise. The total routes return the value; the checked routes return
`Checked CLUint64`. The ordinary divisor routes on two `CLUint64` values stay
`Checked` (`SPEC_ARITHMETIC.md` §4.2). -/

/-- `/` by a `PositiveDivisor`: total, the quotient of the bound dividend. -/
instance : HDiv CLUint64 PositiveDivisor CLUint64 := ⟨CLUint64.divPos⟩

/-- `%` by a `PositiveDivisor`: total, the remainder. -/
instance : HMod CLUint64 PositiveDivisor CLUint64 := ⟨CLUint64.modPos⟩

/-- Same-width `&`: total (§5.1). -/
instance : HAnd CLUint64 CLUint64 CLUint64 := ⟨CLUint64.bitAnd⟩

/-- Same-width `|`: total (§5.1). -/
instance : HOr CLUint64 CLUint64 CLUint64 := ⟨CLUint64.bitOr⟩

/-- Same-width `^`: total (§5.1). -/
instance : HXor CLUint64 CLUint64 CLUint64 := ⟨CLUint64.bitXor⟩

/-- The total right shift: `a >>> count` with a `Nat` count, zero from 64 on. -/
instance : HShiftRight CLUint64 Nat CLUint64 := ⟨CLUint64.rshift⟩

/-- The checked left shift: `a << count` with a `Nat` count. -/
instance : HShiftLeft CLUint64 Nat (Checked CLUint64) := ⟨fun a n => a.lshift n⟩

/-- The checked mixed right shift: a plain left operand with a checked count.
Not total: `(2**64) >>> Uint64(0)` raises (§5.1). -/
instance : HShiftRight Nat CLUint64 (Checked CLUint64) :=
  ⟨fun a b => CLUint64.rshiftChecked a b.asInt⟩

/-- The checked power with a `Nat` exponent: `Uint64(2) ** 64`. -/
instance : HPow CLUint64 Nat (Checked CLUint64) := ⟨fun b e => b.pow e⟩

/-- The checked power with a plain base: `2 ** Uint64(64)` raises. -/
instance : HPow Nat CLUint64 (Checked CLUint64) := ⟨CLUint64.powNatChecked⟩

/-- The checked power with a signed base: `(-2) ** Uint64(2) = 4`,
`(-2) ** Uint64(3)` raises. -/
instance : HPow Int CLUint64 (Checked CLUint64) := ⟨CLUint64.powIntChecked⟩

end EthCLLib.Spec
