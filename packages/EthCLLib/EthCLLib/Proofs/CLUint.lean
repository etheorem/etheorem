import EthCLLib.Spec.CLInt
import EthCLLib.Spec.CLTotal

/-!
# `EthCLLib.Proofs.CLUint`: the checked-arithmetic law library

The reusable laws every later arithmetic proof consumes
(`SPEC_ARITHMETIC.md` §4.9): success conditions, value lemmas, the `simp_arith`
chain set, the checked-fold law, the conversion round-trips, and the `Checked`
lift laws. Everything here is a kernel proof over the plain `Nat` / `Int`
values (`toPlainNat`), within the axiom trio `propext`, `Classical.choice`,
`Quot.sound`. The audit command is `#print axioms` over each exported
theorem. No `native_decide` appears in a `@[simp]` lemma, and no lemma here
carries a compiler axiom.

An impossible `Except` equation closes by constructor reasoning before any
arithmetic tactic runs (`SPEC_ARITHMETIC.md` §4.9).
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec

/-! ## Small `UInt64` bridges

Four facts the operator laws need to read the native tests on the plain
values. -/

/-- `x = 0` reads the same on the wrapper and on the plain value. -/
private theorem val_eq_zero_iff_toNat_eq_zero (x : UInt64) : x = 0 ↔ x.toNat = 0 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    refine UInt64.toNat_inj.1 ?_
    show x.toNat = (0 : UInt64).toNat
    rw [h]
    rfl

/-- The native inequality test is the decidable inequality. -/
private theorem bne_eq_true {x y : UInt64} (h : (x != y) = true) : x ≠ y := by
  intro he
  rw [he] at h
  simp at h

/-- The native inequality test fires exactly on unequal values. -/
private theorem bne_eq_true_of_ne {x y : UInt64} (h : x ≠ y) : (x != y) = true := by
  show (!(x == y)) = true
  cases hbeq : (x == y) with
  | true => exact absurd (eq_of_beq hbeq) h
  | false => rfl

/-- A nonzero plain value is a nonzero native value. -/
private theorem val_ne_of_toPlainNat_ne {a : CLUint64} (h : a.toPlainNat ≠ 0) :
    a.val ≠ 0 := fun h0 => h (val_eq_zero_iff_toNat_eq_zero a.val |>.mp h0)

/-! ## The `Checked` bind laws

Every chain proof reduces a `do`-bound sequence through these before any
arithmetic fact appears. -/

/-- A bind succeeds with `r` exactly when the left side succeeds with some `a`
and the continuation succeeds with `r` from `a`. -/
theorem bind_ok_iff {α β : Type} {x : Checked α} {f : α → Checked β} {r : β} :
    (x >>= f) = .ok r ↔ ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | ok a =>
    exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, hb, h⟩ => by rw [hb]; exact h⟩
  | error e =>
    refine ⟨fun hc => ?_, fun ⟨_, hb, _⟩ => ?_⟩
    · have hc' : ((Except.error e : Checked α) >>= f) = Except.error e := rfl
      rw [hc'] at hc
      simp at hc
    · simp at hb

/-- The monad laws, stated as examples over `Checked`. -/
example {α β : Type} (a : α) (f : α → Checked β) :
    ((pure a : Checked α) >>= f) = f a := rfl

example {α : Type} (x : Checked α) : (x >>= pure) = x := by cases x <;> rfl

example {α β γ : Type} (x : Checked α) (f : α → Checked β) (g : β → Checked γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by cases x <;> rfl

/-- Bind and map agree. Later chain proofs use this to move a cast across a
bind. -/
theorem bind_pure_map {α β : Type} (x : Checked α) (f : α → β) :
    (x >>= fun a => pure (f a)) = (f <$> x) := by cases x <;> rfl

/-! ## The mixed-route engine

The `Nat` / `CLInt` operand shapes route through `mixBin` and `mixBinDiv`, so
their laws are these plus one `rfl` per shape. -/

/-- `mixBin` computes `f` on the original operands, then runs the one range
test (`SPEC_ARITHMETIC.md` §4.2, no-narrow rule). -/
theorem mixBin_eq_ok (op : String) (f : Int → Int → Int) (a b : Int) (r : CLUint64) :
    CLUint64.mixBin op f a b = .ok r ↔
      0 ≤ f a b ∧ f a b < UInt64.size ∧ r.toPlainNat = (f a b).toNat := by
  simp only [CLUint64.mixBin]
  split
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · cases hc
      exact ⟨h.1, h.2, CLUint64.ofNatLT_toPlainNat _ _⟩
    · obtain ⟨h1, h2, h3⟩ := hn
      have h4 : (f a b).toNat < UInt64.size := by omega
      refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
      show (CLUint64.ofNatLT (f a b).toNat h4).toPlainNat = r.toPlainNat
      rw [CLUint64.ofNatLT_toPlainNat _ _]
      exact h3.symm
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · cases hc
    · obtain ⟨h1, h2, _⟩ := hn
      have h2' : f a b < 18446744073709551616 := h2
      exact absurd ⟨h1, h2'⟩ h

/-- The mixed route returns the plain value of `f`. -/
theorem mixBin_value (op : String) (f : Int → Int → Int) (a b : Int) (c : CLUint64)
    (hres : CLUint64.mixBin op f a b = .ok c) : c.toPlainNat = (f a b).toNat := by
  simp only [CLUint64.mixBin] at hres
  split at hres
  · cases hres
    exact CLUint64.ofNatLT_toPlainNat _ _
  · simp at hres

/-- `mixBin` succeeds exactly when the plain result is in range. -/
theorem mixBin_ok (op : String) (f : Int → Int → Int) (a b : Int) :
    (∃ r, CLUint64.mixBin op f a b = .ok r) ↔ 0 ≤ f a b ∧ f a b < UInt64.size := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨h1, h2, _⟩ := (mixBin_eq_ok op f a b r).mp hr
    exact ⟨h1, h2⟩
  · intro hn
    have h2 : f a b < 18446744073709551616 := hn.2
    refine ⟨CLUint64.ofNatLT (f a b |>.toNat)
      (show (f a b).toNat < 18446744073709551616 from by omega), ?_⟩
    rw [mixBin_eq_ok]
    exact ⟨hn.1, h2, rfl⟩

/-- `mixBinDiv` guards the zero divisor first, then computes as `mixBin`. -/
theorem mixBinDiv_eq_ok (op : String) (f : Int → Int → Int) (a b : Int) (r : CLUint64) :
    CLUint64.mixBinDiv op f a b = .ok r ↔
      b ≠ 0 ∧ 0 ≤ f a b ∧ f a b < UInt64.size ∧ r.toPlainNat = (f a b).toNat := by
  rw [CLUint64.mixBinDiv]
  split
  · rename_i hz
    refine ⟨fun hc => ?_, fun hn => absurd hn.1 (fun hne => hne hz)⟩
    cases hc
  · rename_i hz
    rw [mixBin_eq_ok]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by omega, h1, h2, h3⟩
    · rintro ⟨_, h1, h2, h3⟩
      exact ⟨h1, h2, h3⟩

/-! ## A checked value and a plain `Nat`, as a decision

The pyspec's `slot + 1` and `slot - 1` take the mixed route with a plain `Nat`
right operand. These two laws state that route as a `dite` on the plain range
test, with the exact value and the exact fault in its two branches. A `.run`
equation that states the operation in this form keeps the range test a `Nat`
comparison. The kernel then never reduces the `Int` range test of `mixBin` on
an open operand; that reduction unfolds `Nat.sub` against `2^64` and exhausts
the kernel's recursion depth. -/

/-- The mixed `a + n`: the plain sum when it stays below `2^64`, and the range
fault with the operands otherwise. -/
theorem hadd_un_eq (a : CLUint64) (n : Nat) :
    (a + n : Checked CLUint64) =
      if h : a.toPlainNat + n < UInt64.size then .ok (CLUint64.ofNatLT _ h)
      else .error (ArithFault.range "+" 64 a.asInt n) := by
  -- The instance is `mixAdd`, private to `Spec/CLUint.lean`; unfolding the
  -- instance projection exposes it, and `rfl` unfolds it to `mixBin`.
  have hroute : (a + n : Checked CLUint64) = CLUint64.mixBin "+" (· + ·) a.asInt n := by
    unfold HAdd.hAdd CLUint64.instHAddNatChecked_1
    dsimp only
    rfl
  have hsz : UInt64.size = 18446744073709551616 := rfl
  have hai : a.asInt = (a.toPlainNat : Int) := rfl
  rw [hroute]
  by_cases h : a.toPlainNat + n < UInt64.size
  · rw [dite_eq_left h]
    rw [hsz] at h
    refine (mixBin_eq_ok _ _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · rw [hai]
      omega
    · rw [hai, hsz]
      omega
    · rw [CLUint64.ofNatLT_toPlainNat, hai]
      omega
  · rw [dite_eq_right h]
    unfold CLUint64.mixBin
    rw [dite_eq_right]
    rw [hai]
    rw [hsz] at h
    dsimp only
    omega

/-- The mixed `a - n`: the plain difference when `n ≤ a`, and the range fault
with the operands otherwise. The difference is at most `a`, so it fits. -/
theorem hsub_un_eq (a : CLUint64) (n : Nat) :
    (a - n : Checked CLUint64) =
      if n ≤ a.toPlainNat then
        .ok (CLUint64.ofNatLT (a.toPlainNat - n)
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (UInt64.toNat_lt_size a.val)))
      else .error (ArithFault.range "-" 64 a.asInt n) := by
  -- The instance is `mixSub`, private to `Spec/CLUint.lean`, as in `hadd_un_eq`.
  have hroute : (a - n : Checked CLUint64) = CLUint64.mixBin "-" (· - ·) a.asInt n := by
    unfold HSub.hSub CLUint64.instHSubNatChecked_1
    dsimp only
    rfl
  have hsz : UInt64.size = 18446744073709551616 := rfl
  have hai : a.asInt = (a.toPlainNat : Int) := rfl
  have hlt : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
  rw [hroute]
  by_cases h : n ≤ a.toPlainNat
  · rw [ite_eq_left h]
    refine (mixBin_eq_ok _ _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · rw [hai]
      omega
    · rw [hai, hsz]
      omega
    · rw [CLUint64.ofNatLT_toPlainNat, hai]
      omega
  · rw [ite_eq_right h]
    unfold CLUint64.mixBin
    rw [dite_eq_right]
    rw [hai]
    dsimp only
    omega

/-! ## The five operators on two checked values

Each primitive gets a fused law: the result equals `.ok r` exactly when the
plain `Nat` computation stays in range, and then `r` is the plain result.
These are the rewrite rules of the `simp_arith` chain set. -/

/-- The checked `+` operator computes `CLUint64.add`. -/
theorem hadd_uu_eq (a b : CLUint64) :
    ((a + b : Checked CLUint64)) = CLUint64.add a b := rfl

/-- The checked `-` operator computes `CLUint64.sub`. -/
theorem hsub_uu_eq (a b : CLUint64) :
    ((a - b : Checked CLUint64)) = CLUint64.sub a b := rfl

/-- The checked `*` operator computes `CLUint64.mul`. -/
theorem hmul_uu_eq (a b : CLUint64) :
    ((a * b : Checked CLUint64)) = CLUint64.mul a b := rfl

/-- The checked `/` operator computes `CLUint64.div`. -/
theorem hdiv_uu_eq (a b : CLUint64) :
    ((a / b : Checked CLUint64)) = CLUint64.div a b := rfl

/-- The checked `%` operator computes `CLUint64.mod`. -/
theorem hmod_uu_eq (a b : CLUint64) :
    ((a % b : Checked CLUint64)) = CLUint64.mod a b := rfl

/-- Checked addition: the sum raises exactly past `2^64 - 1`, and then the
value is the plain sum. -/
theorem add_eq_ok (a b r : CLUint64) :
    CLUint64.add a b = .ok r ↔
      a.toPlainNat + b.toPlainNat < UInt64.size ∧
      r.toPlainNat = a.toPlainNat + b.toPlainNat := by
  have ha : a.val.toNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
  have hb : b.val.toNat < 18446744073709551616 := UInt64.toNat_lt_size b.val
  have hac : a.toPlainNat = a.val.toNat := rfl
  have hbc : b.toPlainNat = b.val.toNat := rfl
  simp only [CLUint64.add, UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
  split
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd
      (show a.toPlainNat + b.toPlainNat < 18446744073709551616 from hn.1) (by omega)⟩
    cases hc
  · refine ⟨fun hc => ?_, fun hn => ?_⟩
    · have hpos : a.val.toNat + b.val.toNat < 18446744073709551616 := by omega
      have hv : r.toPlainNat = (a.val + b.val).toNat := by
        rw [← Except.ok.inj hc]
        rfl
      refine ⟨hpos, ?_⟩
      show r.toPlainNat = a.toPlainNat + b.toPlainNat
      rw [hv, UInt64.toNat_add]
      omega
    · obtain ⟨h1, h2⟩ := hn
      have h1' : a.toPlainNat + b.toPlainNat < 18446744073709551616 := h1
      refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
      show (a.val + b.val).toNat = r.toPlainNat
      rw [UInt64.toNat_add]
      omega

/-- Checked subtraction: raises below zero; the `Nat` value floors at zero. -/
theorem sub_eq_ok (a b r : CLUint64) :
    CLUint64.sub a b = .ok r ↔
      b.toPlainNat ≤ a.toPlainNat ∧
      r.toPlainNat = a.toPlainNat - b.toPlainNat := by
  have ha : a.val.toNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
  have hac : a.toPlainNat = a.val.toNat := rfl
  have hbc : b.toPlainNat = b.val.toNat := rfl
  simp only [CLUint64.sub, UInt64.lt_iff_toNat_lt]
  split
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd
      (show b.toPlainNat ≤ a.toPlainNat from hn.1) (by omega)⟩
    cases hc
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · have hv : r.toPlainNat = (a.val - b.val).toNat := by
        rw [← Except.ok.inj hc]
        rfl
      refine ⟨Nat.le_of_not_gt h, ?_⟩
      show r.toPlainNat = a.toPlainNat - b.toPlainNat
      rw [hv, UInt64.toNat_sub]
      omega
    · obtain ⟨h1, h2⟩ := hn
      have h1' : b.val ≤ a.val := h1
      have hac : a.toPlainNat = a.val.toNat := rfl
      have hbc : b.toPlainNat = b.val.toNat := rfl
      refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
      show (a.val - b.val).toNat = r.toPlainNat
      rw [UInt64.toNat_sub_of_le a.val b.val h1']
      omega

/-- The divide-back test of `mul` reads on the plain values: with a nonzero
divisor, the wrapped product fails to divide back exactly when the product
left the range. -/
private theorem mul_nat_test (a b : Nat) (ha : 0 < a) :
    ((a * b) % 18446744073709551616 / a = b) ↔ a * b < 18446744073709551616 := by
  constructor
  · intro h
    have hmod : (a * b) % 18446744073709551616 < 18446744073709551616 :=
      Nat.mod_lt _ (by omega)
    have hge : b * a ≤ (a * b) % 18446744073709551616 :=
      (Nat.le_div_iff_mul_le (by omega)).1 (by rw [h]; exact Nat.le_refl b)
    rw [Nat.mul_comm] at hge
    have hdm : a * b =
        18446744073709551616 * ((a * b) / 18446744073709551616) +
          (a * b) % 18446744073709551616 :=
      (Nat.div_add_mod (a * b) 18446744073709551616).symm
    omega
  · intro h
    have hdm : a * b =
        18446744073709551616 * ((a * b) / 18446744073709551616) +
          (a * b) % 18446744073709551616 :=
      (Nat.div_add_mod (a * b) 18446744073709551616).symm
    have hmod : (a * b) % 18446744073709551616 = a * b := by omega
    rw [hmod, Nat.mul_div_cancel_left _ (by omega)]

/-- Checked multiplication: raises past `2^64 - 1` through the divide-back
test, and then the value is the plain product. -/
theorem mul_eq_ok (a b r : CLUint64) :
    CLUint64.mul a b = .ok r ↔
      a.toPlainNat * b.toPlainNat < UInt64.size ∧
      r.toPlainNat = a.toPlainNat * b.toPlainNat := by
  have hac : a.toPlainNat = a.val.toNat := rfl
  have hbc : b.toPlainNat = b.val.toNat := rfl
  have htest : ((a.val != 0 && (a.val * b.val / a.val != b.val)) = true) ↔
      a.val.toNat ≠ 0 ∧
        (a.val.toNat * b.val.toNat) % 18446744073709551616 / a.val.toNat ≠
          b.val.toNat := by
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun heq => bne_eq_true h1 (val_eq_zero_iff_toNat_eq_zero a.val |>.mpr heq),
        fun heq => bne_eq_true h2 (UInt64.toNat_inj.1 ?_)⟩
      rw [UInt64.toNat_div, UInt64.toNat_mul,
        show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]
      exact heq
    · rintro ⟨h1, h2⟩
      refine ⟨bne_eq_true_of_ne (val_ne_of_toPlainNat_ne h1),
        bne_eq_true_of_ne (x := a.val * b.val / a.val) (y := b.val) (fun heq => h2 (by
          have ht := UInt64.toNat_inj.2 heq
          rw [UInt64.toNat_div, UInt64.toNat_mul,
            show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at ht
          exact ht))⟩
  have hiff : (a.val.toNat ≠ 0 ∧
      (a.val.toNat * b.val.toNat) % 18446744073709551616 / a.val.toNat ≠
        b.val.toNat) ↔
      ¬(a.val.toNat * b.val.toNat < 18446744073709551616) := by
    constructor
    · rintro ⟨h1, h2⟩ hn
      exact h2 ((mul_nat_test a.val.toNat b.val.toNat
        (Nat.pos_of_ne_zero h1)).mpr hn)
    · intro h
      rcases Nat.eq_zero_or_pos a.val.toNat with h0 | hp
      · exfalso
        rw [h0] at h
        simp at h
      · exact ⟨Nat.ne_of_gt hp, fun he => h ((mul_nat_test a.val.toNat b.val.toNat
          hp).mp he)⟩
  simp only [CLUint64.mul, htest, hiff]
  split
  · rename_i h
    rw [← hac, ← hbc] at h
    refine ⟨fun hc => ?_, fun hn => absurd
      (show a.toPlainNat * b.toPlainNat < 18446744073709551616 from hn.1) h⟩
    cases hc
  · refine ⟨fun hc => ?_, fun hn => ?_⟩
    · have hprod : a.val.toNat * b.val.toNat < 18446744073709551616 := by omega
      have hv : r.toPlainNat = (a.val * b.val).toNat := by
        rw [← Except.ok.inj hc]
        rfl
      refine ⟨hprod, ?_⟩
      show r.toPlainNat = a.toPlainNat * b.toPlainNat
      rw [hv, UInt64.toNat_mul,
        show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
        show a.toPlainNat = a.val.toNat from rfl,
        show b.toPlainNat = b.val.toNat from rfl]
      omega
    · obtain ⟨h1, h2⟩ := hn
      have h1' : a.val.toNat * b.val.toNat < 18446744073709551616 := by
        rw [← hac, ← hbc]
        exact h1
      refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
      show (a.val * b.val).toNat = r.toPlainNat
      rw [UInt64.toNat_mul,
        show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
        show r.toPlainNat = a.val.toNat * b.val.toNat from by
          rw [← hac, ← hbc]
          exact h2]
      omega

/-- Checked division: the only raise is the zero divisor, and the value is the
plain quotient. -/
theorem div_eq_ok (a b r : CLUint64) :
    CLUint64.div a b = .ok r ↔
      b.toPlainNat ≠ 0 ∧ r.toPlainNat = a.toPlainNat / b.toPlainNat := by
  simp only [CLUint64.div]
  split
  · rename_i hz
    have hb0 : b.val = 0 := eq_of_beq hz
    refine ⟨fun hc => ?_, fun hn => absurd
      (show b.toPlainNat = 0 from by
        rw [show b.toPlainNat = b.val.toNat from rfl, hb0]; rfl) hn.1⟩
    cases hc
  · rename_i hz
    have hbne : b.val ≠ 0 := fun h0 => hz (by rw [h0]; rfl)
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · have hv : r.toPlainNat = (a.val / b.val).toNat := by
        rw [← Except.ok.inj hc]
        rfl
      refine ⟨fun h0 => hbne (val_eq_zero_iff_toNat_eq_zero _ |>.2 h0), ?_⟩
      show r.toPlainNat = a.toPlainNat / b.toPlainNat
      rw [hv, UInt64.toNat_div]
      rfl
    · obtain ⟨_, h2⟩ := hn
      refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
      show (a.val / b.val).toNat = r.toPlainNat
      rw [show r.toPlainNat = a.toPlainNat / b.toPlainNat from h2,
        show a.toPlainNat = a.val.toNat from rfl,
        show b.toPlainNat = b.val.toNat from rfl,
        UInt64.toNat_div]

/-- Checked modulo: the only raise is the zero divisor, and the value is the
plain remainder. -/
theorem mod_eq_ok (a b r : CLUint64) :
    CLUint64.mod a b = .ok r ↔
      b.toPlainNat ≠ 0 ∧ r.toPlainNat = a.toPlainNat % b.toPlainNat := by
  simp only [CLUint64.mod]
  split
  · rename_i hz
    have hb0 : b.val = 0 := eq_of_beq hz
    refine ⟨fun hc => ?_, fun hn => absurd
      (show b.toPlainNat = 0 from by
        rw [show b.toPlainNat = b.val.toNat from rfl, hb0]; rfl) hn.1⟩
    cases hc
  · rename_i hz
    have hbne : b.val ≠ 0 := fun h0 => hz (by rw [h0]; rfl)
    refine ⟨fun hc => ?_, fun hn => ?_⟩
    · have hv : r.toPlainNat = (a.val % b.val).toNat := by
        rw [← Except.ok.inj hc]
        rfl
      refine ⟨fun h0 => hbne (val_eq_zero_iff_toNat_eq_zero _ |>.2 h0), ?_⟩
      show r.toPlainNat = a.toPlainNat % b.toPlainNat
      rw [hv, UInt64.toNat_mod]
      rfl
    · obtain ⟨_, h2⟩ := hn
      refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
      show (a.val % b.val).toNat = r.toPlainNat
      rw [show r.toPlainNat = a.toPlainNat % b.toPlainNat from h2,
        show a.toPlainNat = a.val.toNat from rfl,
        show b.toPlainNat = b.val.toNat from rfl,
        UInt64.toNat_mod]

/-! ## Success and value, per primitive

The `∃`-form success condition and the separate value law, derived from the
fused rules. The total routes of `Spec/CLTotal.lean` carry their value laws
there; the checked power and left shift carry success and value there too. -/

/-- Success of `+`. -/
theorem add_ok_iff (a b : CLUint64) :
    (∃ r, CLUint64.add a b = .ok r) ↔ a.toPlainNat + b.toPlainNat < UInt64.size := by
  constructor
  · rintro ⟨r, hr⟩
    exact (add_eq_ok a b r).mp hr |>.1
  · intro hn
    refine ⟨CLUint64.ofNatLT (a.toPlainNat + b.toPlainNat)
      (show a.toPlainNat + b.toPlainNat < UInt64.size from hn), ?_⟩
    exact add_eq_ok a b _ |>.mpr ⟨hn, CLUint64.ofNatLT_toPlainNat _ _⟩

/-- The value of a successful `+`. -/
theorem add_value (a b r : CLUint64) (h : CLUint64.add a b = .ok r) :
    r.toPlainNat = a.toPlainNat + b.toPlainNat :=
  (add_eq_ok a b r).mp h |>.2

/-- Success of `-`. -/
theorem sub_ok_iff (a b : CLUint64) :
    (∃ r, CLUint64.sub a b = .ok r) ↔ b.toPlainNat ≤ a.toPlainNat := by
  constructor
  · rintro ⟨r, hr⟩
    exact (sub_eq_ok a b r).mp hr |>.1
  · intro hn
    have ha : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
    refine ⟨CLUint64.ofNatLT (a.toPlainNat - b.toPlainNat)
      (show a.toPlainNat - b.toPlainNat < 18446744073709551616 from by omega), ?_⟩
    exact sub_eq_ok a b _ |>.mpr ⟨hn, CLUint64.ofNatLT_toPlainNat _ _⟩

/-- The value of a successful `-`. -/
theorem sub_value (a b r : CLUint64) (h : CLUint64.sub a b = .ok r) :
    r.toPlainNat = a.toPlainNat - b.toPlainNat :=
  (sub_eq_ok a b r).mp h |>.2

/-- Success of `*`. -/
theorem mul_ok_iff (a b : CLUint64) :
    (∃ r, CLUint64.mul a b = .ok r) ↔ a.toPlainNat * b.toPlainNat < UInt64.size := by
  constructor
  · rintro ⟨r, hr⟩
    exact (mul_eq_ok a b r).mp hr |>.1
  · intro hn
    refine ⟨CLUint64.ofNatLT (a.toPlainNat * b.toPlainNat)
      (show a.toPlainNat * b.toPlainNat < UInt64.size from hn), ?_⟩
    exact mul_eq_ok a b _ |>.mpr ⟨hn, CLUint64.ofNatLT_toPlainNat _ _⟩

/-- The value of a successful `*`. -/
theorem mul_value (a b r : CLUint64) (h : CLUint64.mul a b = .ok r) :
    r.toPlainNat = a.toPlainNat * b.toPlainNat :=
  (mul_eq_ok a b r).mp h |>.2

/-- Success of `/`: the divisor is nonzero. -/
theorem div_ok_iff (a b : CLUint64) :
    (∃ r, CLUint64.div a b = .ok r) ↔ b.toPlainNat ≠ 0 := by
  constructor
  · rintro ⟨r, hr⟩
    exact (div_eq_ok a b r).mp hr |>.1
  · intro hn
    have ha : a.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size a.val
    have hd : a.toPlainNat / b.toPlainNat ≤ a.toPlainNat := Nat.div_le_self _ _
    refine ⟨CLUint64.ofNatLT (a.toPlainNat / b.toPlainNat)
      (show a.toPlainNat / b.toPlainNat < 18446744073709551616 from by omega), ?_⟩
    exact div_eq_ok a b _ |>.mpr ⟨hn, CLUint64.ofNatLT_toPlainNat _ _⟩

/-- The value of a successful `/`. -/
theorem div_value (a b r : CLUint64) (h : CLUint64.div a b = .ok r) :
    r.toPlainNat = a.toPlainNat / b.toPlainNat :=
  (div_eq_ok a b r).mp h |>.2

/-- Success of `%`: the divisor is nonzero. -/
theorem mod_ok_iff (a b : CLUint64) :
    (∃ r, CLUint64.mod a b = .ok r) ↔ b.toPlainNat ≠ 0 := by
  constructor
  · rintro ⟨r, hr⟩
    exact (mod_eq_ok a b r).mp hr |>.1
  · intro hn
    have hb : b.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size b.val
    have hm : a.toPlainNat % b.toPlainNat < b.toPlainNat := Nat.mod_lt _ (by omega)
    refine ⟨CLUint64.ofNatLT (a.toPlainNat % b.toPlainNat)
      (show a.toPlainNat % b.toPlainNat < 18446744073709551616 from by omega), ?_⟩
    exact mod_eq_ok a b _ |>.mpr ⟨hn, CLUint64.ofNatLT_toPlainNat _ _⟩

/-- The value of a successful `%`. -/
theorem mod_value (a b r : CLUint64) (h : CLUint64.mod a b = .ok r) :
    r.toPlainNat = a.toPlainNat % b.toPlainNat :=
  (mod_eq_ok a b r).mp h |>.2

/-! ## The total selectors

`max` picks an operand and never raises (`SPEC_ARITHMETIC.md` §4.5), so its
value is the plain maximum. -/

/-- `max a b` is one of the operands, so its value is the plain maximum. -/
theorem max_value (a b : CLUint64) :
    (max a b).toPlainNat = max a.toPlainNat b.toPlainNat := by
  show (if a < b then b else a).toPlainNat = max a.toPlainNat b.toPlainNat
  split
  · next h =>
    have hlt : a.toPlainNat < b.toPlainNat := h
    rw [Nat.max_eq_right (Nat.le_of_lt hlt)]
  · next h =>
    have hge : b.toPlainNat ≤ a.toPlainNat := by
      have h' : ¬ (a.toPlainNat < b.toPlainNat) := h
      omega
    rw [Nat.max_eq_left hge]

/-! ## The chain simp set

`simp_arith` is one `simp only` call over the fused rules, the bind law, and
the `∃`-normalization rules. It reduces a checked chain of up to three
operations in one step to `Nat` facts under right-nested `∃` binders
(`SPEC_ARITHMETIC.md` §4.9): each checked link of the chain contributes one
binder and its range test. The binder order is what the pins below state,
and the depth-3 pin is the form Stage 4 chain and fold proofs should
expect, so one `simp_arith` call closes. Keep the set focused: only lemmas
of this file belong in it. -/

/-- The `Checked` left operand binds before the addition computes. -/
theorem hadd_checkedL_eq (x : Checked CLUint64) (b : CLUint64) :
    ((x + b : Checked CLUint64)) = (x >>= fun m => CLUint64.add m b) := rfl

/-- The `Checked` left operand binds before the subtraction computes. -/
theorem hsub_checkedL_eq (x : Checked CLUint64) (b : CLUint64) :
    ((x - b : Checked CLUint64)) = (x >>= fun m => CLUint64.sub m b) := rfl

/-- The `Checked` left operand binds before the multiplication computes. -/
theorem hmul_checkedL_eq (x : Checked CLUint64) (b : CLUint64) :
    ((x * b : Checked CLUint64)) = (x >>= fun m => CLUint64.mul m b) := rfl

/-- The `Checked` left operand binds before the division computes. -/
theorem hdiv_checkedL_eq (x : Checked CLUint64) (b : CLUint64) :
    ((x / b : Checked CLUint64)) = (x >>= fun m => CLUint64.div m b) := rfl

/-- The `Checked` left operand binds before the modulo computes. -/
theorem hmod_checkedL_eq (x : Checked CLUint64) (b : CLUint64) :
    ((x % b : Checked CLUint64)) = (x >>= fun m => CLUint64.mod m b) := rfl

/-- The `Checked` right operand binds before the addition computes. -/
theorem hadd_checkedR_eq (a : CLUint64) (x : Checked CLUint64) :
    ((a + x : Checked CLUint64)) = (x >>= fun m => CLUint64.add a m) := rfl

/-- The `Checked` right operand binds before the subtraction computes. -/
theorem hsub_checkedR_eq (a : CLUint64) (x : Checked CLUint64) :
    ((a - x : Checked CLUint64)) = (x >>= fun m => CLUint64.sub a m) := rfl

/-- The `Checked` right operand binds before the multiplication computes. -/
theorem hmul_checkedR_eq (a : CLUint64) (x : Checked CLUint64) :
    ((a * x : Checked CLUint64)) = (x >>= fun m => CLUint64.mul a m) := rfl

/-- The `Checked` right operand binds before the division computes. -/
theorem hdiv_checkedR_eq (a : CLUint64) (x : Checked CLUint64) :
    ((a / x : Checked CLUint64)) = (x >>= fun m => CLUint64.div a m) := rfl

/-- The `Checked` right operand binds before the modulo computes. -/
theorem hmod_checkedR_eq (a : CLUint64) (x : Checked CLUint64) :
    ((a % x : Checked CLUint64)) = (x >>= fun m => CLUint64.mod a m) := rfl

/-- Two `Checked` operands bind left first, then right. -/
theorem hadd_checkedBoth_eq (x y : Checked CLUint64) :
    ((x + y : Checked CLUint64)) =
      (x >>= fun a => y >>= fun b => CLUint64.add a b) := rfl

/-- Two `Checked` operands bind left first, then right. -/
theorem hsub_checkedBoth_eq (x y : Checked CLUint64) :
    ((x - y : Checked CLUint64)) =
      (x >>= fun a => y >>= fun b => CLUint64.sub a b) := rfl

/-- Two `Checked` operands bind left first, then right. -/
theorem hmul_checkedBoth_eq (x y : Checked CLUint64) :
    ((x * y : Checked CLUint64)) =
      (x >>= fun a => y >>= fun b => CLUint64.mul a b) := rfl

/-- Two `Checked` operands bind left first, then right. -/
theorem hdiv_checkedBoth_eq (x y : Checked CLUint64) :
    ((x / y : Checked CLUint64)) =
      (x >>= fun a => y >>= fun b => CLUint64.div a b) := rfl

/-- Two `Checked` operands bind left first, then right. -/
theorem hmod_checkedBoth_eq (x y : Checked CLUint64) :
    ((x % y : Checked CLUint64)) =
      (x >>= fun a => y >>= fun b => CLUint64.mod a b) := rfl

/-- The `∃`-normalization the chain reduction leaves: `bind_ok_iff` puts a
new binder inside a conjunct of the previous one, and these two rules pull
each binder level with the outer one, left or right side. With them, one
`simp_arith` call closes a depth-3 chain; without them, a reassociated `∃`
survives after the arithmetic reduces. -/
theorem exists_pull_left {α β : Type} {p : α → β → Prop} {q : α → Prop} :
    (∃ x, (∃ y, p x y) ∧ q x) ↔ ∃ x y, p x y ∧ q x := by
  constructor
  · rintro ⟨x, ⟨y, hpxy⟩, hqx⟩
    exact ⟨x, y, hpxy, hqx⟩
  · rintro ⟨x, y, hpxy, hqx⟩
    exact ⟨x, ⟨y, hpxy⟩, hqx⟩

/-- The right-side form: the new binder sits in the right conjunct. -/
theorem exists_pull_right {α β : Type} {p : α → Prop} {q : α → β → Prop} :
    (∃ x, p x ∧ ∃ y, q x y) ↔ ∃ x y, p x ∧ q x y := by
  constructor
  · rintro ⟨x, hpx, ⟨y, hqxy⟩⟩
    exact ⟨x, y, hpx, hqxy⟩
  · rintro ⟨x, y, hpx, hqxy⟩
    exact ⟨x, hpx, ⟨y, hqxy⟩⟩

/-- One `simp_arith` reduces a checked chain to its `Nat` facts. -/
scoped macro "simp_arith" : tactic =>
  `(tactic| simp only [bind_ok_iff, exists_pull_left, exists_pull_right,
    hadd_checkedL_eq, hsub_checkedL_eq,
    hmul_checkedL_eq, hdiv_checkedL_eq, hmod_checkedL_eq,
    hadd_checkedR_eq, hsub_checkedR_eq, hmul_checkedR_eq, hdiv_checkedR_eq,
    hmod_checkedR_eq, hadd_checkedBoth_eq, hsub_checkedBoth_eq,
    hmul_checkedBoth_eq, hdiv_checkedBoth_eq, hmod_checkedBoth_eq,
    hadd_uu_eq, hsub_uu_eq, hmul_uu_eq, hdiv_uu_eq, hmod_uu_eq,
    add_eq_ok, sub_eq_ok, mul_eq_ok, div_eq_ok, mod_eq_ok])

/-- The chain pin: one `simp_arith` call exposes both `Nat` facts of
`a * b / c`, the product's range test and the divisor. -/
example (a b c r : CLUint64) :
    ((a * b / c : Checked CLUint64)) = .ok r ↔
      ∃ m : CLUint64, (a.toPlainNat * b.toPlainNat < UInt64.size ∧
        m.toPlainNat = a.toPlainNat * b.toPlainNat) ∧
        c.toPlainNat ≠ 0 ∧
        r.toPlainNat = m.toPlainNat / c.toPlainNat := by
  simp_arith

/-- The same one call exposes both range tests of an addition chain. -/
example (a b c r : CLUint64) :
    ((a + b + c : Checked CLUint64)) = .ok r ↔
      ∃ m : CLUint64, (a.toPlainNat + b.toPlainNat < UInt64.size ∧
        m.toPlainNat = a.toPlainNat + b.toPlainNat) ∧
        m.toPlainNat + c.toPlainNat < UInt64.size ∧
        r.toPlainNat = m.toPlainNat + c.toPlainNat := by
  simp_arith

/-- A checked divisor binds before the division computes, the shape the
reward formula's `rewardNumerator / (activeIncrements * weightDenominator)`
uses. -/
example (a b c r : CLUint64) :
    ((a / (b * c) : Checked CLUint64)) = .ok r ↔
      ∃ m : CLUint64, (b.toPlainNat * c.toPlainNat < UInt64.size ∧
        m.toPlainNat = b.toPlainNat * c.toPlainNat) ∧
        m.toPlainNat ≠ 0 ∧
        r.toPlainNat = a.toPlainNat / m.toPlainNat := by
  simp_arith

/-- Two checked subtotals expose both of their range tests, under the
normalized binders. -/
example (a b c d r : CLUint64) :
    (((a + b : Checked CLUint64) + (c + d : Checked CLUint64)) = .ok r) ↔
      ∃ m n : CLUint64,
        (a.toPlainNat + b.toPlainNat < UInt64.size ∧
          m.toPlainNat = a.toPlainNat + b.toPlainNat) ∧
        (c.toPlainNat + d.toPlainNat < UInt64.size ∧
          n.toPlainNat = c.toPlainNat + d.toPlainNat) ∧
        m.toPlainNat + n.toPlainNat < UInt64.size ∧
        r.toPlainNat = m.toPlainNat + n.toPlainNat := by
  simp_arith

/-- The depth-3 pin: one call closes a three-operation chain. One binder
per checked link; the last link's intermediate is the outer binder. -/
example (a b c d r : CLUint64) :
    (((a * b / c : Checked CLUint64) / d) = .ok r) ↔
      ∃ m n : CLUint64,
        ((a.toPlainNat * b.toPlainNat < UInt64.size ∧
            n.toPlainNat = a.toPlainNat * b.toPlainNat) ∧
          c.toPlainNat ≠ 0 ∧
          m.toPlainNat = n.toPlainNat / c.toPlainNat) ∧
        d.toPlainNat ≠ 0 ∧
        r.toPlainNat = m.toPlainNat / d.toPlainNat := by
  simp_arith

/-! ## The checked fold

`sum(xs)` over checked values is `xs.foldlM (fun acc x => acc + x) 0`
(`SPEC_ARITHMETIC.md` §4.5). It succeeds exactly when every running sum stays
in range, which is the law Stage 4's total-balance folds reuse. -/

/-- The running value after `i` steps of the checked addition fold. -/
def runSum (start : CLUint64) (xs : List CLUint64) (i : Nat) : Nat :=
  start.toPlainNat + ((xs.take i).map (fun x => x.toPlainNat)).sum

/-- The checked addition fold succeeds exactly when every running sum is in
range. -/
theorem foldlM_add_ok_iff (start : CLUint64) (xs : List CLUint64) :
    (∃ c, xs.foldlM (fun acc x => acc + x) start = .ok c) ↔
      ∀ i ≤ xs.length, runSum start xs i < UInt64.size := by
  induction xs generalizing start with
  | nil =>
    constructor
    · rintro ⟨c, hc⟩
      cases hc
      intro i _
      show start.toPlainNat + ((([] : List CLUint64).take i).map
        (fun x : CLUint64 => x.toPlainNat)).sum < 18446744073709551616
      have hnil : (([] : List CLUint64).take i).map
          (fun x : CLUint64 => x.toPlainNat) = [] := by
        cases i <;> rfl
      rw [hnil]
      simp only [List.sum_nil]
      have hs : start.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size start.val
      omega
    · exact fun _ => ⟨start, rfl⟩
  | cons x xs ih =>
    have hx : start.toPlainNat < 18446744073709551616 := UInt64.toNat_lt_size start.val
    -- One fold step, stated in beta-normal form: add the head, then continue.
    have hcons : (x :: xs).foldlM (fun acc y => acc + y) start
        = ((start + x : Checked CLUint64) >>= fun m =>
          xs.foldlM (fun acc y => acc + y) m) := by
      show List.foldlM (fun acc y => acc + y) start (x :: xs) = _
      rw [List.foldlM_cons]
    constructor
    · rintro ⟨c, hc⟩
      rw [hcons, bind_ok_iff] at hc
      obtain ⟨m, hmx, hrest⟩ := hc
      have hrest' := (ih m).mp ⟨c, hrest⟩
      rintro i hi
      rw [List.length_cons] at hi
      cases i with
      | zero =>
        show start.toPlainNat + (((x :: xs).take 0).map
          (fun y : CLUint64 => y.toPlainNat)).sum < 18446744073709551616
        rw [List.take_zero, List.map_nil, List.sum_nil]
        omega
      | succ i =>
        obtain ⟨h1, h2⟩ := add_eq_ok start x m |>.mp hmx
        have hci : m.toPlainNat + ((xs.take i).map
            (fun y : CLUint64 => y.toPlainNat)).sum < 18446744073709551616 :=
          hrest' i (by omega)
        show start.toPlainNat + (((x :: xs).take (i + 1)).map
          (fun y : CLUint64 => y.toPlainNat)).sum < 18446744073709551616
        rw [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
    · intro h
      have h1 : start.toPlainNat + x.toPlainNat < 18446744073709551616 := by
        have h1' : start.toPlainNat + (((x :: xs).take 1).map
            (fun y : CLUint64 => y.toPlainNat)).sum < 18446744073709551616 :=
          h 1 (by rw [List.length_cons]; omega)
        rw [List.take_succ_cons, List.map_cons, List.sum_cons, List.take_zero,
          List.map_nil, List.sum_nil] at h1'
        simpa using h1'
      have hW : ∀ i ≤ xs.length,
          runSum (CLUint64.ofNatLT (start.toPlainNat + x.toPlainNat) h1) xs i <
            UInt64.size := by
        intro i hi
        cases i with
        | zero =>
          show (CLUint64.ofNatLT (start.toPlainNat + x.toPlainNat) h1).toPlainNat +
            ((xs.take 0).map (fun y : CLUint64 => y.toPlainNat)).sum <
            18446744073709551616
          rw [CLUint64.ofNatLT_toPlainNat, List.take_zero, List.map_nil, List.sum_nil]
          omega
        | succ i =>
          have hstep' : start.toPlainNat + (((x :: xs).take (i + 2)).map
              (fun y : CLUint64 => y.toPlainNat)).sum < 18446744073709551616 :=
            h (i + 2) (by rw [List.length_cons]; omega)
          show (CLUint64.ofNatLT (start.toPlainNat + x.toPlainNat) h1).toPlainNat +
            ((xs.take (i + 1)).map (fun y : CLUint64 => y.toPlainNat)).sum <
            18446744073709551616
          rw [List.take_succ_cons, List.map_cons, List.sum_cons] at hstep'
          rw [CLUint64.ofNatLT_toPlainNat]
          omega
      obtain ⟨c, hc⟩ := (ih _).mpr hW
      refine ⟨c, ?_⟩
      rw [hcons, bind_ok_iff]
      exact ⟨CLUint64.ofNatLT (start.toPlainNat + x.toPlainNat) h1,
        add_eq_ok _ _ _ |>.mpr ⟨h1, CLUint64.ofNatLT_toPlainNat _ _⟩, hc⟩

/-- The checked addition fold returns the final running sum. -/
theorem foldlM_add_value (start : CLUint64) (xs : List CLUint64) (c : CLUint64)
    (h : xs.foldlM (fun acc x => acc + x) start = .ok c) :
    c.toPlainNat = runSum start xs xs.length := by
  induction xs generalizing start c with
  | nil =>
    cases h
    rfl
  | cons x xs ih =>
    -- One fold step, stated in beta-normal form: add the head, then continue.
    have hcons : (x :: xs).foldlM (fun acc y => acc + y) start
        = ((start + x : Checked CLUint64) >>= fun m =>
          xs.foldlM (fun acc y => acc + y) m) := by
      show List.foldlM (fun acc y => acc + y) start (x :: xs) = _
      rw [List.foldlM_cons]
    rw [hcons, bind_ok_iff] at h
    obtain ⟨m, hmx, hrest⟩ := h
    have hrest' : xs.foldlM (fun acc y => acc + y) m = .ok c := hrest
    obtain ⟨h1, h2⟩ := add_eq_ok start x m |>.mp hmx
    rw [ih m c hrest']
    show m.toPlainNat + ((xs.take xs.length).map
      (fun y : CLUint64 => y.toPlainNat)).sum =
      start.toPlainNat + (((x :: xs).take (x :: xs).length).map
      (fun y : CLUint64 => y.toPlainNat)).sum
    rw [List.length_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
    omega

/-! ## Conversions

Round-trips and value laws for the checked narrowings
(`SPEC_ARITHMETIC.md` §4.5). -/

/-- `ofNat?` succeeds exactly in range. -/
theorem ofNat_ok_iff (n : Nat) :
    (∃ v, CLUint64.ofNat? n = .ok v) ↔ n < UInt64.size := by
  rw [CLUint64.ofNat?]
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd hn h⟩
    rcases hc with ⟨v, hv⟩
    simp at hv

/-- A successful `ofNat?` returns the exact value. -/
theorem ofNat_value (n : Nat) (v : CLUint64) (h : CLUint64.ofNat? n = .ok v) :
    v.toPlainNat = n := by
  rw [CLUint64.ofNat?] at h
  split at h
  · cases h
    exact CLUint64.ofNatLT_toPlainNat _ _
  · simp at h

/-- `ofNat?` round-trips an in-range value. -/
theorem ofNat_roundtrip (v : CLUint64) :
    CLUint64.ofNat? v.toPlainNat = .ok v := by
  have hv : v.toPlainNat < UInt64.size := UInt64.toNat_lt_size v.val
  rw [CLUint64.ofNat?_ok v.toPlainNat hv]
  refine congrArg Except.ok (CLUint64.val_inj (UInt64.toNat_inj.1 ?_))
  show (CLUint64.ofNatLT v.toPlainNat hv).toPlainNat = v.toPlainNat
  rw [CLUint64.ofNatLT_toPlainNat]

/-- `ofInt?` succeeds exactly on `[0, 2^64)`. -/
theorem ofInt_ok_iff (n : Int) :
    (∃ v, CLUint64.ofInt? n = .ok v) ↔ 0 ≤ n ∧ n < 18446744073709551616 := by
  rw [CLUint64.ofInt?]
  split
  · rename_i h
    refine ⟨fun _ => h, fun hn => ⟨CLUint64.ofNatLT n.toNat ?_, ?_⟩⟩
    · have h2 := hn.2
      show n.toNat < 18446744073709551616
      omega
    · rfl
  · rename_i h
    refine ⟨fun hc => ?_, fun hn => absurd hn h⟩
    rcases hc with ⟨v, hv⟩
    simp at hv

/-- A successful `ofInt?` returns the exact value. -/
theorem ofInt_value (n : Int) (v : CLUint64) (h : CLUint64.ofInt? n = .ok v) :
    v.toPlainNat = n.toNat := by
  rw [CLUint64.ofInt?] at h
  split at h
  · cases h
    exact CLUint64.ofNatLT_toPlainNat _ _
  · simp at h

/-- The checked narrowing round-trips a checked value
(`Spec/CLInt.lean` proves it; restated here for one import). -/
theorem toCLInt_toCLUint64_roundtrip (a : CLUint64) :
    a.toCLInt.toCLUint64? = .ok a := CLUint64.toCLInt_toCLUint64? a

/-- `ofCLInt?` is the namespace-qualified narrowing. -/
theorem ofCLInt_eq (v : CLInt) : CLUint64.ofCLInt? v = v.toCLUint64? := rfl

/-- `saturatingSub` reads back as the truncating `Nat` difference
(`Spec/CLUint.lean` proves it beside the definition). -/
theorem saturatingSub_value (a b : CLUint64) :
    (a.saturatingSub b).toPlainNat = a.toPlainNat - b.toPlainNat :=
  CLUint64.saturatingSub_toPlainNat a b

/-! ## The mixed `&` with a complement

`a & ~f` (`Spec/CLInt.lean`): `~f` is the plain `int` `-f - 1`, so the `&` is the
mixed route with its range test. A nonnegative `a` keeps the result inside
`[0, a]`, so the test never fires, and the value is the same-width `&` with the
64-bit complement of `f`. Proofs about a bit mask (`convert_validator_index_to_builder_index`)
rewrite through this law, then reason on the native words. -/

/-- `a & ~f` succeeds, with the same-width `&` of `a` and the 64-bit complement of
`f`. -/
theorem hand_invert_eq (a f : CLUint64) :
    (a &&& f.invert : Checked CLUint64) =
      .ok (a &&& CLUint64.trustedOfUInt64 (~~~ f.val)) := by
  -- Bit by bit: `x ∧ ¬y = x ⊕ (x ∧ y)`, a kernel proof with no `bv_decide` certificate.
  have key : a.val &&& ~~~ f.val = a.val ^^^ (a.val &&& f.val) := by
    apply UInt64.eq_of_toBitVec_eq
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, UInt64.toBitVec_not]
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not]
    cases a.val.toBitVec[i] <;> cases f.val.toBitVec[i] <;> rfl
  have hval : CLInt.landInt (a.toPlainNat : Int) (Int.negSucc f.toPlainNat)
      = ((a.val &&& ~~~ f.val).toNat : Int) := by
    rw [key, UInt64.toNat_xor, UInt64.toNat_and]
    rfl
  have hlt := UInt64.toNat_lt_size (a.val &&& ~~~ f.val)
  rw [CLUint64.hand_clInt_eq]
  show CLUint64.mixBin "&" CLInt.landInt (a.toPlainNat : Int) (Int.negSucc f.toPlainNat) = _
  rw [mixBin_eq_ok, hval]
  refine ⟨by omega, by omega, ?_⟩
  show (a.val &&& ~~~ f.val).toNat = _
  omega

end EthCLLib.Proofs
