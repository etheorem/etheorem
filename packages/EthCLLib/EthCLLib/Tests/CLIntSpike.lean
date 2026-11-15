import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Tests.CLIntSpike`: `CLInt`, the pyspec's plain `int`

The pyspec has a second integer kind beside `Uint64`: Python's unbounded, signed `int`
(`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3.1). `CLInt` is that type, a `structure` over `Int`, so core's
Euclidean `/` and `%` do not apply. `+`, `-`, and `*` never raise, so they stay total and
return a plain value. `//` and `%` floor toward minus infinity and raise on a zero divisor,
as Python does.

The module also builds the mixed operand shapes a fork body writes. `int op Uint` computes
as plain `int` and narrows once with `CLInt.toUint64?`, so the result carries the pyspec's
range raise (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §4.2). The `Uint64` side is the in-tree
`EthCLLib.Spec.CLUint64` with its in-tree operators; the spike's private copy of that type
is gone.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLIntSpike

/-- The pyspec plain `int`. A `structure` over `Int`, so core's `/` and `%` do not apply. -/
structure CLInt where
  val : Int
  deriving DecidableEq, Ord

namespace CLInt

instance : Repr CLInt := ⟨fun a _ => repr a.val⟩
instance {n : Nat} : OfNat CLInt n := ⟨⟨n⟩⟩
/-- A Lean `Nat` (a size, a loop variable) enters by coercion. -/
instance : NatCast CLInt := ⟨fun n => ⟨n⟩⟩
instance : Neg CLInt := ⟨fun a => ⟨-a.val⟩⟩
instance : LT CLInt := ⟨fun a b => a.val < b.val⟩
instance : LE CLInt := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : CLInt) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : CLInt) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))

/-! `+`, `-`, `*` never raise, so they stay total and return a plain value. -/

instance : Add CLInt := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub CLInt := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Mul CLInt := ⟨fun a b => ⟨a.val * b.val⟩⟩

/-! `//` and `%` raise on a zero divisor and floor toward minus infinity, as Python does. -/

@[inline] def fdiv (a b : CLInt) : Checked CLInt :=
  if b.val = 0 then .error (.zeroDivisor "//" a.val.natAbs) else .ok ⟨Int.fdiv a.val b.val⟩
@[inline] def fmod (a b : CLInt) : Checked CLInt :=
  if b.val = 0 then .error (.zeroDivisor "%" a.val.natAbs) else .ok ⟨Int.fmod a.val b.val⟩

/-- `len(xs)`. -/
@[inline] def len {α : Type} (xs : Array α) : CLInt := ⟨xs.size⟩

/-- `Uint64(n)`: raises for a negative number and for one past the maximum. -/
@[inline] def toUint64? (n : CLInt) : Checked CLUint64 :=
  if 0 ≤ n.val ∧ n.val < 2 ^ 64 then .ok ⟨UInt64.ofNat n.val.toNat⟩
  else .error (.range "Uint64()" n.val.natAbs 0)

/-- A list position. A negative number raises here; `xs[-1]` is modeled in
`EthCLLib.Tests.CLIndex`. -/
@[inline] def toIndex? (n : CLInt) : Checked Nat :=
  if 0 ≤ n.val then .ok n.val.toNat else .error (.range "index" n.val.natAbs 0)

end CLInt

/-- `int(x)`: always succeeds. Lives in this module's own `CLUint64` namespace: it extends
the in-tree type, it does not add a declaration to `EthCLLib.Spec`. -/
@[inline] def CLUint64.toInt (a : CLUint64) : CLInt := ⟨a.toPlainInt⟩

instance : HDiv CLInt CLInt (Checked CLInt) := ⟨CLInt.fdiv⟩
instance : HMod CLInt CLInt (Checked CLInt) := ⟨CLInt.fmod⟩

/-- A total or partial `int` operator with a `Checked` operand on either side. -/
local macro "lift_int " cls:ident f:term : command => `(
  instance : $cls (Checked CLInt) CLInt (Checked CLInt) := ⟨fun a b => a >>= fun x => $f x b⟩
  instance : $cls CLInt (Checked CLInt) (Checked CLInt) := ⟨fun a b => b >>= fun y => $f a y⟩
  instance : $cls (Checked CLInt) (Checked CLInt) (Checked CLInt) :=
    ⟨fun a b => a >>= fun x => b >>= fun y => $f x y⟩)

lift_int HAdd (fun x y => pure (x + y))
lift_int HSub (fun x y => pure (x - y))
lift_int HMul (fun x y => pure (x * y))
lift_int HDiv CLInt.fdiv
lift_int HMod CLInt.fmod

/-- `int op Uint`: compute as plain `int`, then narrow. The result is a `Uint64`. -/
local macro "mix_int " cls:ident f:term : command => `(
  instance : $cls CLInt CLUint64 (Checked CLUint64) :=
    ⟨fun a b => ($f a (CLUint64.toInt b) : Checked CLInt) >>= CLInt.toUint64?⟩
  instance : $cls CLUint64 CLInt (Checked CLUint64) :=
    ⟨fun a b => ($f (CLUint64.toInt a) b : Checked CLInt) >>= CLInt.toUint64?⟩)

mix_int HAdd (fun x y => pure (x + y))
mix_int HSub (fun x y => pure (x - y))
mix_int HMul (fun x y => pure (x * y))
mix_int HDiv CLInt.fdiv
mix_int HMod CLInt.fmod

/-- A literal divisor has no type of its own: Lean defaults `2` to `Nat` and `-2` to `Int`.
The partial operators therefore also need a `Nat` and an `Int` operand on either side. -/
local macro "lit_int " cls:ident f:term : command => `(
  instance : $cls CLInt Nat (Checked CLInt) := ⟨fun a b => $f a (⟨b⟩ : CLInt)⟩
  instance : $cls Nat CLInt (Checked CLInt) := ⟨fun a b => $f (⟨a⟩ : CLInt) b⟩
  instance : $cls CLInt Int (Checked CLInt) := ⟨fun a b => $f a (⟨b⟩ : CLInt)⟩
  instance : $cls Int CLInt (Checked CLInt) := ⟨fun a b => $f (⟨a⟩ : CLInt) b⟩
  instance : $cls (Checked CLInt) Nat (Checked CLInt) :=
    ⟨fun a b => a >>= fun x => $f x (⟨b⟩ : CLInt)⟩)

lit_int HDiv CLInt.fdiv
lit_int HMod CLInt.fmod
instance : HAdd (Checked CLInt) Nat (Checked CLInt) := ⟨fun a b => a >>= fun x => pure (x + ⟨b⟩)⟩

/-- `Uint` and `int` operands where one side is already a `Checked` expression. -/
local macro "mix_checked " cls:ident f:term : command => `(
  instance : $cls (Checked CLUint64) CLInt (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => ($f (CLUint64.toInt x) b : Checked CLInt) >>= CLInt.toUint64?⟩
  instance : $cls CLInt (Checked CLUint64) (Checked CLUint64) :=
    ⟨fun a b => b >>= fun y => ($f a (CLUint64.toInt y) : Checked CLInt) >>= CLInt.toUint64?⟩
  instance : $cls CLUint64 (Checked CLInt) (Checked CLUint64) :=
    ⟨fun a b => b >>= fun y => ($f (CLUint64.toInt a) y : Checked CLInt) >>= CLInt.toUint64?⟩
  instance : $cls (Checked CLInt) CLUint64 (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => ($f x (CLUint64.toInt b) : Checked CLInt) >>= CLInt.toUint64?⟩
  instance : $cls (Checked CLUint64) (Checked CLInt) (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => b >>= fun y => ($f (CLUint64.toInt x) y : Checked CLInt) >>= CLInt.toUint64?⟩
  instance : $cls (Checked CLInt) (Checked CLUint64) (Checked CLUint64) :=
    ⟨fun a b => a >>= fun x => b >>= fun y => ($f x (CLUint64.toInt y) : Checked CLInt) >>= CLInt.toUint64?⟩)

mix_checked HAdd (fun x y => pure (x + y))
mix_checked HSub (fun x y => pure (x - y))
mix_checked HMul (fun x y => pure (x * y))
mix_checked HDiv CLInt.fdiv
mix_checked HMod CLInt.fmod

/-- The `Uint64` maximum, `2^64 - 1`. A test operand only. -/
def maxValue : CLUint64 := ⟨0xffffffffffffffff⟩

/-! ## The behaviours the pyspec shows -/

-- Subtraction of two plain values never raises: `7 - 9` is `-2`, as in Python.
example : ((7 : CLInt) - 9) = ⟨-2⟩ := rfl
-- `//` and `%` floor toward minus infinity.
example : ((-7 : CLInt) / 2 : Checked CLInt) = .ok ⟨-4⟩ := rfl
example : ((-7 : CLInt) % 2 : Checked CLInt) = .ok ⟨1⟩ := rfl
example : ((7 : CLInt) / -2 : Checked CLInt) = .ok ⟨-4⟩ := rfl
example : ((7 : CLInt) % -2 : Checked CLInt) = .ok ⟨-1⟩ := rfl
-- A zero divisor raises.
example : ((7 : CLInt) / 0 : Checked CLInt) = .error (.zeroDivisor "//" 7) := rfl
-- Total and partial operators mix. One quirk, recorded in the spike README: Lean types a
-- literal-only `10 / 4` as `Nat` division, so the quotient enters the sum unchecked. With the
-- spike's outer `: Checked CLInt` ascription the line does not elaborate; the sum below is a
-- plain `CLInt`, and the value is `8` either way, since `Nat.div 10 4` is also `2`.
example : ((2 : CLInt) * 3 + ((10 / 4 : Nat) : CLInt)) = ⟨8⟩ := rfl
-- A partial operator inside a total one: the sum binds the quotient's `Checked`.
example : ((2 : CLInt) * 3 + ((7 : CLInt) / 2 : Checked CLInt)) = .ok ⟨9⟩ := rfl
example : (CLInt.len #[1, 2, 3] - 5) = ⟨-2⟩ := rfl
-- `Uint64(-2)` raises, and so does a negative index.
example : ((CLInt.len #[1, 2, 3] - 5).toUint64?) = .error (.range "Uint64()" 2 0) := rfl
example : ((CLInt.len #[1, 2, 3] - 5).toIndex?) = .error (.range "index" 2 0) := rfl

/-! ## The operand shapes a fork body writes -/

section
variable (a : CLUint64) (n : CLInt) (k : Nat) (xs : Array Nat)

-- `int op Uint` narrows, so the result is a checked `Uint64`.
example : Checked CLUint64 := n * a
example : Checked CLUint64 := n - a
-- A Lean `Nat` operand coerces into `CLInt`.
example : CLInt := k + n
-- Plain arithmetic stays plain: no bind until the expression divides.
example : CLInt := CLInt.len xs - 1
-- Core `Nat` subtraction floors at zero. A fork body writes `len xs - 1` when it means Python.
example : Nat := xs.size - 1

end

example : ((3 : CLInt) * (5 : CLUint64)) = .ok ⟨15⟩ := rfl
example : ((3 : CLInt) - (5 : CLUint64)) = .error (.range "Uint64()" 2 0) := rfl
-- The mix computes in plain `int` and narrows once, so `0 * maxValue` is `0` and the sum fits.
example : ((0 : CLInt) * maxValue + (7 : CLInt)) = .ok ⟨7⟩ := rfl

end EthCLLib.Tests.CLIntSpike
