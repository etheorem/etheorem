import EthCLLib.Spec.CLUint

/-!
# `EthCLLib.Spec.CLInt`: the pyspec's plain `int`

The pyspec has a second integer kind beside `Uint64`: Python's unbounded, signed `int`
(`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3.1). `CLInt` is that type, a `structure` over `Int`, so core's
Euclidean `/` and `%` do not apply. `+`, `-`, and `*` never raise, so they stay total and
return a plain value. `//` and `%` floor toward minus infinity and raise on a zero divisor,
as Python does.

The module also builds the mixed operand shapes a fork body writes. `int op Uint` computes
as plain `int` and narrows once with `CLInt.toUint64?`, so the result carries the pyspec's
range raise (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §4.2). The `Uint64` side is the in-tree
`EthCLLib.Spec.CLUint64` with its in-tree operators.

Promoted from `EthCLLib.Tests.CLIntSpike` (§5.5). The behaviour pins stay in the test
module; the `ToIndex CLInt` instance lives beside the class in `Spec/State.lean`.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

/-- The pyspec plain `int`. A `structure` over `Int`, so core's `/` and `%` do not apply. -/
structure CLInt where
  val : Int
  deriving DecidableEq, Ord

namespace CLInt

instance : Repr CLInt := ⟨fun a _ => repr a.val⟩
instance : ToString CLInt := ⟨fun a => toString a.val⟩
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

/-- `max(a, b)` (`SPEC_ARITHMETIC.md` §4.5): the larger operand, never raises. -/
instance : Max CLInt := ⟨fun a b => if a < b then b else a⟩
/-- `min(a, b)` (`SPEC_ARITHMETIC.md` §4.5): the smaller operand, never raises. -/
instance : Min CLInt := ⟨fun a b => if a < b then a else b⟩

/-! `//` and `%` raise on a zero divisor and floor toward minus infinity, as Python does. -/

@[inline] def fdiv (a b : CLInt) : Checked CLInt :=
  if b.val = 0 then .error (.zeroDivisor "//" a.val.natAbs) else .ok ⟨Int.fdiv a.val b.val⟩
@[inline] def fmod (a b : CLInt) : Checked CLInt :=
  if b.val = 0 then .error (.zeroDivisor "%" a.val.natAbs) else .ok ⟨Int.fmod a.val b.val⟩

/-- `len(xs)`. -/
@[inline] def len {α : Type} (xs : Array α) : CLInt := ⟨xs.size⟩

/-- `Uint64(n)`: raises for a negative number and for one past the maximum. -/
@[inline] def toUint64? (n : CLInt) : Checked CLUint64 :=
  if 0 ≤ n.val ∧ n.val < 2 ^ 64 then .ok (CLUint64.trustedOfUInt64 (UInt64.ofNat n.val.toNat))
  else .error (.range "Uint64()" n.val.natAbs 0)

/-- A list position. A negative number raises here; `xs[-1]` is modeled by the `ToIndex
CLInt` instance in `EthCLLib.Spec.State`. -/
@[inline] def toIndex? (n : CLInt) : Checked Nat :=
  if 0 ≤ n.val then .ok n.val.toNat else .error (.range "index" n.val.natAbs 0)

end CLInt

/-- `int(x)`: always succeeds. It extends the in-tree `CLUint64` namespace, the projection
side of the checked kind's one plain route. -/
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

end EthCLLib.Spec
