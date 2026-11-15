import EthCLLib.Spec.State

/-!
# `EthCLLib.Tests.CLIndex`: indexing with a checked or a plain integer

The pyspec indexes a list with any integer kind, and a plain negative `int` counts from the
end (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §3.7). The `ToIndex` class, the raising
read `getAt`, and every instance (the `CLInt` one arrived with the §5.5 promotion) live in
`EthCLLib.Spec.State`, beside `sszGetIdx`; this module keeps the tests.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.Tests.CLIndex

/-- Core's own bracket forms with a `CLUint64` index: `xs[i]?`, `xs[i]!`, and `xs[i]` with a
proof. -/
instance {α : Type} : GetElem? (Array α) CLUint64 α (fun xs i => i.toPlainInt < xs.size) where
  getElem xs i h := xs[i.toPlainInt]'h
  getElem? xs i := xs[i.toPlainInt]?

/-- A stand-in for the beacon state's validator balances. -/
def balances : Array CLUint64 := #[10, 20, 30]

/-! ## Reads at each integer kind -/

example : balances⟦(1 : CLUint64)⟧ = .ok (CLUint64.trustedOfUInt64 20) := rfl
example : balances⟦(3 : CLUint64)⟧ = .error (.range "index" 0 3) := rfl
-- A plain `-1` counts from the end.
example : balances⟦(-1 : CLInt)⟧ = .ok (CLUint64.trustedOfUInt64 30) := rfl
example : balances⟦(-4 : CLInt)⟧ = .error (.range "index" 0 3) := rfl
example : balances⟦CLInt.len balances - 1⟧ = .ok (CLUint64.trustedOfUInt64 30) := rfl
-- A Lean `Nat` still works.
example : balances⟦(2 : Nat)⟧ = .ok (CLUint64.trustedOfUInt64 30) := rfl
-- Core's optional form.
example : balances[(1 : CLUint64)]? = some (CLUint64.trustedOfUInt64 20) := rfl
-- Core's default form returns the `Inhabited` default instead of raising. The pyspec raises,
-- so `xs[i]!` is forbidden where the read can fail (`packages/EthCLSpecs/docs/SPEC_ARITHMETIC.md` §6). This row only
-- compiles because the in-tree `CLUint64` has `Inhabited`; the spike's private copy had none.
example : balances[(5 : CLUint64)]! = 0 := rfl

/-! ## A read feeds arithmetic -/

/-- A read feeds arithmetic with no conversion: `balances[index] + delta`. -/
def increased (index delta : CLUint64) : Checked CLUint64 := do
  (← balances⟦index⟧) + delta

/-- The same with no `do`: the read is a `Checked` operand like any other. -/
def increased' (index delta : CLUint64) : Checked CLUint64 :=
  balances⟦index⟧ + delta

/-- An index computed from another read: `(xs[-1] + 1) % len(xs)`. -/
def nextCursor : Checked CLUint64 :=
  (balances⟦(-1 : CLInt)⟧ + 1) % CLInt.len balances

example : increased 1 5 = .ok (CLUint64.trustedOfUInt64 25) := rfl
-- The index fault propagates out of the arithmetic.
example : increased' 7 5 = .error (.range "index" 0 3) := rfl
example : nextCursor = .ok (CLUint64.trustedOfUInt64 1) := rfl

end EthCLLib.Tests.CLIndex
