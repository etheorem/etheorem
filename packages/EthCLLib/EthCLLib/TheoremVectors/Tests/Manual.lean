import EthCLLib.Internal.ManualTerms
import EthCLLib.Tests.InheritanceReplay

/-!
# `EthCLLib.TheoremVectors.Tests.Manual`: the `theorem_vectors_manual` pins

Build-gate checks for the manual-terms command over the toy fork
`EthCLLib.Tests.InheritanceReplay.Base`, whose proof namespace by the
repository layout is `EthCLLib.Proofs.Base`:

- the ledger holds the `(theorem, input, holder)` triples the three
  registrations spell, in registration and clause order; the registrations
  cover a typed `let`, an untyped `let`, an ascribed assignment, and an
  untyped assignment;
- each holder's type is its input's type over the theorem's instance
  binders: the instance-free holders are plain `Nat`s, and the
  instance-binder holder is `∀ [Inhabited Nat], Nat`;
- a holder is compiled code: `native_decide` walks the same compiled-code
  path the probe's `evalExpr` uses, and a holder that was never compiled
  fails there. The pins decide the shared-`let` value and the shared-`let`
  expression.

The error paths are pinned the way `Tests/Command.lean` pins its own: an
unknown label, one input filled twice, a duplicate registration, an input
whose type depends on an earlier input, a lets-only registration, and an
ascription mismatch.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs.Base

/-- The instance-free control: two inputs, one filled through a shared
`let`, one through a shared-`let` expression. -/
theorem toyManualAdd (n : Nat) (m : Nat) : n + m = m + n := Nat.add_comm n m

/-- The instance-binder control: the holder for `n` must take the
`[Inhabited Nat]` binder. -/
theorem toyManualInst [Inhabited Nat] (n : Nat) : n = n := rfl

/-- The clause-rule control: the registration below fills it through an
untyped `let` and an ascribed assignment. -/
theorem toyManualTwo (a : Nat) (b : Nat) : a + b = b + a := Nat.add_comm a b

/-- The unknown-label fixture. -/
theorem toyUnknownLabel (n : Nat) : n = n := rfl

/-- The filled-twice fixture. -/
theorem toyFillTwice (n : Nat) : n = n := rfl

/-- The dependent-input fixture: `v`'s type mentions the earlier input
`n`, so no holder over the instance binders alone could exist. -/
theorem toyDep (n : Nat) (v : Fin n) : v = v := rfl

/-- The ascription fixture. -/
theorem toyAscribed (n : Nat) : n = n := rfl

/-- The lets-only fixture. -/
theorem toyLetsOnly (n : Nat) : n = n := rfl

open EthCLLib.Internal in
theorem_vectors_manual toyManualAdd
  let k : Nat :=
    1
  n := k
  m := k + 1

open EthCLLib.Internal in
theorem_vectors_manual toyManualInst
  n := 3

open EthCLLib.Internal in
theorem_vectors_manual toyManualTwo
  let k := 7
  a : Nat := k + 1
  b := k * 2

end EthCLLib.Proofs.Base

namespace EthCLLib.TheoremVectors.Tests.Manual

-- the ledger holds exactly the triples the three registrations spelled. A
-- holder constant lives under the module's private prefix, so the expected
-- name is the public-shaped one through `mkPrivateName`.
open Lean in
run_cmd do
  let env ← getEnv
  let got := EthCLLib.Internal.manualTermsOf env
  let holder (n : Name) : Name := mkPrivateName env n
  let want : Array (Name × Name × Name) :=
    #[(`EthCLLib.Proofs.Base.toyManualAdd, `n,
        holder `EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualAdd.n),
      (`EthCLLib.Proofs.Base.toyManualAdd, `m,
        holder `EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualAdd.m),
      (`EthCLLib.Proofs.Base.toyManualInst, `n,
        holder `EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualInst.n),
      (`EthCLLib.Proofs.Base.toyManualTwo, `a,
        holder `EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualTwo.a),
      (`EthCLLib.Proofs.Base.toyManualTwo, `b,
        holder `EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualTwo.b)]
  unless got == want do
    throwError s!"the manual-terms ledger holds {got}, expected {want}"

-- each holder's type is its input's type over the instance binders; the
-- private constants resolve by ident inside their own module
example : Nat :=
  EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualAdd.n

example : Nat :=
  EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualAdd.m

example : ∀ [Inhabited Nat], Nat :=
  EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualInst.n

example : Nat :=
  EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualTwo.a

example : Nat :=
  EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualTwo.b

-- a holder is compiled code: the `n` holder is its `let` value, the `m`
-- holder its `let` expression
example : EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualAdd.n = 1 :=
  by native_decide

example : EthCLLib.Proofs.Base.TheoremVectorsManual.toyManualAdd.m = 2 :=
  by native_decide

-- An unknown label errors at its clause, with the theorem's input list.
/-- error: `theorem_vectors_manual`: `m` does not name an input of `EthCLLib.Proofs.Base.toyUnknownLabel`. The theorem's inputs are `n`. -/
#guard_msgs (error) in
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.toyUnknownLabel
  m := 1

-- One input filled twice errors at the second clause.
/-- error: `theorem_vectors_manual` fills `n` twice in `EthCLLib.Proofs.Base.toyFillTwice`'s registration; one assignment per input. -/
#guard_msgs (error) in
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.toyFillTwice
  n := 1
  n := 2

-- A second registration for one theorem errors.
/-- error: `theorem_vectors_manual` already registered witness terms for `EthCLLib.Proofs.Base.toyManualAdd`; one registration per theorem. -/
#guard_msgs (error) in
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.toyManualAdd
  n := 1

-- An input whose type mentions an earlier input errors at its clause.
/-- error: `theorem_vectors_manual`: `v`'s type in `EthCLLib.Proofs.Base.toyDep` mentions a binder a holder cannot take. An input's type may depend on the instance binders alone, so no holder over them could exist for a type parameter or an earlier input. -/
#guard_msgs (error) in
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.toyDep
  v := 0

-- A lets-only registration errors.
/-- error: `theorem_vectors_manual` registered no assignments for `EthCLLib.Proofs.Base.toyLetsOnly`; spell at least one input's clause, or drop the command. -/
#guard_msgs (error) in
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.toyLetsOnly
  let k := 1

-- An ascription that mismatches its input's type errors at the ascription.
/-- error: `theorem_vectors_manual`: the ascription `Int` does not match `n`'s type in `EthCLLib.Proofs.Base.toyAscribed`. -/
#guard_msgs (error) in
open EthCLLib.Internal in
theorem_vectors_manual EthCLLib.Proofs.Base.toyAscribed
  n : Int := 1

end EthCLLib.TheoremVectors.Tests.Manual
