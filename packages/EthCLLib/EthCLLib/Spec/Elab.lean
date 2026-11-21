import EthCLLib.Spec.CLTotal

/-!
# `EthCLLib.Spec.Elab`: the scoped operator elaborator

Core's operator elaborator (`binop%`) reads the expected type
(`SPEC_ARITHMETIC.md` §4.7). Under `let x ← a * b` in a machine monad that type
is the monad. No operand type compares with a monad, so core fails the step
that types a literal operand, and the result type unifies with the monad in
place of the checked one. The pure-`Checked` contexts need no help: there the
instances themselves return `Checked`, so core picks them through the expected
type.

This module adds one scoped elaborator for the operator trees. It is active
only while `EthCLLib.Spec` is open, so a module that never opens the authoring
namespace elaborates exactly as core does. Its contract, from §4.7:

- **Bounded.** One probe pass and one real pass, no unbounded retry loop.
- **Postpones on unknown operand types.** A lambda binder whose type a later
  argument fixes yields a metavariable type on the probe pass; the elaborator
  postpones instead of letting a literal default.
- **Never changes operand types.** Both passes elaborate the tree with no
  expected type, so each operand keeps its own type and no operand coercion is
  inserted. Only the whole tree's fault travels, through the
  `MonadLift (Except ArithFault) m` instance in `Spec/Checked.lean`.
- **Claims only checked trees.** A tree that does not elaborate to
  `Checked _` is dropped, the state is restored, and core re-elaborates it
  unchanged. Unrelated `Nat`, `Int`, and `UInt64` arithmetic keeps core's
  terms, in this scope and out of it (`Tests/CLCheckedElab.lean` pins both
  scopes).
- **Reports errors at the offending expression.** A tree whose no-expected-type
  pass fails falls through, so core's own diagnostic lands on the expression
  that failed.

The explicit `(expression : Checked _)` ascription stays the supported
fallback everywhere: an ascription fixes the expected type, the instances
match it directly, and the elaborator is never involved.

Two elaboration hazards, and how this elaborator handles them:

- A one-line `← CLUint64.ofNat? x + y` bind with a checked or typed-literal
  `y` elaborates here: the operand matrix carries the
  `HAdd (Checked CLUint64) _ (Checked CLUint64)` rows, the probe pass keeps
  the term, and the lift bridges once. This is what the elaborator accepts. A
  fork body still splits the conversion from the arithmetic that follows it
  (`SPEC_ARITHMETIC.md` §4.3). A *bare* numeral beside a
  `Checked`-typed operand, on EITHER side, does not elaborate, ascription
  included: core's `binop%` types the numeral with the checked operand's type,
  the kernel literal gate rejects that `OfNat`, and no `Nat` retry follows, so
  the error lands on the numeral. The escapes are the §4.3 two-bind form and a
  typed literal.
  Both are pinned in `Tests/CLCheckedElab.lean`.
- A prior do-bound dividend with a non-literal `Nat` divisor
  (`let s ← …; let y ← s % n`) elaborates here the same way. Should a shape
  ever mis-elaborate, the ascription `(s % n : Checked _)` is the escape; it
  forces the expected type and hides nothing.

Historical build measurement, taken on 2026-11-17 with warm SizzLean
dependencies, before any fork body used this elaborator. A cold
`lake build EthCLLib EthCLLibTests` ran 49.7s wall over 303 jobs. The
four-target chain `EthCLLib EthCLLibTests EthCLSpecs EthCLSpecsTests` ran
6m6s wall over 652 jobs, mostly to re-elaborate the fork bodies against the
new barrel entry. A change to this module alone re-elaborated it in 0.8s and
replayed the chain in 1.4s wall over 652 jobs. The figures do not describe
the current fork bodies. Per §4.7, cost is recorded, never a stop
threshold.
-/

set_option autoImplicit false

namespace EthCLLib.Spec

open Lean Elab Term Meta in
/-- The scoped checked-operator elaborator (`SPEC_ARITHMETIC.md` §4.7). See
the module docstring for the contract and the two pinned hazards. -/
@[scoped term_elab binop] def elabCheckedOp : TermElab := fun stx expectedType? => do
  let some expected := expectedType? | throwUnsupportedSyntax
  -- An unresolved whole-tree type (an untyped `let` body) has no information
  -- to offer; core's own path handles it.
  if (← instantiateMVars expected).isMVar then throwUnsupportedSyntax
  let saved ← saveState
  -- Probe pass. If an operand type is still unknown (a lambda binder a later
  -- argument fixes), wait for it: forcing the pass now would let the literal
  -- operand default and lock in the wrong instance.
  let unknown ← try
      let e ← elabTerm stx none
      pure (← instantiateMVars (← inferType e)).hasExprMVar
    catch _ => pure false
  saved.restore
  -- A `postpone` thrown by core inside the probe pass lands in the same
  -- catch and reads as "no unknown operands"; that is safe, because the real
  -- pass fails or falls through and core's own postponement fires with the
  -- expected type, after which the tree re-elaborates with everything known.
  if unknown then tryPostpone
  -- Real pass. Keep the tree only when it is a checked expression; the lift
  -- into the ambient monad is the one conversion this elaborator adds.
  let checked? ← try
      let e ← withSynthesize (elabTerm stx none)
      let ty ← whnfR (← instantiateMVars (← inferType e))
      if ty.isAppOfArity ``Except 2 && (ty.getArg! 0).isConstOf ``ArithFault then
        pure (some e)
      else
        pure none
    catch _ => pure none
  match checked? with
  | some e => ensureHasType expected e
  | none => saved.restore; throwUnsupportedSyntax

end EthCLLib.Spec

