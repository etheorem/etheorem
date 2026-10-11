import Lean
import EthCLLib.TheoremVectors.Statement

/-!
# `EthCLLib.TheoremVectors.Prepare`: the prepare pass

The prepare pass turns a `Statement` into the array of search problems the
sources solve (`THEOREM_VECTORS_ARCHITECTURE.md` §8). Stage 2 carries the pass's
first form (the plan's stage 2, step 1): one `Case` per theorem, holding the
conjunction of its hypotheses, plus the `Decidable` synthesis of §8.4. The
`simp only` unfold (§8.1), the DNF split with its cap (§8.2), and the
`.iffTrue` sides (§8.3) arrive in stage 3.

Every source ends with `decide` on its candidate, so every case must carry a
`Decidable` instance for its conjunction (§8.4). The pass synthesizes it once,
at build time, over the statement's binders, and stores it beside the
conjunction; the probe substitutes the instance binders into it (§11.2). A
case whose synthesis fails is reported and dropped (§8.4).

## Lean idioms annotated

- `Meta.synthInstance` runs ordinary instance search on a `Prop` goal. It
  returns a term that may mention the statement's instance binders, which is
  why the pass, the probe, and everything downstream run inside the reader's
  telescope scope (`Statement.readIn`).
- `mkAnd` builds the conjunction right-associated, so the `Decidable` chain
  reads outermost-first, the binder order.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- One search problem: a conjunction of hypotheses over the inputs
(`THEOREM_VECTORS_ARCHITECTURE.md` §5.4). The prepare pass produces one per DNF disjunct,
times two for `.iffTrue`; stage 2 produces one per theorem. The conjunction
and its `Decidable` instance ride beside the conjuncts so the probe does not
re-derive either (§8.4). -/
structure Case where
  /-- The case's position, which names its record directory (§12.1). -/
  index : Nat
  /-- The `.iffTrue` side this case serves, when the shape is `.iffTrue`
  (§8.3). -/
  side  : Option Bool
  /-- The conjuncts, in binder order, binders still free. -/
  hyps  : Array Expr
  /-- The conjunction of `hyps`, as one `Prop`. -/
  conj  : Expr
  /-- The `Decidable` instance of `conj` (§8.4). -/
  decidable : Expr
  deriving Inhabited

/-- The right-associated conjunction of the hypotheses, `True` for none. -/
private def conjunction (hyps : Array Expr) : Expr :=
  hyps.foldr (fun h acc => mkApp2 (.const ``And []) h acc) (.const ``True [])

/-- The pass's stage-2 form: one case per theorem, the conjunction of its
hypotheses with its `Decidable` instance synthesized (§8.4). Returns the
cases and the reasons of the cases dropped for failed synthesis. The unfold
(§8.1) and split (§8.2) arrive in stage 3. -/
def Prepare.pass (stmt : Statement) : MetaM (Array Case × Array String) := do
  let conj := conjunction stmt.hyps
  match ← (try some <$> Meta.synthInstance (mkApp (.const ``Decidable []) conj)
    catch _ => pure none) with
  | none =>
    -- §8.4: a case whose synthesis fails is reported and dropped
    return (#[], #[s!"no `Decidable` instance for the hypothesis \
      conjunction ({stmt.hyps.size} conjunct(s))"])
  | some dec =>
    return (#[{ index := 0, side := none, hyps := stmt.hyps, conj,
                decidable := dec }], #[])

end EthCLLib.TheoremVectors
