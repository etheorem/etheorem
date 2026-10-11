import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement

/-!
# `EthCLLib.TheoremVectors.Scope`: the block-input walk

The scope walk over input types (`THEOREM_VECTORS_ARCHITECTURE.md` §7.4). A type is out of
scope when its constant applications touch one of the binding's block
types, directly or through a structure's fields or a container's element
type; every hit goes in the statement's `blockInputs`, and only the base
source may run on such a theorem (§1.2). A function-typed input is a
separate hit and makes the statement `.unsupported` (§7.4), the fold §7.5
reports as a skip.

The walk is a graph walk over type constants with a seen-set, so a
recursive type cannot loop it. It descends into the type arguments of every
constant application and into the fields of a single-constructor,
non-recursive type, which covers the structures, the `Vector` / `Array` /
`List` wrappers, and the SSZ list and vector wrappers of §7.4 with one rule.

## Lean idioms annotated

- `withReducible (whnf t)` unfolds the fork's `forkabbrev` aliases (`Gwei`,
  `Slot`, and friends are reducible abbrevs of the `UInt64` scalars), so a
  bound that states `slot : Slot` still walks as a scalar. Full `whnf`
  transparency would unfold the spec's definitions, which the scope rule
  never wants.
- `ctorDomains` over a constructor's type exposes the field types as
  bound-variable types; the walk keeps them all, parameters included.
  Walking a parameter's type can only re-reach types the argument walk
  already saw, and the seen-set makes that free.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- What the walk found for one input type (`THEOREM_VECTORS_ARCHITECTURE.md` §7.4). -/
inductive ScopeHit where
  /-- The type is producible as far as the walk can see. -/
  | none
  /-- The type reaches the named block type. -/
  | block (t : Name)
  /-- The type is a function type. -/
  | function

/-- Every `∀` domain of a constructor's type, outermost first. The
domains are the parameters and the fields, left as they come: a domain
under earlier binders carries loose bound variables, and the walk below
handles those without naming them, so the walk creates no free variables
of its own. (`Meta.forallTelescope` here would create real ones, and a
later `whnf` inside the same pass can no longer see them.) -/
private partial def ctorDomains (t : Expr) (acc : Array Expr) : Array Expr :=
  match t with
  | .forallE _ d b _ => ctorDomains b (acc.push d)
  | _ => acc

/-- The block-input walk for one type (`THEOREM_VECTORS_ARCHITECTURE.md` §7.4). The first
hit wins: a `Store` input reports `Store` even though the store's fields
reach blocks and payloads too, because the walk stops at the first block
type it touches. `loose` says the expression may carry loose bound
variables, in which case the walk skips `whnf` and treats any application
whose head is a variable as a leaf. -/
private partial def typeHit (binding : ForkBinding) (seen : NameSet)
    (loose : Bool) (t : Expr) : MetaM ScopeHit := do
  let t ←
    if loose && (t.hasLooseBVars || t.hasFVar) then pure t
    else Meta.withReducible (Meta.whnf t)
  match t with
  -- a function type: `Gwei → Gwei` and every dependent arrow (§7.4)
  | .forallE .. => return .function
  | _ => pure ()
  let loose := loose || t.hasLooseBVars || t.hasFVar
  match t.getAppFn with
  | .const c _ =>
    if binding.blockTypes.contains c then return .block c
    if seen.contains c then return .none
    let seen := seen.insert c
    -- the type arguments: the element type of `Vector` / `Array` / `List`
    -- and of the SSZ list and vector wrappers
    for a in t.getAppArgs do
      match ← typeHit binding seen loose a with
      | .none => pure ()
      | hit => return hit
    -- the fields of a single-constructor, non-recursive type: the
    -- structures and the structure-like wrappers (§7.4)
    let env ← getEnv
    match env.find? c with
    | some (.inductInfo iv) =>
      if iv.isRec || iv.ctors.length != 1 || iv.numIndices != 0 then return .none
      let some (.ctorInfo cv) := env.find? iv.ctors[0]! | return .none
      for ft in ctorDomains cv.type #[] do
        match ← typeHit binding seen true ft with
        | .none => pure ()
        | hit => return hit
      return .none
    | _ => return .none
  | _ => return .none

/-- The scope pass over a statement (§7.4): fill `blockInputs` from the
input-type walk, and fold a function-typed input into an `.unsupported`
shape. The fold keeps an already-unsupported reason, the same rule the
unknown-instance fold in `Statement.readIn` follows. -/
def Scope.classify (binding : ForkBinding) (stmt : Statement) : MetaM Statement := do
  let mut blockInputs : Array Name := #[]
  let mut functionInput : Option Name := none
  for i in stmt.inputs do
    match ← typeHit binding {} false i.type with
    | .none => pure ()
    | .block _ => blockInputs := blockInputs.push i.name
    | .function => if functionInput.isNone then functionInput := some i.name
  let shape :=
    match functionInput with
    | some n =>
      if stmt.shape matches .unsupported _ then stmt.shape
      else .unsupported s!"function-typed input `{n}`"
    | none => stmt.shape
  return { stmt with blockInputs, shape }

end EthCLLib.TheoremVectors
