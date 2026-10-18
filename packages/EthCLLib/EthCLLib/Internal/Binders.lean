import Lean

/-!
# `EthCLLib.Internal.Binders`: the shared binder sort

The theorem-vector machinery sorts a theorem's binders into four roles. An
instance binder is a seam: the statement takes an instance of a class, and the
generator command fixes it per preset. A hypothesis is a proposition the
statement assumes, and the record carries it verbatim. A type parameter is a
name the fork binding fixes, such as `{σ : Type}`. An input is a value, and a
searcher produces one.

Two consumers run the sort. The statement reader
(`EthCLLib.TheoremVectors.Statement.readIn`) sorts every binder before it
fills a `Statement`. The manual-terms command sorts a theorem's binders again
to decide which of them a manual term fills. The sort lives here, in one home,
so the two consumers cannot disagree about what an input is. A binder the
reader treats as a value and the command treats as a type would give vectors
the manual terms cannot fill.

The checks run in one order, and the first match wins: binder info, then the
proposition test, then the type-level test.

## Lean idioms annotated on first appearance

* `Meta.withReducible (Meta.whnf type)`: one head reduction at reducible
  transparency. The limit unfolds an `abbrev` and stops there, so the
  type-level question reads the surface type. Plain `whnf` unfolds any
  definition it meets, and the answer would then depend on how far the fork
  body unfolds.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.Internal

/-- The role of one telescope binder in a theorem statement. -/
inductive BinderRole where
  /-- The binder carries `instImplicit` info (the `[...]` form): an instance
  of a class the statement quantifies over, and the generator command binds
  it per preset. -/
  | instance
  /-- The binder's type is a `Prop`: a proposition the statement assumes, and
  the record carries it verbatim. -/
  | hypothesis
  /-- The binder's type is a sort or an arrow into a sort: a name the fork
  binding fixes, such as `{σ : Type}` or `{map : MapKind}`. No searcher can
  produce it. -/
  | typeParameter
  /-- Any other binder: a value the statement consumes, and a searcher
  produces one for it. -/
  | input

/-- Is the binder's type a sort or an arrow into a sort? A binder such as
`{σ : Type}` or `{map : MapKind}` names a type parameter the fork binding
fixes, not a value any searcher could produce; it is neither an instance
nor an input. -/
private def isTypeLevelBinder (type : Expr) : MetaM Bool := do
  let t ← Meta.withReducible (Meta.whnf type)
  let rec peel (e : Expr) : Expr :=
    match e with
    | .forallE _ _ b _ => peel b
    | _ => e
  return (peel t).isSort

/-- Sort one telescope binder into its `BinderRole`. The checks run in the
reader's §7.1 order (`THEOREM_VECTORS_ARCHITECTURE.md`), and the first match
wins: `instImplicit` binder info, then a `Prop` type, then a type-level type.
`Statement.readIn` sorts through this function, and the manual-terms command
sorts through it too. -/
def binderRole (d : LocalDecl) : MetaM BinderRole := do
  if d.binderInfo matches .instImplicit then
    return .instance
  else if ← Meta.isProp d.type then
    return .hypothesis
  else if ← isTypeLevelBinder d.type then
    return .typeParameter
  else
    return .input

end EthCLLib.Internal
