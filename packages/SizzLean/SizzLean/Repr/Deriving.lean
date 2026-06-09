import Lean
import SizzLean.Repr.Class
import SizzLean.Repr.Instances

/-!
# `SizzLean.Repr.Deriving`: `deriving SSZRepr` handler

The user-surface deriving handler so that

```lean
structure Foo where
  a : Bool
  b : Bool
  deriving SSZRepr
```

emits an `instance : SSZRepr Foo` with no manual work. The handler
walks the structure's fields, looks up each field type's `SSZRepr`
instance (so the field type must itself derive, or carry, an
`SSZRepr` instance), assembles the matching `SSZType.container`
shape, and emits the iso plus `rfl` proofs.

## What a deriving handler is

Lean's `deriving Cls` after a declaration asks the compiler to
synthesise a `Cls` instance automatically. The compiler looks up
a *deriving handler* for `Cls`, a function registered ahead of
time that takes the just-elaborated type's name and returns the
elaborated `instance` declaration. For `Repr`, `DecidableEq`,
etc., the handlers ship with Lean core; for user-defined
classes like `SSZRepr` the handler ships with the class. This
file is that handler.

The handler runs at *elaboration* time (after parsing, before
typechecking the generated code), using Lean's metaprogramming
API (`MetaM`, `TermElabM`, `CommandElabM`). It produces a
`Syntax` tree that is then re-fed through normal elaboration,
so anything the handler emits is typechecked exactly as if a
user had written it by hand.

## Implementation strategy

This is the only metaprogramming in the project. ARCHITECTURE.md §5.2
names Lean core's `src/Lean/Elab/Deriving/Repr.lean` and
`src/Lean/Elab/Deriving/FromToJson.lean` as templates; the path
here is lighter-weight because (a) only *structures* are
handled (not general inductives), and (b) no `mutual`-block
generation is needed. The handler emits exactly one `instance`
command per derived type.

The emitted instance has the following shape, where `Foo` has
fields `a₁ : T₁, ..., aₙ : Tₙ`:

```lean
instance : SSZRepr Foo where
  shape    := .container [SSZRepr.shape (T := T₁), …, SSZRepr.shape (T := Tₙ)]
  toRepr   := fun (s : Foo) => (s.a₁, …, s.aₙ, PUnit.unit)
  fromRepr := fun ⟨v₁, …, vₙ, _⟩ => { a₁ := v₁, …, aₙ := vₙ }
  to_from  := fun _ => rfl
  from_to  := fun r => by rcases r with ⟨…⟩; rfl
```

The `to_from` proof is `rfl` because `fromRepr ∘ toRepr` rebuilds
the structure component-wise, so Lean's structure eta sees the result
as the original. `from_to` requires `rcases` to destructure the
right-nested `Prod` chain (terminating in `PUnit`) so the kernel
can apply `PUnit`'s singleton-eta.

## Lean metaprogramming idioms used here (annotated on first appearance)

* `registerDerivingHandler : Name → (Array Name → CommandElabM Bool) → IO Unit`:
  the entry point Lean's `deriving` machinery calls when it sees
  `deriving SSZRepr` after a `structure`/`inductive` declaration.
* `getStructureFields : Environment → Name → Array Name`: the list
  of fields a `structure` declares, in declaration order.
* `getStructureFieldInfo? : Environment → Name → Name → Option StructureFieldInfo`:
  per-field metadata including the projection function name.
* `Lean.Elab.Term.exprToSyntax : Expr → TermElabM Syntax`: turns
  an `Expr` (e.g. a field's type extracted from the projection
  function's signature) into something the macro-template antiquotation
  `$...` can splice into a generated `Syntax` tree.
* `forallTelescopeReducing`: strips off pi-binders from a type,
  exposing the body and the bound variables. Used here to peek
  at a projection function's return type (= the field's type).
-/

set_option autoImplicit false

namespace SizzLean.Repr.Deriving

open SizzLean.Repr

open Lean Elab Command Meta Term

/-- Map a Lean type to its literal `SSZType` shape Syntax.

Hardcoded pattern matching on the recognised primitive and composite
constructors (`Bool`, `UInt8/16/32/64`, `BitVec n`, `Vector α n`).
For non-recognised types, falls back to typeclass synthesis + `whnf`
reduction of the resulting `SSZRepr.shape` projection: this lets
the handler recursively support any user type with a pre-existing
`SSZRepr` instance (including struct-of-struct fields).

Using `whnf` rather than `Meta.reduceAll` is deliberate: the
latter has been observed to produce metavariables in the output
on the same input, presumably because it reduces too aggressively.
`whnf` stops at weak-head normal form, and with `@[reducible]` on
`interp` / `interpFields` reduces instance projections cleanly.

`fieldType` is `whnf`'d at entry so `abbrev` newtypes (e.g.
`abbrev Slot := UInt64`) expand to their underlying type before
pattern matching. -/
private partial def shapeForType (fieldTypeOrig : Expr) : TermElabM (TSyntax `term) := do
  -- First check the *pre-whnf* form for named SSZ-collection abbrevs
  -- and structures (`Bitlist`, `Bitvector`, `SSZList`): their
  -- abbrev/structure heads carry the cap/size argument we need to
  -- splice into the emitted shape, and `whnf` would unfold them to
  -- `Subtype`/`BitVec` and lose that head.
  if fieldTypeOrig.isAppOfArity ``SizzLean.Repr.Bitlist 1 then
    let n := fieldTypeOrig.appArg!
    let some nVal ← Lean.Meta.evalNat (← Lean.Meta.whnf n) |>.run
      | throwError "deriving SSZRepr: cannot evaluate Bitlist cap '{n}' to a Nat literal"
    let nSyn : TSyntax `term := Syntax.mkNumLit (toString nVal)
    return ← `(SizzLean.Spec.SSZType.bitlist $nSyn)
  if fieldTypeOrig.isAppOfArity ``SizzLean.Repr.Bitvector 1 then
    let n := fieldTypeOrig.appArg!
    let some nVal ← Lean.Meta.evalNat (← Lean.Meta.whnf n) |>.run
      | throwError "deriving SSZRepr: cannot evaluate Bitvector length '{n}' to a Nat literal"
    let nSyn : TSyntax `term := Syntax.mkNumLit (toString nVal)
    return ← `(SizzLean.Spec.SSZType.bitvector $nSyn)
  if fieldTypeOrig.isAppOfArity ``SizzLean.Repr.SSZList 2 then
    -- `SSZList α cap`: recurse on `α`, splice the literal `cap`.
    let cap := fieldTypeOrig.appArg!
    let α := fieldTypeOrig.appFn!.appArg!
    let αShape ← shapeForType α
    let some capVal ← Lean.Meta.evalNat (← Lean.Meta.whnf cap) |>.run
      | throwError "deriving SSZRepr: cannot evaluate SSZList cap '{cap}' to a Nat literal"
    let capSyn : TSyntax `term := Syntax.mkNumLit (toString capVal)
    return ← `(SizzLean.Spec.SSZType.list $αShape $capSyn)
  -- Otherwise reduce via `whnf` for abbrev newtypes (`Slot = UInt64`)
  -- and proceed with the primitive pattern checks.
  let fieldType ← Lean.instantiateMVars (← Lean.Meta.whnf fieldTypeOrig)
  if fieldType.isConstOf ``Bool then
    `(SizzLean.Spec.SSZType.bool)
  else if fieldType.isConstOf ``UInt8 then
    `(SizzLean.Spec.SSZType.uintN 8)
  else if fieldType.isConstOf ``UInt16 then
    `(SizzLean.Spec.SSZType.uintN 16)
  else if fieldType.isConstOf ``UInt32 then
    `(SizzLean.Spec.SSZType.uintN 32)
  else if fieldType.isConstOf ``UInt64 then
    `(SizzLean.Spec.SSZType.uintN 64)
  else if fieldType.isAppOfArity ``BitVec 1 then
    -- `BitVec n` → `.uintN n`. `n` is a `Nat`-level expression; we
    -- extract its numeric value via `evalNat` (rather than going
    -- through `exprToSyntax`, which would round-trip
    -- `OfNat.ofNat 256 _` and leave the instance argument as a
    -- metavariable in the emitted syntax).
    let n := fieldType.appArg!
    let some nVal ← Lean.Meta.evalNat (← Lean.Meta.whnf n) |>.run
      | throwError "deriving SSZRepr: cannot evaluate BitVec width '{n}' to a literal Nat"
    let nSyn : TSyntax `term := Syntax.mkNumLit (toString nVal)
    `(SizzLean.Spec.SSZType.uintN $nSyn)
  else if fieldType.isAppOfArity ``Vector 2 then
    -- `Vector α n` → `.vector (shape α) n`. Recurse on `α`; extract
    -- the literal `n` value the same way as the `BitVec` arm.
    let n := fieldType.appArg!
    let α := fieldType.appFn!.appArg!
    let αShape ← shapeForType α
    let some nVal ← Lean.Meta.evalNat (← Lean.Meta.whnf n) |>.run
      | throwError "deriving SSZRepr: cannot evaluate Vector length '{n}' to a literal Nat"
    let nSyn : TSyntax `term := Syntax.mkNumLit (toString nVal)
    `(SizzLean.Spec.SSZType.vector $αShape $nSyn)
  else
    -- Fallback: try synthesising a `SSZRepr` instance for `fieldType`
    -- and project + reduce the `shape`. Works for user structures
    -- that have themselves been `deriving SSZRepr`'d.
    -- Fallback uses the *original*, unreduced field type so
    -- `abbrev`-defined types like `Bitlist cap` keep their named
    -- form for the instance lookup and the emitted syntax.
    let sszReprClass ← mkAppM ``SizzLean.SSZRepr #[fieldTypeOrig]
    match ← Lean.Meta.synthInstance? sszReprClass with
    | some _ =>
        let tySyn : TSyntax `term ← match fieldTypeOrig with
          | .const name _ => pure ⟨mkIdent name⟩
          | _             => exprToSyntax fieldTypeOrig
        `(@SizzLean.SSZRepr.shape $tySyn inferInstance)
    | none =>
        throwError "deriving SSZRepr: field type '{fieldTypeOrig}' is not directly recognised by the handler and has no `SSZRepr` instance in scope. Supported directly: Bool, UInt8/16/32/64, BitVec n, Vector α n. Other types must derive (or hand-write) their own `SSZRepr` instance first."

/-- For each field of `declName`, return a pair: the literal `SSZType`
shape Syntax (for the emitted `shape` field) and the field's Lean
type Syntax (for the `fromRepr` input-type annotation). -/
private def getFieldShapesAndTypes (declName : Name) :
    TermElabM (Array (TSyntax `term) × Array (TSyntax `term)) := do
  let env ← getEnv
  let fieldNames := getStructureFields env declName
  let mut shapes : Array (TSyntax `term) := #[]
  let mut types  : Array (TSyntax `term) := #[]
  for fname in fieldNames do
    let some info := getFieldInfo? env declName fname
      | throwError "deriving SSZRepr: cannot find field info for {fname}"
    let projInfo ← getConstInfo info.projFn
    let fieldType ← forallTelescopeReducing projInfo.type fun _ body => pure body
    types := types.push (← exprToSyntax fieldType)
    shapes := shapes.push (← shapeForType fieldType)
  return (shapes, types)

/-- Build the `instance` command for `SSZRepr declName`. -/
private def mkInstance (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env declName do
    throwError "deriving SSZRepr: '{declName}' is not a structure (only structures are supported)"
  let fieldNames := getStructureFields env declName
  if fieldNames.isEmpty then
    throwError "deriving SSZRepr: '{declName}' has no fields"
  -- Compute each field's `SSZType` shape via typeclass synthesis,
  -- and also extract the field's Lean type for the input-type
  -- annotation on `fromRepr`. See `getFieldShapesAndTypes`'s
  -- docstring for the dual role.
  let (shapeExprs, fieldTypes) ← liftTermElabM <| getFieldShapesAndTypes declName
  -- Build the *unfolded* product type matching the shape's interp:
  -- `τ₁ × τ₂ × … × τₙ × PUnit`. Right-nested `Prod`, terminated by
  -- `PUnit`. This is the explicit type we pin `fromRepr`'s input
  -- through, so Lean doesn't have to unfold the mutual `interp` /
  -- `interpFields` block during instance elaboration.
  let mut interpTy : TSyntax `term ← `(PUnit)
  for ty in fieldTypes.reverse do
    interpTy ← `($ty × $interpTy)
  let structIdent := mkIdent declName
  let fieldIdents := fieldNames.map mkIdent
  -- Build `toRepr` body: wraps each field through its inner
  -- `SSZRepr.toRepr` so the field-type-to-shape-interp iso composes.
  -- For primitive fields (Bool, UInt*) with identity iso, this is a
  -- no-op semantically but typechecks uniformly.
  let mut toReprBody : TSyntax `term ← `(PUnit.unit)
  for fid in fieldIdents.reverse do
    toReprBody ← `(((SizzLean.SSZRepr.toRepr (s.$fid:ident)), $toReprBody))
  -- Build `fromRepr` via an anonymous-constructor pattern on the
  -- input. Each pattern binder `v_i` has type
  -- `(SSZRepr.shape Tᵢ).interp` (the inner shape's interp), and the
  -- structure literal field expects `Tᵢ`, bridge the two through
  -- `SSZRepr.fromRepr`.
  let vBinders : Array Ident := fieldIdents.map fun fid =>
    mkIdent (fid.getId.appendAfter "_v")
  let mut fromReprPat : TSyntax `term ← `(_)
  for vid in vBinders.reverse do
    fromReprPat ← `(⟨$vid:ident, $fromReprPat⟩)
  -- Wrap each binder with `SSZRepr.fromRepr` for the struct-literal
  -- assignment so the inner iso converts each field back to its
  -- user-facing type.
  let fromReprFields : Array (TSyntax `term) ← vBinders.mapM fun vid =>
    `(SizzLean.SSZRepr.fromRepr $vid:ident)
  -- Emit the instance command. Names are fully qualified so the
  -- synthesised instance resolves regardless of which namespace or
  -- `open` directives the user's declaration site has.
  --
  -- `to_from` / `from_to` proofs: with the iso bodies now wrapping
  -- each field through `toRepr`/`fromRepr`, the proofs need
  -- per-field unfolding (`SSZRepr.to_from`/`SSZRepr.from_to`). We
  -- discharge with `simp` over those lemma names: the right-nested
  -- `Prod` chain plus `PUnit` eta closes once the inner iso laws
  -- fire on each field.
  -- Build an explicit instance name from the full structure path,
  -- `instSSZRepr_<sanitized full name>`. Without this, Lean's
  -- auto-naming uses just the *leaf* component of the type name
  -- (e.g. `instSSZReprMinimal`), which collides between sibling types
  -- that share a leaf via `ssz_struct_for_presets` (every preset
  -- variant has the same suffix `Minimal` / `Mainnet`).
  let instLeafStr : String :=
    "instSSZRepr_" ++ (declName.toString.replace "." "_")
  let instIdent : Ident :=
    mkIdent (`_root_ ++ Name.mkSimple instLeafStr)
  let cmd ← `(
    instance $instIdent:ident : SizzLean.SSZRepr $structIdent where
      shape    := SizzLean.Spec.SSZType.container [$shapeExprs,*]
      toRepr   := fun (s : $structIdent) => $toReprBody
      fromRepr := fun $fromReprPat:term =>
        { $[$fieldIdents:ident := $fromReprFields:term],* }
      to_from  := fun _ => by simp [SizzLean.SSZRepr.to_from]
      from_to  := fun _ => by simp [SizzLean.SSZRepr.from_to])
  trace[Elab.Deriving.sszRepr] "Emitting:\n{cmd}"
  elabCommand cmd

/-- The deriving handler. Lean's `deriving SSZRepr` clause invokes
this for each declared name. Returns `true` if handled.

Only single-structure derivations are handled (no mutual
inductives, no general inductives). Mutual / recursive `SSZRepr`
derivation can be added later if user types demand it. -/
def handler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  let declName := declNames[0]!
  let env ← getEnv
  unless isStructure env declName do
    return false
  mkInstance declName
  return true

initialize
  registerTraceClass `Elab.Deriving.sszRepr
  registerDerivingHandler ``SizzLean.SSZRepr handler

end SizzLean.Repr.Deriving
