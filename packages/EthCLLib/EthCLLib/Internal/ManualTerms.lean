import Lean
import EthCLLib.Internal.Binders
import EthCLLib.Internal.Capture
import EthCLLib.Internal.ProofLedger

/-!
# `EthCLLib.Internal.ManualTerms`: the `theorem_vectors_manual` command

The generator (`EthCLLib.TheoremVectors`) takes an author's witness terms
through this module: the terms sit next to the theorem they witness. A manual
witness is a value for one theorem input, written in the theorem's own file:

```lean
theorem_vectors_manual myTheorem
  let bs : SomeListType :=
    ((default : SomeListType).push 18446744073709551615)
  state    := { (default : BeaconState) with balances := bs }
  preState := default
  i        := 0
  delta    := 1
```

Indentation carries the block, the way a structure instance's fields do.
Each clause opens under `withPosition`, and the clause's term parses under
`colGt`, so a term stops at the next clause's label no matter how many lines
it spans. A `let` clause names a shared value: the clauses below it see it,
and it never reaches the theorem. An assignment clause names one theorem
input.

The command elaborates every clause and emits one private holder definition
per assignment. The theorem
`EthCLSpecs.Proofs.Fulu.increaseBalance_run_overflow` with an assignment to
`state` gets the holder
`EthCLSpecs.Proofs.Fulu.TheoremVectorsManual.increaseBalance_run_overflow.state`:
the theorem's declaring namespace, `TheoremVectorsManual`, the theorem's own
name, and the input's name. The holder takes the theorem's instance binders,
in the theorem's order, and the theorem's universe parameters, and nothing
else. The definition is `private`, so the public surface never sees it. The
definition is compiled, because the probe serializes manual terms in
compiled code through `evalExpr`, and that code calls the holder.

The registration records one `(theorem, input, holder)` name triple per
assignment in a `SimplePersistentEnvExtension`, the same storage
`characterizesExt` uses. Only names cross the `.olean`.

Every failure is a build error in the author's own file, at the exact
clause:

* The target must be a theorem under a registered fork's proof namespace,
  and the command must sit in the theorem's own file.
* One registration per theorem, and one assignment per input. An unknown
  label errors at its clause, with the theorem's input names.
* An input whose type mentions any binder outside the instance binders (a
  type parameter, or an earlier input) errors at its clause: no holder over
  the instance binders alone could exist.
* An ill-typed term errors at its clause, and a spelled `:` ascription must
  match its input's type.

Every check fires before the first declaration is added, so a failing
registration leaves the environment untouched.

## Lean idioms annotated on first appearance

* `withPosition` and `colGt`: the block's indentation mechanic.
  `withPosition` saves the clause's start column, and `colGt` makes the
  term's first token and every application continuation demand a strictly
  greater column, which is what ends a term at the next clause's label.
* `forallTelescope` and the two walks: walk one sorts every binder through
  `binderRole` and validates the labels. Walk two introduces the instance
  binders alone and elaborates the clause terms, so the non-instance
  binders stay out of scope while a term elaborates.
* `TermElabM.run'`: the generator's own containment for an author's term
  (`TheoremVectors/Command.lean`). The run keeps the walk's local context
  and starts a fresh term-elaboration state, and `withoutErrToSorry` turns
  an authoring error into a build error at the clause.
* `mkPrivateName`: the holder's `private` marking. A private declaration
  lives under a `_private.<module>` name, and the resolver answers a
  public-shaped spelling only inside its own module.
-/

set_option autoImplicit false

open Lean
open Lean.Elab.Command

namespace EthCLLib.Internal

/-! ## The ledger -/

/-- Every `theorem_vectors_manual` registration, as `(theorem, input,
holder)` name triples.

An `Array` (not a map) keeps the merge across imports trivial, the same
choice `characterizesExt` makes. Only names cross the `.olean`: the holder
terms live in compiled code, never in this state. -/
initialize manualTermsExt :
    SimplePersistentEnvExtension (Name × Name × Name) (Array (Name × Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- Every `theorem_vectors_manual` registration in the environment. -/
def manualTermsOf (env : Environment) : Array (Name × Name × Name) :=
  manualTermsExt.getState env

/-! ## The syntax -/

/-- One `theorem_vectors_manual` clause: a shared `let`, or one input's
assignment. -/
declare_syntax_cat manualClause

-- the `: <type>` ascription is optional, and the two forms of each clause
-- kind are separate rules, so the label, the type, and the term sit at
-- fixed indices
scoped syntax (name := theoremVectorsManualLetClause)
  withPosition("let " ident " : " term " := " colGt term) : manualClause

scoped syntax (name := theoremVectorsManualLetNoTypeClause)
  withPosition("let " ident " := " colGt term) : manualClause

scoped syntax (name := theoremVectorsManualAssignClause)
  withPosition(ident " : " term " := " colGt term) : manualClause

scoped syntax (name := theoremVectorsManualAssignNoTypeClause)
  withPosition(ident " := " colGt term) : manualClause

scoped syntax (name := theoremVectorsManualCmd)
  "theorem_vectors_manual " ident manualClause+ : command

/-! ## The clause walk -/

/-- One parsed clause. -/
private inductive ManualClause where
  /-- A shared `let`; the clauses below it see the value. -/
  | shared (name : Name) (nameStx : Syntax) (type? : Option Syntax) (val : Syntax)
  /-- An input assignment; one holder's term. -/
  | assign (name : Name) (nameStx : Syntax) (type? : Option Syntax) (val : Syntax)
  deriving Inhabited

/-- Every clause node of the command, in source order. `many`'s own node
wraps the list, so the walk recurses and keys on the four clause rule
kinds, the way the generator's line parsers key on their rules' kinds.
The kinds compare fully qualified: a bare name literal never picks up the
module namespace, and the rule names carry it. -/
private partial def collectClauses (stx : Syntax) (acc : Array Syntax) :
    Array Syntax :=
  let k := stx.getKind
  if k == `EthCLLib.Internal.theoremVectorsManualLetClause
      || k == `EthCLLib.Internal.theoremVectorsManualLetNoTypeClause
      || k == `EthCLLib.Internal.theoremVectorsManualAssignClause
      || k == `EthCLLib.Internal.theoremVectorsManualAssignNoTypeClause then
    acc.push stx
  else
    stx.getArgs.foldl (init := acc) fun acc s => collectClauses s acc

/-- Unpack one clause node. The optional `: <type>` ascription has its own
rule, and every parser element takes one slot, so the shapes read
`[let, ident, :, type, :=, term]` and `[ident, :, type, :=, term]` when the
ascription is spelled, and one slot less when it is not. -/
private def unpackClause (stx : Syntax) : ManualClause :=
  let k := stx.getKind
  if k == `EthCLLib.Internal.theoremVectorsManualLetClause then
    .shared stx[1].getId stx[1] (some stx[3]) stx[5]
  else if k == `EthCLLib.Internal.theoremVectorsManualLetNoTypeClause then
    .shared stx[1].getId stx[1] none stx[3]
  else if k == `EthCLLib.Internal.theoremVectorsManualAssignClause then
    .assign stx[0].getId stx[0] (some stx[2]) stx[4]
  else
    .assign stx[0].getId stx[0] none stx[2]

/-- The domain of the `n`-th `∀` binder of `e`, `none` past the chain. -/
private def forallDomain? : Expr → Nat → Option Expr
  | .forallE _ d _ _, 0     => some d
  | .forallE _ _ b _, n + 1 => forallDomain? b n
  | _, _                    => none

/-- The number of `instImplicit` foralls heading `type`. Walk one has
already checked that the instance binders form the theorem's binder
prefix, so this count is the prefix's length. -/
private def instancePrefixArity : Expr → Nat
  | .forallE _ _ b bi => if bi matches .instImplicit then instancePrefixArity b + 1 else 0
  | _ => 0

/-- Walk `type`'s instance-binder prefix: introduce one free variable per
`instImplicit` binder, keep the binder order, and hand `k` the prefix plus
the rest of the chain. `forallBoundedTelescope` instantiates the rest of
the chain over each new free variable, so a later binder's domain names
the free variables and never a loose bound variable. The first
non-instance binder stays unintroduced, so the clause terms cannot see it. -/
private def withInstanceTelescope {α : Type} (type : Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α :=
  Meta.forallBoundedTelescope type (some (instancePrefixArity type)) k

/-- Elaborate one clause's term against `expectedType?`: `errToSorry` is
off, so an authoring error is a build error at the clause. The run keeps the
walk's local context, so the instance free variables and the shared `let`s
stay visible. -/
private def elabClauseTerm (stx : Syntax) (expectedType? : Option Expr) :
    MetaM Expr := do
  let v ← (Lean.Elab.Term.withoutErrToSorry
    (Lean.Elab.Term.elabTermAndSynthesize stx expectedType?)).run'
  Lean.instantiateMVars v

/-- Elaborate a spelled `: <type>` ascription, with the same containment. -/
private def elabAscribedType (stx : Syntax) : MetaM Expr := do
  let t ← (Lean.Elab.Term.withoutErrToSorry
    (Lean.Elab.Term.elabType stx)).run'
  Lean.instantiateMVars t

/-! ## The command's elaboration -/

/-- The `theorem_vectors_manual` elaborator. It validates the target
theorem, the registration's file, and every clause's label, elaborates each
clause's term over the theorem's instance binders, installs one private
compiled holder per assignment, and records one `(theorem, input, holder)`
name triple per assignment in the ledger. Every failure is a build error at
the exact clause, and a failing registration adds no declaration. -/
@[command_elab theoremVectorsManualCmd]
def elabTheoremVectorsManual : CommandElab := fun stx => do
  -- the command's shape: the theorem ident at 1, the clause list at 2
  let thmName ← liftCoreM <| resolveGlobalConstNoOverload stx[1]
  let env ← getEnv
  -- 1. the theorem: a theorem, under a registered fork's proof namespace
  unless env.find? thmName matches some (.thmInfo _) do
    throwError "`theorem_vectors_manual` registers witness terms for a \
      theorem; `{thmName}` is not one."
  unless (registeredForks env).any fun fork =>
      (proofNamespaceOf fork).isPrefixOf thmName do
    throwError "`theorem_vectors_manual` must target a theorem under a \
      registered fork's proof namespace (`EthCLSpecs.Proofs.<Fork>`), and \
      `{thmName}` sits under none. Move the theorem into its fork's proof \
      directory, or move the command with it."
  -- 2. the file: the registration rides with the theorem it witnesses
  unless (env.getModuleIdxFor? thmName).isNone do
    throwError "`theorem_vectors_manual` sits in a file that imports \
      `{thmName}`. A registration must sit in the theorem's own file; move \
      it under the theorem."
  -- 3. one registration per theorem
  unless !((manualTermsOf env).any fun (t, _, _) => t == thmName) do
    throwError "`theorem_vectors_manual` already registered witness terms \
      for `{thmName}`; one registration per theorem."
  let clauses := (collectClauses stx[2] #[]).map unpackClause
  let some (.thmInfo thmVal) := env.find? thmName
    | throwError "`theorem_vectors_manual` cannot read `{thmName}`'s \
        statement."
  -- 4. the labels, then the holders. One term-elaboration run carries
  -- both walks, and the declarations are added only after it returns, so a
  -- failing registration leaves the environment untouched.
  let holders ← liftTermElabM do
    -- walk one: sort every binder through `binderRole`, the same sort the
    -- statement reader runs, and validate each assignment's label
    let plan ← Meta.forallTelescope thmVal.type fun fvars _ => do
      let mut instFvars : Array Expr := #[]
      let mut inputs : Array (Name × Expr × Nat) := #[]
      let mut nonInstCount := 0
      let mut sawNonInstance := false
      for f in fvars do
        let d ← Meta.getFVarLocalDecl f
        match ← binderRole d with
        | .instance =>
          unless !sawNonInstance do
            throwError "`theorem_vectors_manual` needs `{thmName}`'s \
              instance binders before its other binders. A holder \
              quantifies the instance prefix alone, and \
              `{d.userName.eraseMacroScopes}` breaks the prefix."
          instFvars := instFvars.push f
        | .input =>
          sawNonInstance := true
          inputs := inputs.push
            (d.userName.eraseMacroScopes, d.type, nonInstCount)
          nonInstCount := nonInstCount + 1
        | _ =>
          sawNonInstance := true
          nonInstCount := nonInstCount + 1
      let inputList :=
        if inputs.isEmpty then "none"
        else String.intercalate ", "
          (inputs.toList.map fun (n, _, _) => s!"`{n}`")
      let instIds := instFvars.map (·.fvarId!)
      let mut plan : Array (Name × Nat) := #[]
      let mut filled : Array Name := #[]
      for c in clauses do
        match c with
        | .shared .. => pure ()
        | .assign name nameStx _ _ =>
          let some (_, ty, nonInstIdx) := inputs.find? fun (n, _, _) => n == name
            | throwErrorAt nameStx "`theorem_vectors_manual`: `{name}` does \
                not name an input of `{thmName}`. The theorem's inputs are \
                {inputList}."
          unless !filled.contains name do
            throwErrorAt nameStx "`theorem_vectors_manual` fills `{name}` \
              twice in `{thmName}`'s registration; one assignment per \
              input."
          filled := filled.push name
          unless (collectFVars {} ty).fvarIds.all instIds.contains do
            throwErrorAt nameStx "`theorem_vectors_manual`: `{name}`'s type \
              in `{thmName}` mentions a binder a holder cannot take. An \
              input's type may depend on the instance binders alone, so no \
              holder over them could exist for a type parameter or an \
              earlier input."
          plan := plan.push (name, nonInstIdx)
      pure plan
    -- a lets-only registration would write nothing, so the command refuses it
    if plan.isEmpty then
      throwError "`theorem_vectors_manual` registered no assignments for \
        `{thmName}`; spell at least one input's clause, or drop the command."
    -- walk two: the instance prefix alone
    withInstanceTelescope thmVal.type fun instFvars rest => do
      let resultsRef ← IO.mkRef (#[] : Array (Name × Expr × Expr))
      -- the walk runs on a list, so the recursion is structural
      let rec go (cs : List ManualClause) (lets : Array (FVarId × Expr)) :
          MetaM (Array (FVarId × Expr)) := do
        match cs with
        | [] => return lets
        | c :: cs' =>
          match c with
          | .shared name _ typeStx? valStx =>
            let expected? ← match typeStx? with
              | some tStx => some <$> elabAscribedType tStx
              | none => pure none
            let v ← elabClauseTerm valStx expected?
            let ty ← Meta.inferType v
            unless !ty.hasExprMVar do
              throwError "`theorem_vectors_manual`: the type of the shared \
                value `{name}` has a metavariable. Spell it as \
                `let {name} : T := …`."
            Meta.withLocalDeclD name ty fun fv =>
              go cs' (lets.push (fv.fvarId!, v))
          | .assign name nameStx typeStx? valStx =>
            let some (_, nonInstIdx) := plan.find? fun (n, _) => n == name
              | throwErrorAt nameStx "`theorem_vectors_manual`: `{name}` does \
                  not name an input of `{thmName}`."
            let some inputType := forallDomain? rest nonInstIdx
              | throwErrorAt nameStx "`theorem_vectors_manual`: `{name}`'s \
                  binder position is past `{thmName}`'s binder chain."
            if let some tStx := typeStx? then
              let ascribed ← elabAscribedType tStx
              unless ← Meta.isDefEq ascribed inputType do
                throwErrorAt tStx "`theorem_vectors_manual`: the ascription \
                  `{tStx}` does not match `{name}`'s type in `{thmName}`."
            let v ← elabClauseTerm valStx (some inputType)
            resultsRef.set ((← resultsRef.get).push (name, inputType, v))
            go cs' lets
      let lets ← go clauses.toList #[]
      let results ← resultsRef.get
      -- the holders: one per assignment, over the instance prefix alone.
      -- The shared `let`s leave first, innermost first, because a value
      -- may mention the lets before it.
      let ns := thmName.getPrefix
      let leaf := thmName.componentsRev.headD .anonymous
      results.mapM fun (inputName, inputType, raw) => do
        let val := lets.reverse.foldl (init := raw)
          fun acc (fv, v) => acc.replaceFVarId fv v
        let val ← Lean.instantiateMVars val
        let holderBase := ns ++ `TheoremVectorsManual ++ leaf ++ inputName
        let holderName := mkPrivateName (← getEnv) holderBase
        let ty ← Meta.mkForallFVars instFvars inputType
        let val ← Meta.mkLambdaFVars instFvars val
        let ty ← Lean.instantiateMVars ty
        let val ← Lean.instantiateMVars val
        unless !(ty.hasExprMVar || val.hasExprMVar) do
          throwError "`theorem_vectors_manual`: the term for `{inputName}` \
            left a metavariable behind."
        pure (holderName, inputName, ty, val)
  -- 5. install: one private holder per assignment, compiled, because the
  -- probe's `evalExpr` calls it from compiled code
  for (holderName, _, ty, val) in holders do
    let envNow ← getEnv
    let decl : Declaration := .defnDecl
      { name        := holderName
        levelParams := thmVal.levelParams
        type        := ty
        value       := val
        hints       := ReducibilityHints.regular (getMaxHeight envNow val + 1)
        safety      := DefinitionSafety.safe }
    liftCoreM <| addDecl decl
    liftCoreM <| compileDecl decl
  -- 6. the ledger: one name triple per assignment
  for (holderName, inputName, _, _) in holders do
    modifyEnv fun env => manualTermsExt.addEntry env (thmName, inputName, holderName)

end EthCLLib.Internal
