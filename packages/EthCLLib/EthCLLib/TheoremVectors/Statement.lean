import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.Internal.Binders
import EthCLLib.Internal.Capture

/-!
# `EthCLLib.TheoremVectors.Statement`: the statement reader

The reader turns a theorem's type into a `Statement` (`THEOREM_VECTORS_ARCHITECTURE.md` §7):
the binder walk with its three-way classification (§7.1), target discovery
through the capture extension (§7.2), and shape matching over the conclusion
(§7.3, in that section's order). The reader keeps every instance binder free;
the generator command fixes them per preset later.

The scope walk over input types lives in `Scope.lean` (§7.4); the reporting
folds of §7.5 split the same way. The unknown-instance fold fires here,
because §7.1 already classified the binder. The function-input fold fires in
`Scope.lean`, because only the scope walk sees input types.

Three readings deviate from the sketches and carry their reasons:

- `target` is an `Option Name`. §7.2 says a conclusion with no spec function
  on its left side is `.unsupported`, but `getPtcElseOffset_lt_next_slot` is
  exactly that theorem, and the plan's stage 3 acceptance makes it write a
  vector. The walk still fills `target` when it finds a spec function, and a
  theorem whose conclusion matches no shape is `.unsupported` by §7.3's rule
  8 regardless.
- The pyspec name comes from the fork binding's `pyspecNames` table (§6).
  §7.2's sketch names no spec-name field, and the spelling a client
  consumes is data the fork owns, so the binding carries one row per
  function the fork declares with a pyspec spelling; the inherited
  replays carry none. The reader looks the discovered target up in the
  table. A target with no row answers `none`. A target declaration's
  docstring may still open with the backticked snake-case span, as
  documentation for humans; nothing reads it.
- The run matches require the run's state to be one of the statement's
  state-typed value binders, the binders whose type names
  `binding.stateType`; the `.runOk` returned value and post-state must
  mention only inputs (§7.3). A failure to meet that requirement makes the
  arm not fire. Matching falls through to the next rule, which is how a
  contract whose right side is a `match` lands on `.eq`.

## Lean idioms annotated

- `forallTelescope` walks the theorem's `∀` chain and hands the tactic the
  free variables plus the conclusion. The `Prop` binders among them are the
  hypotheses, so the walk is also where the reader sorts binders.
- `LocalDecl.binderInfo` tells the three binder kinds apart: `.instImplicit`
  is the `[...]` form, `.default` the explicit `(...)`, and `.implicit` /
  `.strictImplicit` the `{...}` form.
- `getAppFn` / `getAppArgs` see through an n-ary application spine, which is
  how the matcher names the head constant of `f a b` without unfolding `f`.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## The data model (§5.2, §5.3) -/

-- §5.3 defines `BoundRel` next to `Shape`; stage 0 put it in `Types.lean`
-- with the records' wire vocabulary.

/-- The conclusion forms the reader accepts (`THEOREM_VECTORS_ARCHITECTURE.md` §5.3). Each
carries the terms the executor evaluates, with the binders still free. -/
inductive Shape where
  /-- `lhs = rhs`. One vector; `rhs` pins the output. -/
  | eq (lhs rhs : Expr)
  /-- `lhs = true ↔ q`. Two vectors, one per side of `q`. -/
  | iffTrue (lhs q : Expr)
  /-- `lhs < b` or `lhs ≤ b`. One vector; the bound is checked. -/
  | bound (lhs : Expr) (rel : BoundRel) (b : Expr)
  /-- `act.run (pureState pre) = .ok (ret, pureState post)`, or the
  `runPure` reading `runPure act pre = .ok (ret, post)`. One vector; the
  recorded output is `ret` when the run's return value is the state, and
  `post` otherwise (§11.3's output rule). -/
  | runOk (act pre ret post : Expr)
  /-- `act.run (pureState pre) = .error err`, or the `runPure` reading
  `runPure act pre = .error err`. One vector with no post-state. -/
  | runError (act pre err : Expr)
  /-- Anything else, with the reason. -/
  | unsupported (reason : String)
  deriving Repr

/-- The wire tag of a shape, as the outcome files write it. The tags come
from `ShapeTag.tag`, the one home of the wire strings (§5.3); an
unsupported statement writes `unsupported` in the shape field and carries
the reason in its run entry. -/
def Shape.wire : Shape → String
  | .eq _ _          => ShapeTag.tag .eq
  | .iffTrue _ _     => ShapeTag.tag .iffTrue
  | .bound _ _ _     => ShapeTag.tag .bound
  | .runOk _ _ _ _   => ShapeTag.tag .runOk
  | .runError _ _ _  => ShapeTag.tag .runError
  | .unsupported _   => "unsupported"

/-- The record's shape tag (`THEOREM_VECTORS_ARCHITECTURE.md` §5.6): the `ShapeTag`
form of the wire mapping above. An `.unsupported` statement never reaches
a record; the `none` case is unreachable there. -/
def Shape.tag? : Shape → Option ShapeTag
  | .eq ..           => some .eq
  | .iffTrue ..      => some .iffTrue
  | .bound ..        => some .bound
  | .runOk ..        => some .runOk
  | .runError ..     => some .runError
  | .unsupported _   => none

/-- The `.unsupported` reason, when the shape is unsupported. -/
def Shape.reason? : Shape → Option String
  | .unsupported r => some r
  | _ => none

/-- One value binder of the theorem, explicit or implicit. -/
structure Input where
  /-- The binder's user-facing name. -/
  name     : Name
  /-- The binder's type, with the instance binders still free. -/
  type     : Expr
  /-- `true` for the `(...)` form, `false` for the `{...}` form. -/
  explicit : Bool
  deriving Repr, Inhabited

/-- One instance binder and the seam it belongs to (`THEOREM_VECTORS_ARCHITECTURE.md` §5.2).
The four known seams are the ones the generator binds per preset; an
unknown class is `.other` and the reader reports it (§7.5). -/
inductive InstanceKind where
  | preset
  | config
  | hasherTag
  | cryptoBackend
  /-- An instance binder the generator cannot bind. -/
  | other (className : Name)
  deriving Repr

/-- The parsed theorem: what the reader found, in binder order
(`THEOREM_VECTORS_ARCHITECTURE.md` §5.2). `blockInputs` starts empty; `Scope.classify`
fills it (§7.4). -/
structure Statement where
  /-- The theorem's full constant name. -/
  thm       : Name
  /-- Instance binders as `(binder name, seam)` pairs, in binder order. -/
  instances : Array (Name × InstanceKind)
  /-- Value binders, explicit and implicit, in binder order. -/
  inputs    : Array Input
  /-- Type-parameter binders (`{σ : Type}`, `{map : MapKind}`): neither
  instances nor producible values; the fork binding fixes them. -/
  typeBinders : Array Name
  /-- `Prop` binders, in binder order; each entry is the proposition itself. -/
  hyps      : Array Expr
  /-- The spec function under test, when the conclusion's left side names
  one the binding's fork owns (§7.2). -/
  target    : Option Name
  /-- The target's pyspec name, from the fork binding's `pyspecNames`
  table (§6). A target with no row answers `none`. The function format
  then falls back to the Lean target name. -/
  pyspecName : Option String
  /-- The scalar kind of each input, in binder order, `none` for a
  container (`§9.4`). The reader computes it once, in `MetaM`, because
  the kind needs a reducible `whnf` that a pure `applies` test cannot
  run; the searchers' `applies` tests and the probe read this field, which
  is what keeps an alias (`Gwei` for `UInt64`) reading as a container in
  a pure test (§9.4). -/
  scalarKinds : Array (Option ScalarKind)
  /-- The matched conclusion form (§7.3). -/
  shape     : Shape
  /-- Inputs out of scope by the block-input rule (§1.2); `Scope.classify`
  fills it. -/
  blockInputs : Array Name := #[]
  deriving Repr

/-! ## Binder classification (§7.1) -/

/-- The seam of an instance binder, from the class the binder's type names.
The four known seams match on the class name's last component, because each
fork declares its own `Preset` and `Config` classes and the theorem binds
the fork's, not a shared one. -/
private def instanceKindOf (type : Expr) : InstanceKind :=
  -- `componentsRev` heads with the name's last atom: `Preset` for
  -- `EthCLSpecs.Gloas.Preset`
  match type.getAppFn with
  | .const c _ =>
    match c.componentsRev.headD .anonymous with
    | `Preset        => .preset
    | `Config        => .config
    | `HasherTag     => .hasherTag
    | `CryptoBackend => .cryptoBackend
    | _              => .other c
  | _ => .other Name.anonymous

/-! ## Target discovery (§7.2) -/

/-- Is the constant `c` a function the binding's fork owns? §7.2's two
queries combine here: `specFunctionOwner?` gives fork ownership, and the
candidate must name a function, not a type. The `forkdef` narrowing of
`isSpecFunction` alone would drop the fork-upgrade file's boundary
functions, which are plain `def`s (`initializePtcWindow` among them) and
§7.2's own example names one as the target. Ownership plus
"elaborates to a definition, and not a projection accessor" keeps the
fork's containers, its `forkstruct` types, and their field accessors out
of the walk while keeping every callable fork function in. The test's one
home is `ForkBinding.ownedSpecFunction?`; the binding's `pyspecNames`
validation reads through the same rule. -/
private def isOwnedSpecFunction (env : Environment) (binding : ForkBinding)
    (c : Name) : Bool :=
  ownedSpecFunction? env binding c

/-- The left side of a conclusion: the first operand of an equation, an
`↔`'s equation's first operand, or the first operand of a comparison.
`none` when the conclusion has none of those heads. -/
private partial def conclusionLhs? (body : Expr) : Option Expr :=
  match body.getAppFn, body.getAppArgs with
  | .const c _, args =>
    if c == ``Eq && args.size ≥ 2 then some args[1]!
    else if c == ``Iff && args.size ≥ 1 then conclusionLhs? args[0]!
    else if (c == ``LT.lt || c == ``LE.le) && args.size ≥ 3 then some args[2]!
    else none
  | _, _ => none

/-- Pre-order walk over `e` for the first application whose head is a spec
function the binding's fork owns. This is what finds
`initializePtcWindow` under the `GetElem.getElem` head of
`(initializePtcWindow (pureState state))[i]` (§7.2).

Type and instance arguments stay out of the walk: `@StateT.run σ m α act s`
carries the boxed state type in `σ`, and pre-order over it would name the
fork's `State` abbreviation, not the action under test;
`(x)[i]`'s spine carries the `GetElem` instance for the fork's container,
and pre-order over that would name the fork's instance constant. An
argument is skipped when `inferType` answers a sort (a type argument) or
`isClass?` answers a class name (an instance argument); the term
arguments (the action, the collection, the pre-state) are what the walk
descends into. -/
private partial def findTargetIn (env : Environment) (binding : ForkBinding)
    (e : Expr) : MetaM (Option Name) :=
  match e with
  | .const c _ => pure (if isOwnedSpecFunction env binding c then some c else none)
  | .app f a => do
    let inF ← findTargetIn env binding f
    match inF with
    | some _ => pure inF
    | none => do
      let aType ← Meta.inferType a
      if aType.isSort then pure none
      else if (← Meta.isClass? aType).isSome then pure none
      else findTargetIn env binding a
  | .mdata _ b => findTargetIn env binding b
  | .proj _ _ b => findTargetIn env binding b
  -- `lam` and `letE` stay out: a left side under a binder is not an
  -- application the executor could call, and instantiating the binder
  -- here would drag the walk past the term it was given
  | _ => pure none

/-! ## Shape matching (§7.3) -/

/-- Is the conclusion's head a framework box predicate (`THEOREM_VECTORS_ARCHITECTURE.md`
§7.3, rule 8)? A theorem whose conclusion states `KeepsUncached`,
`KeepsUncachedFrom`, or `ReturnsUncached` is a box lemma: it states a fact
about the box discipline of a spec function, and no input and output pair
expresses it. -/
private def isBoxLemmaHead (c : Name) : Bool :=
  c == `EthCLLib.Proofs.KeepsUncached
    || c == `EthCLLib.Proofs.KeepsUncachedFrom
    || c == `EthCLLib.Proofs.ReturnsUncached

/-- The plain value under a `pureState` or `SSZ.UncachedBox` wrapper, the
two spellings a contract theorem uses for its pre- and post-state. -/
private def pureBox? (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const c _ =>
    if c == `EthCLLib.Proofs.pureState || c == `SizzLean.Cache.SSZ.UncachedBox then
      e.getAppArgs.back?
    else none
  | _ => none

/-- The value under an `Except.ok`, when `e` is one. -/
private def exceptOk? (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const c _ => if c == ``Except.ok then e.getAppArgs.back? else none
  | _ => none

/-- The error under an `Except.error`, when `e` is one. -/
private def exceptError? (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const c _ => if c == ``Except.error then e.getAppArgs.back? else none
  | _ => none

/-- The two halves of a `Prod.mk`, when `e` is one. -/
private def prodMk? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFn, e.getAppArgs with
  | .const c _, args =>
    if c == ``Prod.mk && args.size ≥ 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else none
  | _, _ => none

/-- The equation's two sides, when `body` is an `Eq` application. -/
private def eqSides? (body : Expr) : Option (Expr × Expr) :=
  match body.getAppFn, body.getAppArgs with
  | .const c _, args =>
    if c == ``Eq && args.size ≥ 2 then some (args[1]!, args[2]!) else none
  | _, _ => none

/-- Every fvar of `e` is one the theorem binds? The `.runOk` match
requires the run's returned value and its post-state to be closed terms
over the inputs (§7.3). The binders include the instance binders,
because the box wrappers take
`[SSZRepr T]` and `[HasherTag]` implicitly: the post-state's `pureState`
applications carry those fvars, and phase B fixes them like every other
instance binder (§10). What the check rules out is a term over locals the
theorem does not bind, an existential's body or a proof's subterm. An
unbound fvar in the returned value would surface as a crash at
`evalExpr`; the check turns the arm off instead. -/
private def overBindersOnly (e : Expr) (binderIds : Array FVarId) : Bool :=
  (collectFVarIds e #[]).all binderIds.contains

/-- The `lhs = true` left side of an `.iffTrue` conclusion. -/
private def eqTrueLhs? (body : Expr) : Option Expr := do
  let (lhs, rhs) ← eqSides? body
  match rhs.getAppFn with
  | .const c _ => if c == ``Bool.true then some lhs else none
  | _ => none

/-- The `.runOk` reading of a `StateT.run` equation: the action runs on the
box of `pre` and returns `(ret, pureState post)` (§7.3, form 2). Fires only
when `pre` is one of the state-typed binders and `ret` and `post` mention
only binders. -/
private def runOkStateT? (body : Expr) (preIds : Array FVarId)
    (binderIds : Array FVarId) :
    Option (Expr × Expr × Expr × Expr) := do
  let (lhs, rhs) ← eqSides? body
  match lhs.getAppFn, lhs.getAppArgs with
  | .const c _, args =>
    if c != ``StateT.run then none
    else do
      let act ← args[args.size - 2]?
      let st ← args[args.size - 1]?
      let pre ← pureBox? st
      unless pre.fvarId?.any preIds.contains do none
      let value ← exceptOk? rhs
      let (ret, postBox) ← prodMk? value
      let post ← pureBox? postBox
      unless overBindersOnly ret binderIds do none
      unless overBindersOnly post binderIds do none
      some (act, pre, ret, post)
  | _, _ => none

/-- The `.runOk` reading of a `runPure` equation (§7.3, form 3): the
post-state arrives as the plain value, with no box wrapper to strip. Fires
only when `pre` is one of the state-typed binders and `ret` and `post`
mention only binders. -/
private def runOkRunPure? (body : Expr) (preIds : Array FVarId)
    (binderIds : Array FVarId) :
    Option (Expr × Expr × Expr × Expr) := do
  let (lhs, rhs) ← eqSides? body
  match lhs.getAppFn, lhs.getAppArgs with
  | .const c _, args =>
    if c != `EthCLLib.Proofs.runPure then none
    else do
      let act ← args[args.size - 2]?
      let pre ← args[args.size - 1]?
      unless pre.fvarId?.any preIds.contains do none
      let value ← exceptOk? rhs
      let (ret, post) ← prodMk? value
      unless overBindersOnly ret binderIds do none
      unless overBindersOnly post binderIds do none
      some (act, pre, ret, post)
  | _, _ => none

/-- The `.runError` reading of a `StateT.run` equation (§7.3, form 4). -/
private def runErrorStateT? (body : Expr) (preIds : Array FVarId) :
    Option (Expr × Expr × Expr) := do
  let (lhs, rhs) ← eqSides? body
  match lhs.getAppFn, lhs.getAppArgs with
  | .const c _, args =>
    if c != ``StateT.run then none
    else do
      let act ← args[args.size - 2]?
      let st ← args[args.size - 1]?
      let pre ← pureBox? st
      unless pre.fvarId?.any preIds.contains do none
      let err ← exceptError? rhs
      some (act, pre, err)
  | _, _ => none

/-- The `.runError` reading of a `runPure` equation (§7.3, form 5). It
mirrors `runOkRunPure?` on the error side: the value under the run
arrives as the plain binder, with no box wrapper to strip. -/
private def runErrorRunPure? (body : Expr) (preIds : Array FVarId) :
    Option (Expr × Expr × Expr) := do
  let (lhs, rhs) ← eqSides? body
  match lhs.getAppFn, lhs.getAppArgs with
  | .const c _, args =>
    if c != `EthCLLib.Proofs.runPure then none
    else do
      let act ← args[args.size - 2]?
      let pre ← args[args.size - 1]?
      unless pre.fvarId?.any preIds.contains do none
      let err ← exceptError? rhs
      some (act, pre, err)
  | _, _ => none

/-- Shape matching in §7.3's order: `.iffTrue`, `.runOk` in its two forms,
`.runError` in its two forms, `.eq`, `.bound`, then `.unsupported` with the
conclusion's head constant in the reason. A conclusion whose head is a
framework box predicate (`KeepsUncached`, `KeepsUncachedFrom`,
`ReturnsUncached`) is a box lemma (§7.3, rule 8): the reason reads
`box lemma: <head>`, and the report counts these apart from the other
`.unsupported` reasons (§16.2). -/
private def matchShape (body : Expr) (preIds : Array FVarId)
    (binderIds : Array FVarId) : Shape :=
  match body.getAppFn with
  | .const cHead _ =>
    if cHead == ``Iff then
      -- rule 1: `lhs = true ↔ q`
      match body.getAppArgs[0]?, body.getAppArgs[1]? with
      | some side, some q =>
        match eqTrueLhs? side with
        | some lhs => .iffTrue lhs q
        | none => .unsupported "unsupported conclusion: `↔` whose left side is not `… = true`"
      | _, _ => .unsupported "unsupported conclusion: head `Iff`"
    else
      if let some (act, pre, ret, post) := runOkStateT? body preIds binderIds then
        -- rule 2
        .runOk act pre ret post
      else if let some (act, pre, ret, post) := runOkRunPure? body preIds binderIds then
        -- rule 3
        .runOk act pre ret post
      else if let some (act, pre, err) := runErrorStateT? body preIds then
        -- rule 4
        .runError act pre err
      else if let some (act, pre, err) := runErrorRunPure? body preIds then
        -- rule 5
        .runError act pre err
      else
        -- rule 6, then rule 7, then rule 8
        match eqSides? body with
        | some (lhs, rhs) => .eq lhs rhs
        | none =>
          match cHead, body.getAppArgs with
          | c, args =>
            if (c == ``LT.lt || c == ``LE.le) && args.size ≥ 4 then
              let rel : BoundRel := if c == ``LT.lt then .lt else .le
              .bound args[2]! rel args[3]!
            else if isBoxLemmaHead c then
              .unsupported s!"box lemma: {c}"
            else
              .unsupported s!"unsupported conclusion: head `{c}`"
  | _ => .unsupported "unsupported conclusion: not an application"

/-! ## The reader -/

/-- Zeta-reduce the leading `let`s of a conclusion. A theorem may spell a
scratch value between its hypotheses and its conclusion
(`getInclusionListCommittee_run_eq` names `indices` there), and
`forallTelescope` stops at the `let`, handing the matcher a `letE` where
it expects the conclusion's head. Instantiating the value into the body
is the whole reduction; the reader's shapes match over what is left. -/
private partial def zetaLets (body : Expr) : Expr :=
  match body with
  | .letE _ _ v b _ => zetaLets (b.instantiate1 v)
  | _ => body

/-- What the reader hands its caller: the parsed statement plus the free
variables the binder walk introduced, so the probe can substitute the
instance binders and abstract the value binders (`THEOREM_VECTORS_ARCHITECTURE.md` §11.2).
The variables are telescope-local: like the statement's expressions, they
are valid only inside the reader's fold. -/
structure StatementCtx where
  /-- The parsed theorem. -/
  stmt       : Statement
  /-- One free variable per value input, aligned with `stmt.inputs`. -/
  inputFvars : Array Expr
  /-- One free variable per instance binder, aligned with
  `stmt.instances`. -/
  instFvars  : Array Expr

/-- Read one theorem into a `StatementCtx` and fold `k` over it (§7). Errors
when the name does not resolve or is not a theorem; the failure policy
makes both build errors (`THEOREM_VECTORS_ARCHITECTURE.md` §18).

`k` runs inside the telescope's scope, and the statement cannot escape it:
the binder walk introduces the theorem's free variables with a local
context that `forallTelescope` restores once its callback returns, so a
`Statement` carried out of `k` would name free variables no later step can
see. Every consumer therefore folds to its wire form inside `k`: the
command derives the outcome and writes it, the probe builds and evaluates
its term, the pins assert on the reader's answer. -/
def Statement.readIn {α : Type} (binding : ForkBinding) (thmName : Name)
    (k : StatementCtx → MetaM α) : MetaM α := do
  let env ← getEnv
  let some info := env.find? thmName
    | throwError "theorem_vectors: `{thmName}` does not resolve"
  let .thmInfo v := info
    | throwError "theorem_vectors: `{thmName}` is not a theorem"
  Meta.forallTelescope v.type fun fvars body => do
    let mut instances : Array (Name × InstanceKind) := #[]
    let mut instFvars : Array Expr := #[]
    let mut inputs : Array Input := #[]
    let mut inputFvars : Array Expr := #[]
    let mut typeBinders : Array Name := #[]
    let mut preIds : Array FVarId := #[]
    let mut binderIds : Array FVarId := #[]
    let mut hyps : Array Expr := #[]
    for f in fvars do
      let d ← Meta.getFVarLocalDecl f
      binderIds := binderIds.push d.fvarId
      match ← EthCLLib.Internal.binderRole d with
      | .instance =>
        instances := instances.push (d.userName.eraseMacroScopes, instanceKindOf d.type)
        instFvars := instFvars.push f
      | .hypothesis =>
        hyps := hyps.push d.type
      | .typeParameter =>
        -- a type parameter the fork binding fixes (`{σ : Type}`,
        -- `{map : MapKind}`): not a class, so §7.1's instance arm does not
        -- take it, and not a value any searcher could produce
        typeBinders := typeBinders.push d.userName.eraseMacroScopes
      | .input =>
        inputs := inputs.push
          { name := d.userName.eraseMacroScopes, type := d.type
            explicit := d.binderInfo matches .default }
        inputFvars := inputFvars.push f
        -- the run's state, by type: every value binder whose type names
        -- the binding's state container is a candidate store (§7.3). The
        -- Fulu balance theorems bind two `BeaconState` values and read
        -- one, threading the other, so the position of the binder cannot
        -- pick the store
        if isStateType binding d.type then preIds := preIds.push d.fvarId
    let body := zetaLets body
    let target ← match conclusionLhs? body with
      | none => pure none
      | some lhs => findTargetIn env binding lhs
    -- the pyspec name, from the binding's table (§6): one row per
    -- function the fork declares with a pyspec spelling, and a target
    -- with no row answers `none`
    let pyspecName := target.bind fun c =>
      binding.pyspecNames.find? (fun p => p.1 == c) |>.map (·.2)
    -- the scalar kinds, once per input: the searchers' `applies` tests and
    -- the probe read this table, so an alias never reads as a container
    -- and the reducible `whnf` never runs twice (§9.4)
    let scalarKinds ← inputs.mapM fun i => scalarKind i.type
    let shape := matchShape body preIds binderIds
    -- §7.5: an instance binder on an unknown seam is a skip, because the
    -- command cannot bind it. The fold keeps an already-unsupported reason,
    -- the same precedence §7.3's rule 8 has over the folds. Hygienic
    -- instance names lose their macro scopes, so the report shows the
    -- binder's source-level name.
    let shape :=
      match instances.find? fun (_, k) => k matches .other _ with
      | some (n, .other c) =>
        if shape matches .unsupported _ then shape
        else .unsupported s!"unknown instance seam on binder `{n}`: `{c}`"
      | _ => shape
    k { stmt := { thm := thmName, instances, inputs, typeBinders, hyps, target,
                  pyspecName, scalarKinds, shape }
        inputFvars, instFvars }

end EthCLLib.TheoremVectors
