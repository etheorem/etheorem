import Lean
import Lean.Elab.Tactic.BVDecide
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Layers

/-!
# `EthCLLib.TheoremVectors.Witness.BitVec`: the bit-vector searcher

The solver-backed witness searcher (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4). The searcher
poses the disjunct's negated conjunction as a goal and calls `bvDecide'` from
`Lean.Elab.Tactic.BVDecide.Frontend`. A `Result` proves `¬P`, so the disjunct is
vacuous and the searcher answers `unsat`; no later searcher can find
what does not exist. A `CounterExample` is a model of `P`: its equations pair the
solver's atoms with values, the reader unwraps the `UIntX.toBitVec` /
`BitVec.ofBool` wrappers, and the values become the scalar inputs of a
candidate the loop's check still decides.

Three forms of the solve live here, one entry point:

- **Pure scalar.** Every input scalar and no manual terms: the prepared
  hypotheses go to the solver as they are.
- **The manual handoff.** A line whose manual terms fix the container
  inputs leaves scalar inputs, and the prepared hypotheses still name the
  manual values (`maxBalanceState.balances[i.toNat]!` in
  `increaseBalance_run_overflow`). The
  searcher fixes each *coupled* scalar, one that co-occurs with a manual
  input, over a bounded value grid. At each fixed point the manual reads
  become closed terms of scalar type, the searcher evaluates them in
  compiled code and substitutes the literals, and the solver takes the
  remaining free scalars. The grid holds the small values a scalar index
  into a manual container takes in practice; a scalar the grid misses
  falls to a later searcher. The check
  stays the single arbiter throughout: a candidate from any fixed point
  counts only when the compiled `decide` accepts it, and a
  per-fixed-point `unsat` never reports the disjunct vacuous, because another
  grid point may satisfy it.
- **The `Fin` bridge.** A free `Fin n` input enters the solver as a
  `UInt64` stand-in with the bound `u < n` posed as a hypothesis of the
  goal, so the solver's model stays in range; the `Fin.val` reads rewrite
  to the stand-in, and the candidate's value crosses the byte boundary
  through `Fin`'s own codec, whose strict decode refuses what slipped
  past (§9.3, §9.4).

The random searcher (§9.4) drives the same entry point with its drawn
containers in the `drawn` overlay: the manual terms' positions stay the
probe's, and the drawn bytes stand in for the containers, so a drawn
state grounds the same reads a manual term would.

## Lean idioms annotated

- `Frontend.bvDecide'` creates auxiliary declarations and compiles them, so
  it runs only through the compiled implementation behind
  `@[implemented_by]`, the same shape `Command.lean`'s `evalConst` uses;
  the `opaque` face is what interpreted code sees.
- `mkFreshExprMVar` inside `withLocalDeclD` gives the goal the free scalars
  as its local context, which is what `bv_decide`'s reflection and its
  counterexample equations name; the reflection takes every proposition in
  the goal's context, which is how the `Fin` stand-ins' bound enters the
  formula.
- `Expr.replace` with a `none`-returning function is a bottom-up rewrite:
  the instance substitution below rewrites only the free variables it
  knows and leaves every other node to the recursion.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## The solver call (§9.4) -/

/-- The `bvDecide'` call behind the compiled face below. `TacticContext.new`
is `TermElabM` and the searcher runs in `MetaM`, so the context is built
here with core's fresh names and the same cadical lookup `TacticContext.new`
does. -/
private unsafe def bvDecideImpl (g : MVarId) :
    MetaM (Except Lean.Elab.Tactic.BVDecide.Frontend.CounterExample
      Lean.Elab.Tactic.BVDecide.Frontend.Result) := do
  IO.FS.withTempFile fun _ lrat => do
    let solver := ((← IO.appPath).parent.get! / "cadical")
      |>.withExtension System.FilePath.exeExtension
    let solver := if ← solver.pathExists then solver else "cadical"
    let ctx : Lean.Elab.Tactic.BVDecide.Frontend.TacticContext := {
      exprDef       := ← Lean.Core.mkFreshUserName `bvExprDef
      certDef       := ← Lean.Core.mkFreshUserName `bvCertDef
      reflectionDef := ← Lean.Core.mkFreshUserName `bvReflectionDef
      solver, lratPath := lrat, config := {}
    }
    Lean.Elab.Tactic.BVDecide.Frontend.bvDecide' g ctx

/-- The compiled face of the `bvDecide'` call (§9.4). Proves the goal or
returns the counterexample whose model the reader turns into a candidate. -/
@[implemented_by bvDecideImpl]
private opaque bvDecideCore (g : MVarId) :
    MetaM (Except Lean.Elab.Tactic.BVDecide.Frontend.CounterExample
      Lean.Elab.Tactic.BVDecide.Frontend.Result)

/-! ## Compiled evaluation of closed reads -/

/-- Compiled evaluation of a closed `Nat` term. -/
private unsafe def evalNatImpl (e : Expr) : MetaM Nat :=
  Lean.Meta.evalExpr Nat (.const ``Nat []) e

/-- The compiled face of a closed `Nat` evaluation (§9.4's read
grounding; the built searcher reads the fork's `slotsPerEpoch` through
it, which is what puts the grid's first epoch boundary in preset units
without naming a fork). -/
@[implemented_by evalNatImpl] opaque evalNatOp (e : Expr) : MetaM Nat

/-- Compiled evaluation of a closed `Bool` term. -/
private unsafe def evalBoolImpl (e : Expr) : MetaM Bool :=
  Lean.Meta.evalExpr Bool (.const ``Bool []) e

@[implemented_by evalBoolImpl] private opaque evalBoolOp (e : Expr) : MetaM Bool

/-- Compiled evaluation of a closed `UInt8` term. -/
private unsafe def evalUInt8Impl (e : Expr) : MetaM UInt8 :=
  Lean.Meta.evalExpr UInt8 (.const ``UInt8 []) e

@[implemented_by evalUInt8Impl] private opaque evalUInt8Op (e : Expr) : MetaM UInt8

/-- Compiled evaluation of a closed `UInt16` term. -/
private unsafe def evalUInt16Impl (e : Expr) : MetaM UInt16 :=
  Lean.Meta.evalExpr UInt16 (.const ``UInt16 []) e

@[implemented_by evalUInt16Impl] private opaque evalUInt16Op (e : Expr) : MetaM UInt16

/-- Compiled evaluation of a closed `UInt32` term. -/
private unsafe def evalUInt32Impl (e : Expr) : MetaM UInt32 :=
  Lean.Meta.evalExpr UInt32 (.const ``UInt32 []) e

@[implemented_by evalUInt32Impl] private opaque evalUInt32Op (e : Expr) : MetaM UInt32

/-- Compiled evaluation of a closed `UInt64` term. -/
private unsafe def evalUInt64Impl (e : Expr) : MetaM UInt64 :=
  Lean.Meta.evalExpr UInt64 (.const ``UInt64 []) e

@[implemented_by evalUInt64Impl] private opaque evalUInt64Op (e : Expr) : MetaM UInt64

/-- The values one coupled scalar walks in the grid (§9.4): the small values
a scalar index into a manual container takes in practice. -/
def gridValuesPerScalar : Nat := 64

/-- The grid's point cap (§9.4): the most fixed points one disjunct's handoff
walks. -/
def gridPointCap : Nat := 128

/-- The values one coupled scalar walks in the grid: the small values a
scalar index into a manual container takes in practice. -/
def gridValues (k : ScalarKind) : MetaM (Array Nat) := do
  match k with
  | .bool => pure #[0, 1]
  | .uint _ | .nat => pure (Array.range gridValuesPerScalar)
  | .fin n => do
    let nVal ← try evalNatOp n catch _ => pure 0
    pure (Array.range (min nVal gridValuesPerScalar))

/-! ## The term walk -/

/-- Free-variable substitution. -/
private def substFvars (e : Expr) (sub : Array (FVarId × Expr)) : Expr :=
  e.replace fun s =>
    match s with
    | .fvar id => (sub.find? fun (g, _) => g == id).map (·.2)
    | _ => none

/-- The literal form of a closed scalar term, evaluated in compiled code
(§9.4's read substitution). `none` when the type is not a scalar the walk
records, which leaves the term for the solver to abstract. -/
private def scalarLiteralOfTerm (closed : Expr) (ty : Expr) : MetaM (Option Expr) := do
  match ← scalarKind ty with
  | none => return none
  | some .bool => do
    let b ← try evalBoolOp closed catch _ => return none
    return some (.const (if b then ``Bool.true else ``Bool.false) [])
  | some .nat => do
    let v ← try evalNatOp closed catch _ => return none
    return some (mkRawNatLit v)
  | some (.uint w) => do
    let v? ← try
      (match w with
        | 8  => some <$> ((·.toNat) <$> evalUInt8Op closed)
        | 16 => some <$> ((·.toNat) <$> evalUInt16Op closed)
        | 32 => some <$> ((·.toNat) <$> evalUInt32Op closed)
        | _  => some <$> ((·.toNat) <$> evalUInt64Op closed))
    catch _ => pure none
    let some v := v? | return none
    let lit := mkRawNatLit v
    let inst? ← try
      some <$> Meta.synthInstance
        (mkAppN (.const ``OfNat [levelZero]) #[ty, lit])
    catch _ =>
      pure none
    match inst? with
    | some inst => return some (mkAppN (.const ``OfNat.ofNat [levelZero]) #[ty, lit, inst])
    | none => return none
  | some (.fin _) => return none

/-- Is the term already in literal form? A raw literal, a `Bool`
constructor, or an `OfNat.ofNat` over a raw literal needs no compiled
evaluation. -/
private def literalForm (e : Expr) : Bool :=
  match e with
  | .lit _ => true
  | .const c _ => c == ``Bool.true || c == ``Bool.false
  | _ =>
    match e.getAppFn, e.getAppArgs with
    | .const ``OfNat.ofNat _, #[_, lit, _] =>
      match lit with
      | .lit _ => true
      | _ => false
    | _, _ => false

/-- The result type of `e`'s head constant, after the leading binders. -/
private def headResultType (env : Environment) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const c _ =>
    (env.find? c).map fun info =>
      let rec strip (t : Expr) : Expr :=
        match t with
        | .forallE _ _ b _ | .lam _ _ b _ => strip b
        | _ => t
      strip info.type
  | _ => none

/-- Can a subterm of this shape ground to a scalar literal at all? A type
(a sort result) and a class instance or type family (an application result)
cannot; the walk skips the `inferType` call for them and still descends.
A constant result may be an alias (`Gwei` for `UInt64`), so the gate leaves
its decision to the scalar kind, which reduces aliases (§9.4). -/
private def groundsScalar (env : Environment) (e : Expr) : Bool :=
  match e with
  | .lit _ => true
  | .proj .. => true
  | _ =>
    match headResultType env e with
    | none => true
    | some (.sort _) => false
    | some (.app ..) => false
    | some _ => true

/-- Replace every maximal closed subterm of `e` with its compiled value
(§9.4's read substitution). Manual reads
(`oneBalanceState.balances[0]!` from `decreaseBalance_run_no_underflow`),
preset constants
(`UInt64.ofNat slotsPerEpoch`, whose opaque form the solver would abstract
into a spurious model), and crypto gates under the verify-off backend all
ground to literals this way; the residual formula stays a bit-vector
formula over the free scalars alone. Subterms that mention a free scalar
stay, and the solver abstracts them.

The grounding gate answers from the environment before the `inferType`
walk: a type, a type family, and a class instance never ground, and a term
already in literal form needs no evaluation. Both skips save one
`inferType` per node, which is the walk's own cost on a large hypothesis. -/
private partial def eliminateReads (freeIds : Array FVarId)
    (instSub : Expr → Expr) (e : Expr) : MetaM Expr := do
  if literalForm e then
    return e
  let tryLiteral : MetaM (Option Expr) := do
    let ids := collectFVarIds e #[]
    -- a term is evaluable only when it names no variable at all: an
    -- `evalExpr` on a free variable (a fresh scalar's own fvar, or a
    -- drawn container's variable) throws. A term under a lambda carries
    -- loose bound variables, which no compiled evaluation can run; the
    -- caller descends into it instead
    unless ids.isEmpty && !e.hasLooseBVars do
      return none
    let ty ← Meta.inferType e
    scalarLiteralOfTerm (instSub e) ty
  let lit? ←
    if groundsScalar (← getEnv) e then tryLiteral else pure none
  match lit? with
  | some lit => return lit
  | none =>
    match e with
    | .app f a =>
      let f' ← eliminateReads freeIds instSub f
      let a' ← eliminateReads freeIds instSub a
      return .app f' a'
    | .lam n t b bi =>
      return .lam n (← eliminateReads freeIds instSub t)
        (← eliminateReads freeIds instSub b) bi
    | .letE n t v b bi =>
      return .letE n (← eliminateReads freeIds instSub t)
        (← eliminateReads freeIds instSub v)
        (← eliminateReads freeIds instSub b) bi
    | .mdata m b => return .mdata m (← eliminateReads freeIds instSub b)
    | .proj s i b => return .proj s i (← eliminateReads freeIds instSub b)
    | _ => return e

/-- Introduce one fresh local per type and fold. -/
private partial def withFreshScalars {α : Type} (tys : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α :=
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : MetaM α :=
    if h : i < tys.size then
      Meta.withLocalDeclD (Name.append (`tvScalar) (Name.mkSimple (toString i))) tys[i] fun f =>
        go (i + 1) (acc.push f)
    else
      k acc

/-- The counterexample's atom under its `BitVec` wrapper: `UIntX.toBitVec x`
and `BitVec.ofBool x` unwrap to `x`, the input free variable the equation
values. -/
private def unwrapAtom (e : Expr) : Option FVarId :=
  match e.getAppFn, e.getAppArgs with
  | .const c _, args =>
    let named : Bool :=
      match c.componentsRev.headD .anonymous with
      | `toBitVec => true
      | _ => c == ``BitVec.ofBool
    if named then
      match args.back? with
      | some (.fvar id) => some id
      | _ => none
    else
      none
  | _, _ => none

/-! ## The solve -/

/-- What one solve attempt answered. The random searcher drives the same
entry point, so the answer type is the shared face. -/
inductive SolveAnswer where
  /-- A candidate assignment: manual terms, drawn containers, fixed
  coupled values, solved values. `abstracted` names the atoms the solver
  left opaque, when the model did not cover every equation; a candidate
  the check rejects was spurious, and the atoms say which lemma the
  formula missed. -/
  | solved (a : Assignment) (abstracted : Array String := #[])
  /-- The solver proved this fixed point's conjunction unsatisfiable. -/
  | unsat
  /-- The reflection or an evaluation failed; the answer is no answer. -/
  | stuck (detail : Option String := none)

/-- The candidate's bytes for every input, the layered assignment
(`layeredAssignment`, §9.4): the drawn bytes for the drawn containers,
which win over the manual terms, since on a manual line's failing disjunct
a draw replaces the author's choice (§9.4); then the manual terms' bytes
from the probe, the fixed and solved scalars from their kinds, and the
zero scalar for what neither touched. The `.fail` edge states the
searcher's precondition: the `applies` gate admits a theorem whose every
uncovered input is a scalar, so only scalar positions reach the fill, and
a container left behind answers `none` and the point is stuck. -/
private def buildAssignment (ctx : SearchCtx) (stmt : Statement)
    (drawn : Array (Nat × ByteArray)) (fixed solved : Array (Nat × Nat)) :
    MetaM (Option Assignment) :=
  layeredAssignment stmt drawn ctx.probe.manuals (fixed ++ solved) .fail

/-- One solve attempt at one substitution state: substitute the manual
terms, the drawn containers, and the fixed coupled values, unfold (§8.1),
evaluate the closed reads, and pose the negated conjunction to the
solver (§9.4).
`hyps` carries the disjunct's conjunctions' parts, already read-substituted
when the caller grounds container reads (§9.4's random searcher).
`fixedVals` carries the same positions as `fixed` with the values the
terms spell, so the candidate names what the formula was solved against.
`unfold` runs §8.1's pass: the manual handoff needs it, because a manual
term is a spec call whose equations expose the arithmetic; the random
searcher skips it, because its reads grounding already replaced the calls
with literals and a second unfold over a drawn state's hypotheses would
burn the run's budget per grid point. When the grounding leaves no free
scalar in the formula, the candidate goes to the probe's `check`, the
compiled `decide` of the disjunct's own conjunction, which answers without a
`Decidable` synthesis over the grounded form; `true` is the point's
witness and `false` its unsat (§9.3). -/
def solveOnce (ctx : SearchCtx) (stmt : Statement) (disjunctIndex : Nat)
    (unfold : Bool) (disjunctHyps : Array Expr) (drawn : Array (Nat × ByteArray))
    (fixed : Array (Nat × Expr)) (fixedVals : Array (Nat × Nat)) :
    MetaM SolveAnswer := do
  -- §9.4, from the stage-4 outcome: a fixed point whose reads run past a
  -- container's end is skipped before the grounding evaluates them, the
  -- same rule the random searcher's points follow; the compiled evaluation
  -- of a manual read never sees an out-of-range index
  match ← buildAssignment ctx stmt drawn fixedVals #[] with
    | some gateBytes =>
      unless (ctx.probe.safe disjunctIndex gateBytes).all (· == true) do
        return .stuck (some "a read is out of range at this fixed point")
    | none => pure ()
  let taken := (ctx.manualTerms.map (·.1)) ++ (drawn.map (·.1)) ++
    (fixed.map (·.1))
  let free : Array Nat :=
    (Array.range stmt.inputs.size).filter (fun i => !taken.contains i)
  -- the instance substitution (§11.2): the preset's constants for the
  -- telescope's instance variables, which the manual terms and the reads
  -- carry
  let instSub (e : Expr) : Expr :=
    e.replace fun s =>
      match s with
      | .fvar id =>
        ctx.instFvars.findIdx? (fun g => g.fvarId! == id)
          |>.map (fun i => mkConst ctx.instConsts[i]!)
      | _ => none
  -- the free scalars' types carry the substitution too: a type such as
  -- `Fin (3 * slotsPerEpoch)` names an instance variable the goal's fresh
  -- context does not hold (§9.4). A free `Fin n` input stands in as a
  -- `UInt64` with the bound `u < n` (§9.4): the solver's fragment takes
  -- the integer, and the bound keeps the model in range
  let finBounds : Array (Nat × Expr) ← free.filterMapM fun i => do
    match ← scalarKind (instSub (stmt.inputs[i]!.type)) with
    | some (.fin n) => pure (some (i, instSub n))
    | _ => pure none
  let finPos : Array Nat := finBounds.map (·.1)
  let freeTys := free.map fun i =>
    if finPos.contains i then mkConst ``UInt64 []
    else instSub (stmt.inputs[i]!.type)
  withFreshScalars freeTys fun fresh => do
    let ltUInt64 ← Meta.synthInstance
      (mkApp (.const ``LT [levelZero]) (.const ``UInt64 []))
    -- the stand-ins' bounds: `u < n`, in the stand-ins' `free`-aligned
    -- order
    let bounds : Array Expr ←
      ((free.zip fresh).filter fun (i, _) => finPos.contains i).filterMapM
        fun (i, u) => do
          let some n := (finBounds.find? fun (p, _) => p == i).map (·.2)
            | pure none
          let bound0 := mkAppN (.const ``LT.lt [levelZero])
            #[.const ``UInt64 [], ltUInt64, u,
              mkApp (.const ``UInt64.ofNat []) n]
          eliminateReads (fresh.map (·.fvarId!)) instSub bound0
    -- the substitution the formula reads: a manual term the draw
    -- replaced leaves, since the candidate carries the drawn bytes and
    -- the leftover subterm must ground at the draw, not at the author's
    -- term; then the fixed coupled scalars; then the non-`Fin` free
    -- scalars, whose stand-ins the substitution writes in directly (a
    -- `Fin` input's own variable stays, and its `Fin.val` reads rewrite
    -- to the stand-in below)
    let sub : Array (FVarId × Expr) :=
      (((ctx.manualTerms.filter fun (pos, _) =>
            !(drawn.any fun (p, _) => p == pos)) ++
          fixed).filterMap fun (pos, t) => do
            let f ← ctx.inputFvars[pos]?
            some (f.fvarId!, t)) ++
        ((free.zip fresh).filter fun (i, _) => !finPos.contains i).map
          fun (i, f) => (ctx.inputFvars[i]!.fvarId!, f)
    let freeIds := fresh.map (·.fvarId!)
    -- `Fin.val i` reads rewrite to the stand-in (§9.4). The corpus states
    -- its `Fin` bounds at the `Nat` level (`1 < i.val`), and the solver's
    -- fragment takes `UInt64` comparisons alone, so a `Nat`-form
    -- comparison over one `Fin.val` side bridges to the stand-in's
    -- `UInt64` form at the same time; the other side must be closed, and
    -- a comparison the bridge cannot express stays for an honest
    -- reflection failure. The closed side's `UInt64.ofNat` truncates a
    -- `Nat` bound at or above `2 ^ 64`; the corpus's `Fin` bounds are
    -- small, and a truncated bound would show as a false `unsat`.
    let ofNatT (x : Expr) : Expr := mkApp (.const ``UInt64.ofNat []) x
    -- the stand-in of one `Fin` input: `fresh` aligns with `free`, so the
    -- lookup walks the pair, never the `Fin`-only positions
    let finU (id : FVarId) : Option Expr :=
      ((free.zip fresh).find? fun (p, _) =>
        ctx.inputFvars[p]!.fvarId! == id).map (·.2)
    let uint64Ty := .const ``UInt64 []
    let finFvarIds : Array FVarId :=
      finPos.map (fun p => ctx.inputFvars[p]!.fvarId!)
    -- `@Fin.val n i`'s own variable: the app spine carries the width
    -- first, the variable second
    let finValOf? (t : Expr) : Option FVarId :=
      if t.isAppOf ``Fin.val then
        t.getAppArgs[1]?.bind (·.fvarId?)
      else none
    let mkCmp (head : Name) (a b : Expr) : MetaM (Option Expr) := do
      -- the rebuilt comparison is `UInt64`-typed, so a `Nat`-level head
      -- becomes its `LT` / `LE` reading
      let head := if head == ``Nat.lt then ``LT.lt else
        if head == ``Nat.le then ``LE.le else head
      if head == ``Eq then
        return some (mkAppN (.const ``Eq [levelOne]) #[uint64Ty, a, b])
      let inst ← Meta.synthInstance
        (mkApp (.const (if head == ``LE.le then ``LE else ``LT) [levelZero])
          uint64Ty)
      return some (mkAppN (.const head [levelZero]) #[uint64Ty, inst, a, b])
    let rec bridgeFinCmp (e : Expr) : MetaM (Option Expr) := do
      let fn := e.getAppFn
      match fn with
      | .const c _ =>
        unless c == ``LT.lt || c == ``LE.le || c == ``Eq ||
            c == ``Nat.lt || c == ``Nat.le do
          return none
        let args := e.getAppArgs
        -- `@LT.lt Nat inst x y` carries the type as the first argument;
        -- `Nat.lt x y` carries none
        unless args.size ≥ 2 do
          return none
        unless c == ``Nat.lt || c == ``Nat.le ||
            args[0]! == .const ``Nat [] do
          return none
        let x := args[args.size - 2]!
        let y := args[args.size - 1]!
        match finValOf? x, finValOf? y with
        | none, some fid =>
          let some u := finU fid | return none
          if (collectFVarIds x #[]).any finFvarIds.contains then return none
          mkCmp c (ofNatT x) u
        | some fid, none =>
          let some u := finU fid | return none
          if (collectFVarIds y #[]).any finFvarIds.contains then return none
          mkCmp c u (ofNatT y)
        | _, _ => return none
      | _ => return none
    let rec rewFin (e : Expr) : MetaM Expr := do
      match ← bridgeFinCmp e with
      | some e' => return e'
      | none =>
        match e with
        | .app f a => return .app (← rewFin f) (← rewFin a)
        | .lam n t b bi => return .lam n (← rewFin t) (← rewFin b) bi
        | .letE n t v b bi =>
          return .letE n (← rewFin t) (← rewFin v) (← rewFin b) bi
        | .mdata m b => return .mdata m (← rewFin b)
        | .proj s i b => return .proj s i (← rewFin b)
        -- a bare `Fin.val` read outside a bridged comparison stays, and
        -- the reflection's honest failure reports it
        | _ => return e
    let mut hyps : Array Expr := #[]
    for h in disjunctHyps do
      -- ground the closed reads first, so the unfold sees arithmetic and
      -- not a spec call whose equations would unfold into a fold (§9.4),
      -- then ground the preset constants the unfold exposes
      let h0 ← rewFin (instSub (substFvars h sub))
      let h1 ← eliminateReads freeIds instSub h0
      let h2 ← if unfold then Prepare.unfoldHyp h1 else pure h1
      hyps := hyps.push (← eliminateReads freeIds instSub h2)
    -- the solver's fragment carries no `True`: a conjunct the unfold
    -- trivialized drops here, so the goal's shape stays in the fragment
    let hypsLive := hyps.filter (· != .const ``True [])
    let conj := conjunction hypsLive
    -- the grounding may close the formula even when free inputs remain
    -- (a disjunct that mentions none of them): the candidate then goes
    -- to the probe's `check`, the compiled `decide` of the disjunct's own
    -- conjunction at these bytes. `true` is the point's witness and
    -- `false` its unsat; a `Decidable` synthesis over the grounded form
    -- would whnf a large prop per point, which is the search's own
    -- budget burn (§9.3, §9.4)
    if !(collectFVarIds conj #[]).any freeIds.contains then
      match ← buildAssignment ctx stmt drawn fixedVals #[] with
      | some a =>
        if ctx.probe.check disjunctIndex a then return .solved a
        else return .unsat
      | none => return .stuck none
    -- the goal's context holds the fresh scalars alone: bv_decide's
    -- reflection takes every hypothesis of the goal's context, and the
    -- reader telescope's own hypotheses are the un-substituted forms the
    -- goal must not see (§9.4 poses `¬P` and nothing else). The `Fin`
    -- stand-ins' bounds sit inside the conjunction, as conjuncts: the
    -- preprocessor normalizes the goal's own formula, and a bound that
    -- lived in the context would reify as an unconnected `Bool` atom,
    -- leaving the stand-in unbounded (§9.4).
    let conjFull := conjunction (hypsLive ++ bounds)
    let decls ← fresh.mapM Meta.getFVarLocalDecl
    let lctx := decls.foldl (init := {}) fun l d => l.addDecl d
    let g ← Meta.mkFreshExprMVarAt lctx {} (mkNot conjFull)
    let answer? ← try
      some <$> bvDecideCore g.mvarId!
    catch _ => pure none
    match answer? with
    | some (.error ce) =>
      let mut solvedVals : Array (Nat × Nat) := #[]
      let mut abstracted : Array String := #[]
      for (atom, packed) in ce.equations do
        match unwrapAtom atom with
        | some fid =>
          match fresh.findIdx? (fun f => f.fvarId! == fid) with
          | some i => solvedVals := solvedVals.push (free[i]!, packed.bv.toNat)
          | none =>
            -- an atom over no free scalar stayed opaque: the formula was
            -- missing a lemma for it, and the report names it
            abstracted := abstracted.push (toString (← Meta.ppExpr atom))
        | none =>
          abstracted := abstracted.push (toString (← Meta.ppExpr atom))
      match ← buildAssignment ctx stmt drawn fixedVals solvedVals with
      | some a => return .solved a abstracted
      | none => return .stuck none
    | some (.ok _) => return .unsat
    | none => return .stuck none

/-- The scalars a manual subterm computes over: the free scalars inside the
topmost manual-mentioning subterm of `e`, where the logical and comparison
connectives stay transparent. `bidAmount ≤ builders[i]!.balance - min`
names `builderIndex` this way (it sits inside the subtraction over the
manual state) and leaves `bidAmount` free for the solver, because
`bidAmount` is a comparison operand, not a read index. The random searcher
runs the same walk over its drawn containers (§9.4). -/
partial def topManualScalarIds (manualIds : Array FVarId) (e : Expr)
    (acc : Array FVarId) : Array FVarId :=
  let isConnective : Bool :=
    match e.getAppFn with
    | .const c _ =>
      c == ``And || c == ``Or || c == ``Not || c == ``Eq || c == ``Iff ||
      c == ``Ne || c == ``LT.lt || c == ``LE.le || c == ``GT.gt || c == ``GE.ge
    | _ => false
  if !((collectFVarIds e #[]).any manualIds.contains) then
    acc
  else if isConnective then
    e.getAppArgs.foldl (fun acc a => topManualScalarIds manualIds a acc) acc
  else
    (collectFVarIds e #[]).foldl (fun acc id =>
      if acc.contains id then acc else acc.push id) acc

/-- The coupled scalars' grid: the product of each coupled position's
values, capped so the searcher stays bounded (§9.4's handoff). Every
coupled scalar stays in every point: the cap truncates after each fold,
so a cut grid explores the earlier scalars' low values across the later
scalars' low values. `valuesCap` bounds each scalar's values from above
when the containers in play are known to be drawn (`randomSize`, §9.4);
`0` means no bound, the manual handoff's situation, where the manual
containers are the author's. -/
def coupledGrid (kinds : Array (Option ScalarKind)) (coupled : Array Nat)
    (valuesCap : Nat) : MetaM (Array (Array (Nat × Nat))) := do
  let mut acc : Array (Array (Nat × Nat)) := #[#[]]
  for i in coupled do
    let vals ← match kinds[i]? with
      | some (some k) => gridValues k
      | _ => pure (Array.range gridValuesPerScalar)
    let vals := if valuesCap == 0 then vals
      else vals.filter (· < valuesCap)
    acc := (acc.flatMap fun c => vals.map (fun v => c.push (i, v))).take gridPointCap
  return acc

/-- The no-literal-form message: a coupled scalar the grid fixed to a
value whose literal term the substitution cannot write (a `Fin` whose
bound does not reduce, §9.4). -/
private def literalDetail (stmt : Statement) (position : Nat) : String :=
  s!"input {stmt.inputs[position]!.name} has no literal form for the \
    coupled grid (§9.4)"

/-- The bit-vector searcher (§9.4). Applies to a theorem without block
inputs; the search answers `nothing` when the residual inputs carry a
container the manual terms do not fix. -/
def bitVecSearcher : WitnessSearcher where
  tag := .bitVec
  applies _ stmt _ := stmt.blockInputs.isEmpty
  search ctx stmt d := do
    let manualPos := ctx.manualTerms.map (·.1)
    let residual : Array Nat :=
      (Array.range stmt.inputs.size).filter (fun i => !manualPos.contains i)
    -- one kind per input position, `none` for a manual or container
    -- input; the statement's own table, the reader computed once (§9.4)
    let kinds : Array (Option ScalarKind) :=
      (Array.range stmt.inputs.size).map fun i =>
        if manualPos.contains i then none else stmt.scalarKinds[i]? |>.join
    let residualKinds := residual.filterMap (fun i => kinds[i]?)
    unless residualKinds.all (·.isSome) do
      -- a residual container input: no bit-vector solve
      return .nothing
    -- §9.4: the coupled scalars sit inside a computation over a manual
    -- input (a read index); the comparison operands stay free
    let manualIds := ctx.manualTerms.filterMap fun (pos, _) => do
      let f ← ctx.inputFvars[pos]?
      some f.fvarId!
    let inner : Array FVarId :=
      d.hyps.foldl (fun acc h => topManualScalarIds manualIds h acc) #[]
    let coupled := residual.filter (fun i =>
      inner.contains (ctx.inputFvars[i]!.fvarId!))
    if coupled.isEmpty && ctx.manualTerms.isEmpty then
      -- the pure scalar solve: every input is a free scalar and no
      -- manual term stands in the formula, so a solver proof of `¬P` is
      -- the disjunct's `unsat` (§9.4). A manual theorem never takes this
      -- branch: its reads hold the manual terms' values, so an `unsat`
      -- there is a fact about one manual term, and the grid below
      -- answers `nothing` for it.
      match ← solveOnce ctx stmt d.index true d.hyps #[] #[] #[] with
      | .solved a abstracted =>
        -- the loop's check is the single arbiter (§9.3); a rejected
        -- candidate was a spurious model, and the abstracted atoms name
        -- the lemma the formula missed (§9.4)
        if ctx.probe.check d.index a then
          return .candidate a
        return .nothing
          (if abstracted.isEmpty then none
           else some (String.intercalate "; " abstracted.toList))
      | .unsat => return .unsat
      | .stuck detail => return .nothing detail
    -- §9.4's handoff: the manual terms fix the containers, the coupled
    -- scalars walk the grid, the solver takes the rest. A per-grid-point
    -- `unsat` is not the disjunct's answer; another point may satisfy it.
    let mut details : Array String := #[]
    for fixedStx in ← coupledGrid kinds coupled 0 do
      let mut fixed : Array (Nat × Expr) := #[]
      let mut fixable := true
      for (i, v) in fixedStx do
        match ← literalTerm stmt.inputs[i]!.type v with
        | some t => fixed := fixed.push (i, t)
        | none =>
          -- a coupled scalar whose type has no literal form
          let note := literalDetail stmt i
          unless details.contains note do
            details := details.push note
          fixable := false
      if fixable then
        match ← solveOnce ctx stmt d.index true d.hyps #[] fixed fixedStx with
        | .solved a abstracted =>
          -- the loop's check is the single arbiter (§9.3); a rejected
          -- candidate sends the walk to the next grid point, and the
          -- atoms the solver abstracted name the missing lemma (§9.4)
          if ctx.probe.check d.index a then
            return .candidate a
          details := details ++ abstracted
        | .unsat => pure ()
        | .stuck _ => pure ()
    return .nothing
      (if details.isEmpty then none
       else some (String.intercalate "; " details.toList))

end EthCLLib.TheoremVectors
