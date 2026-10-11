import Lean
import Lean.Elab.Tactic.BVDecide
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source

/-!
# `EthCLLib.TheoremVectors.Witness.BitVec`: the bit-vector source

The solver-backed witness source (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4). The source
poses the case's negated conjunction as a goal and calls `bvDecide'` from
`Lean.Elab.Tactic.BVDecide.Frontend`. A `Result` proves `¬P`, so the case is
vacuous and the source answers `unsat`; no later source can find what does
not exist. A `CounterExample` is a model of `P`: its equations pair the
solver's atoms with values, the reader unwraps the `UIntX.toBitVec` /
`BitVec.ofBool` wrappers, and the values become the scalar inputs of a
candidate the loop's check still decides.

Two forms of the handoff live here:

- **Pure scalar.** Every input scalar and no seeds: the prepared hypotheses
  go to the solver as they are.
- **The seed handoff.** A line whose seeds fix the container inputs leaves
  scalar inputs, and the prepared hypotheses still name the seeded values
  (`coverBidState.builders[builderIndex]!.balance`). The source fixes each
  *coupled* scalar, one that co-occurs with a seeded input, over a bounded
  value grid. At each fixed point the seeded reads become closed terms of
  scalar type, the source evaluates them in compiled code and substitutes
  the literals, and the solver takes the remaining free scalars. The grid
  holds the small values a scalar index into a seeded container takes in
  practice (the builder index of `canBuilderCoverBid_iff` among them); a
  scalar the grid misses falls to a later source or to the random source's
  stage. The check stays the single arbiter throughout: a candidate from
  any fixed point counts only when the compiled `decide` accepts it, and a
  per-fixed-point `unsat` never reports the case vacuous, because another
  grid point may satisfy it.

## Lean idioms annotated

- `Frontend.bvDecide'` creates auxiliary declarations and compiles them, so
  it runs only through the compiled implementation behind
  `@[implemented_by]`, the same shape `Command.lean`'s `evalConst` uses;
  the `opaque` face is what interpreted code sees.
- `mkFreshExprMVar` inside `withLocalDeclD` gives the goal the free scalars
  as its local context, which is what `bv_decide`'s reflection and its
  counterexample equations name.
- `Expr.replace` with a `none`-returning function is a bottom-up rewrite:
  the instance substitution below rewrites only the free variables it
  knows and leaves every other node to the recursion.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## The solver call (§9.4) -/

/-- The `bvDecide'` call behind the compiled face below. `TacticContext.new`
is `TermElabM` and the source runs in `MetaM`, so the context is built here
with core's fresh names and the same cadical lookup `TacticContext.new`
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

@[implemented_by evalNatImpl] private opaque evalNatOp (e : Expr) : MetaM Nat

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

/-! ## Scalar analysis -/

/-- The scalar shape of an input type, after the reducible aliases
(`Slot`, `Gwei`, and the other SSZ aliases) reduce. -/
private inductive ScalarKind where
  | bool
  | nat
  | uint (width : Nat)
  | fin (n : Expr)

/-- The scalar kind of a type, `none` for everything the solver's wire form
does not cover. -/
private def scalarKind (ty : Expr) : MetaM (Option ScalarKind) := do
  let t ← Meta.withReducible (Meta.whnf ty)
  match t with
  | .const c _ =>
    match c with
    | ``Bool   => return some .bool
    | ``Nat    => return some .nat
    | ``UInt64 => return some (.uint 64)
    | ``UInt32 => return some (.uint 32)
    | ``UInt16 => return some (.uint 16)
    | ``UInt8  => return some (.uint 8)
    | _        => return none
  | .app (.const ``Fin _) n => return some (.fin n)
  | _ => return none

/-- The values one coupled scalar walks in the grid (§9.4): the small values
a scalar index into a seeded container takes in practice. -/
def gridValuesPerScalar : Nat := 64

/-- The grid's point cap (§9.4): the most fixed points one case's handoff
walks. -/
def gridPointCap : Nat := 128

/-- The values one coupled scalar walks in the grid: the small values a
scalar index into a seeded container takes in practice. -/
private def gridValues (k : ScalarKind) : MetaM (Array Nat) := do
  match k with
  | .bool => pure #[0, 1]
  | .uint _ | .nat => pure (Array.range gridValuesPerScalar)
  | .fin n => do
    let nVal ← try evalNatOp n catch _ => pure 0
    pure (Array.range (min nVal gridValuesPerScalar))

/-- The little-endian `uintN` bytes of `v` at byte width `w`, the SSZ wire
form of the scalar family (§9.4's "serialization of each value to its SSZ
width"). -/
private def leBytes (w : Nat) (v : Nat) : ByteArray :=
  ByteArray.mk ((Array.range w).map fun i =>
    UInt8.ofNat ((v / 2 ^ (8 * i)) % 256))

/-- The SSZ bytes of one scalar value at its input type (§9.4). -/
private def scalarBytes (k : ScalarKind) (v : Nat) : ByteArray :=
  match k with
  | .bool => leBytes 1 (v % 2)
  | .nat | .uint 64 => leBytes 8 v
  | .uint 32 => leBytes 4 v
  | .uint 16 => leBytes 2 v
  | .uint 8 => leBytes 1 v
  | .uint _ => leBytes 8 v
  | .fin _ => leBytes 8 v

/-- The literal term of one scalar value at its input type: the form a
coupled scalar takes when the source fixes it in the hypotheses. `none`
when the type has no literal form the substitution can write. -/
private def literalTerm (ty : Expr) (v : Nat) : MetaM (Option Expr) := do
  match ← scalarKind ty with
  | some .bool => return some (.const (if v == 0 then ``Bool.false else ``Bool.true) [])
  | some .nat => return some (mkRawNatLit v)
  | some (.uint _) =>
    let lit := mkRawNatLit v
    let inst? ← try
      some <$> Meta.synthInstance
        (mkAppN (.const ``OfNat [levelZero]) #[ty, lit])
    catch _ =>
      pure none
    match inst? with
    | some inst => return some (mkAppN (.const ``OfNat.ofNat [levelZero]) #[ty, lit, inst])
    | none => return none
  | _ => return none

/-! ## The term walk -/

/-- Every fvar id in `e`, each once. -/
private partial def collectFVarIds (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar id => if acc.contains id then acc else acc.push id
  | .app f a => collectFVarIds a (collectFVarIds f acc)
  | .lam _ t b _ => collectFVarIds b (collectFVarIds t acc)
  | .letE _ t v b _ => collectFVarIds b (collectFVarIds v (collectFVarIds t acc))
  | .forallE _ t b _ => collectFVarIds b (collectFVarIds t acc)
  | .mdata _ b => collectFVarIds b acc
  | .proj _ _ b => collectFVarIds b acc
  | _ => acc

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
(§9.4's read substitution). Seeded reads
(`coverBidState.builders[0]!.balance`), preset constants
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
    -- a term under a lambda carries loose bound variables, which no
    -- compiled evaluation can run; the caller descends into it instead
    if ids.any freeIds.contains || e.hasLooseBVars then
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

/-- What one solve attempt answered. -/
private inductive SolveAnswer where
  /-- A candidate assignment: seeds, fixed coupled values, solved values.
  `abstracted` names the atoms the solver left opaque, when the model did
  not cover every equation; a candidate the check rejects was spurious, and
  the atoms say which lemma the formula missed. -/
  | solved (a : Assignment) (abstracted : Array String := #[])
  /-- The solver proved this fixed point's conjunction unsatisfiable. -/
  | unsat
  /-- The reflection or an evaluation failed; the answer is no answer. -/
  | stuck (detail : Option String := none)

/-- The candidate's bytes for every input: the seeds' bytes from the probe
for the seeded positions, the fixed and solved scalars from their kinds,
and the zero scalar for what neither touched. -/
private def buildAssignment (ctx : SearchCtx) (stmt : Statement)
    (fixed solved : Array (Nat × Nat)) : MetaM (Option Assignment) := do
  let chosen := fixed ++ solved
  let mut a : Array ByteArray := #[]
  for i in [0:stmt.inputs.size] do
    match ctx.probe.seeds.find? fun (p, _) => p == i with
    | some (_, b) => a := a.push b
    | none =>
      let ty := stmt.inputs[i]!.type
      match ← scalarKind ty with
      | none => return none
      | some k =>
        let v := (chosen.find? fun (p, _) => p == i).map (·.2) |>.getD 0
        a := a.push (scalarBytes k v)
  return some a

/-- One solve attempt at one substitution state: substitute the seeds and
the fixed coupled values, unfold (§8.1), evaluate the seeded reads, and
pose the negated conjunction to the solver (§9.4). `fixedVals` carries the
same positions as `fixed` with the values the terms spell, so the
candidate names what the formula was solved against. When the grounding
leaves no free scalar in the formula, the conjunction decides without the
solver. If the decision itself fails, the candidate goes to the loop's
check unevaluated when every input is seeded or fixed; otherwise the
answer is no answer (§9.3). -/
private def solveOnce (ctx : SearchCtx) (stmt : Statement) (c : Case)
    (fixed : Array (Nat × Expr)) (fixedVals : Array (Nat × Nat)) :
    MetaM SolveAnswer := do
  let taken := (ctx.seedTerms.map (·.1)) ++ (fixed.map (·.1))
  let free : Array Nat :=
    (Array.range stmt.inputs.size).filter (fun i => !taken.contains i)
  -- the instance substitution (§11.2): the preset's constants for the
  -- telescope's instance variables, which the seeded terms and the reads
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
  -- context does not hold (§9.4)
  let freeTys := free.map (fun i => instSub (stmt.inputs[i]!.type))
  withFreshScalars freeTys fun fresh => do
    let sub : Array (FVarId × Expr) :=
      ((ctx.seedTerms ++ fixed).filterMap fun (pos, t) => do
          let f ← ctx.inputFvars[pos]?
          some (f.fvarId!, t)) ++
        (free.zip fresh).map fun (i, f) => (ctx.inputFvars[i]!.fvarId!, f)
    let freeIds := fresh.map (·.fvarId!)
    let mut hyps : Array Expr := #[]
    for h in c.hyps do
      -- ground the closed reads first, so the unfold sees arithmetic and
      -- not a spec call whose equations would unfold into a fold (§9.4),
      -- then ground the preset constants the unfold exposes
      let h0 := instSub (substFvars h sub)
      let h1 ← eliminateReads freeIds instSub h0
      let h2 ← Prepare.unfoldHyp h1
      hyps := hyps.push (← eliminateReads freeIds instSub h2)
    let conj := conjunction hyps
    -- the grounding may close the formula even when free inputs remain
    -- (a disjunct that mentions none of them): the goal then decides
    -- without a solver, and bv_decide refuses an atom-free goal (§9.4).
    -- A synthesis or an evaluation failure falls back to the candidate
    -- and the loop's check when no free scalar remains (§9.3); the
    -- original conjunction's `Decidable` instance, which the prepare pass
    -- built (§8.4), decides there.
    if !(collectFVarIds conj #[]).any freeIds.contains then
      let decided? : Option Bool ← try
        let dec ← Meta.synthInstance (mkApp (.const ``Decidable []) conj)
        some <$> evalBoolOp (mkAppN (.const ``Decidable.decide []) #[conj, dec])
      catch _ => pure none
      match decided? with
      | some true =>
        match ← buildAssignment ctx stmt fixedVals #[] with
        | some a => return .solved a
        | none => return .stuck none
      | some false => return .unsat
      | none =>
        -- the candidate and the loop's check answer when every input is
        -- seeded or fixed; otherwise the answer is no answer
        if free.isEmpty then
          match ← buildAssignment ctx stmt fixedVals #[] with
          | some a => return .solved a
          | none => return .stuck none
        return .stuck none
    -- the goal's context holds the fresh scalars alone: bv_decide's
    -- reflection takes every hypothesis of the goal's context, and the
    -- reader telescope's own hypotheses are the un-substituted forms the
    -- goal must not see (§9.4 poses `¬P` and nothing else)
    let decls ← fresh.mapM Meta.getFVarLocalDecl
    let lctx := decls.foldl (init := {}) fun l d => l.addDecl d
    let g ← Meta.mkFreshExprMVarAt lctx {} (mkNot conj)
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
      match ← buildAssignment ctx stmt fixedVals solvedVals with
      | some a => return .solved a abstracted
      | none => return .stuck none
    | some (.ok _) => return .unsat
    | none => return .stuck none

/-- The scalars a seeded subterm computes over: the free scalars inside the
topmost seeded-mentioning subterm of `e`, where the logical and comparison
connectives stay transparent. `bidAmount ≤ builders[i]!.balance - min`
names `builderIndex` this way (it sits inside the subtraction over the
seeded state) and leaves `bidAmount` free for the solver, because
`bidAmount` is a comparison operand, not a read index. -/
private partial def topSeededScalarIds (seededIds : Array FVarId) (e : Expr)
    (acc : Array FVarId) : Array FVarId :=
  let isConnective : Bool :=
    match e.getAppFn with
    | .const c _ =>
      c == ``And || c == ``Or || c == ``Not || c == ``Eq || c == ``Iff ||
      c == ``Ne || c == ``LT.lt || c == ``LE.le || c == ``GT.gt || c == ``GE.ge
    | _ => false
  if !((collectFVarIds e #[]).any seededIds.contains) then
    acc
  else if isConnective then
    e.getAppArgs.foldl (fun acc a => topSeededScalarIds seededIds a acc) acc
  else
    (collectFVarIds e #[]).foldl (fun acc id =>
      if acc.contains id then acc else acc.push id) acc

/-- The coupled scalars' grid: the product of each coupled position's
values, capped so the source stays bounded (§9.4's handoff). Every
coupled scalar stays in every point: the cap truncates after each fold,
so a cut grid explores the earlier scalars' low values across the later
scalars' low values. -/
private def coupledGrid (kinds : Array (Option ScalarKind)) (coupled : Array Nat) :
    MetaM (Array (Array (Nat × Nat))) := do
  let mut acc : Array (Array (Nat × Nat)) := #[#[]]
  for i in coupled do
    let vals ← match kinds[i]? with
      | some (some k) => gridValues k
      | _ => pure (Array.range gridValuesPerScalar)
    acc := (acc.flatMap fun c => vals.map (fun v => c.push (i, v))).take gridPointCap
  return acc

/-- The `Fin n` message of §9.4: the solver's domain stages the bridge in
stage 4, and until then the source names the input instead of failing the
reflection silently. -/
private def finDetail (stmt : Statement) (positions : Array Nat) : String :=
  let names := String.intercalate ", "
    (positions.toList.map (fun i => stmt.inputs[i]!.name.toString))
  s!"input {names} has a `Fin` type, which the solver does not take yet \
    (§9.4; stage 4 carries the bridge)"

/-- The bit-vector source (§9.4). Applies to a theorem without block
inputs; the search answers `nothing` when the residual inputs carry a
container the seeds do not fix. -/
def bitVecSource : WitnessSource where
  tag := .bitVec
  applies _ stmt _ := stmt.blockInputs.isEmpty
  search ctx stmt c := do
    let seededPos := ctx.seedTerms.map (·.1)
    let residual : Array Nat :=
      (Array.range stmt.inputs.size).filter (fun i => !seededPos.contains i)
    -- one kind per input position, `none` for a seeded or container input
    let kinds : Array (Option ScalarKind) ←
      (Array.range stmt.inputs.size).mapM fun i =>
        if seededPos.contains i then pure none
        else scalarKind stmt.inputs[i]!.type
    let residualKinds := residual.filterMap (fun i => kinds[i]?)
    unless residualKinds.all (·.isSome) do
      -- a residual container input: no bit-vector solve
      return .nothing
    -- §9.4 stages the `Fin n` bridge; the input reports itself instead of
    -- failing the reflection into a silent `stuck`
    let fins := residual.filter fun i =>
      match kinds[i]? with
      | some (some (.fin _)) => true
      | _ => false
    if !fins.isEmpty then
      return .nothing (some (finDetail stmt fins))
    -- §9.4: the coupled scalars sit inside a computation over a seeded
    -- input (a read index); the comparison operands stay free
    let seededIds := ctx.seedTerms.filterMap fun (pos, _) => do
      let f ← ctx.inputFvars[pos]?
      some f.fvarId!
    let inner : Array FVarId :=
      c.hyps.foldl (fun acc h => topSeededScalarIds seededIds h acc) #[]
    let coupled := residual.filter (fun i =>
      inner.contains (ctx.inputFvars[i]!.fvarId!))
    if coupled.isEmpty && ctx.seedTerms.isEmpty then
      -- the pure scalar solve: every input is a free scalar and no seed
      -- stands in the formula, so a solver proof of `¬P` is the case's
      -- `unsat` (§9.4). A seeded theorem never takes this branch: its
      -- reads hold the seed's values, so an `unsat` there is a fact about
      -- one seed, and the grid below answers `nothing` for it.
      match ← solveOnce ctx stmt c #[] #[] with
      | .solved a abstracted =>
        -- the loop's check is the single arbiter (§9.3); a rejected
        -- candidate was a spurious model, and the abstracted atoms name
        -- the lemma the formula missed (§9.4)
        if ctx.probe.check c.index a then
          return .candidate a
        return .nothing
          (if abstracted.isEmpty then none
           else some (String.intercalate "; " abstracted.toList))
      | .unsat => return .unsat
      | .stuck detail => return .nothing detail
    -- §9.4's handoff: the seeds fix the containers, the coupled scalars
    -- walk the grid, the solver takes the rest. A per-grid-point `unsat`
    -- is not the case's answer; another point may satisfy it.
    let mut details : Array String := #[]
    for fixedStx in ← coupledGrid kinds coupled do
      let mut fixed : Array (Nat × Expr) := #[]
      let mut fixable := true
      for (i, v) in fixedStx do
        match ← literalTerm stmt.inputs[i]!.type v with
        | some t => fixed := fixed.push (i, t)
        | none =>
          -- a coupled scalar whose type has no literal form yet
          let note := finDetail stmt #[i]
          unless details.contains note do
            details := details.push note
          fixable := false
      if fixable then
        match ← solveOnce ctx stmt c fixed fixedStx with
        | .solved a abstracted =>
          -- the loop's check is the single arbiter (§9.3); a rejected
          -- candidate sends the walk to the next grid point, and the
          -- atoms the solver abstracted name the missing lemma (§9.4)
          if ctx.probe.check c.index a then
            return .candidate a
          details := details ++ abstracted
        | .unsat => pure ()
        | .stuck _ => pure ()
    return .nothing
      (if details.isEmpty then none
       else some (String.intercalate "; " details.toList))

end EthCLLib.TheoremVectors
