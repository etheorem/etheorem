import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.BitVec

/-!
# `EthCLLib.TheoremVectors.Witness.Random`: the random-plus-solve source

The random source of §9.4: draw the container inputs with their
`SampleableExt` instances (§9.5), ground the case's container reads at the
draw, and hand the residual formula over the scalar inputs to the solver.
The loop redraws up to `theorem_vectors.randomDraws` times when a draw
fails the case, and answers `nothing` when every draw fails: a per-draw
`unsat` is a fact about that draw, the same rule the seed handoff's grid
follows.

The grounding runs through the probe's `reads` face: the probe evaluates
the case's container-reading subterms at the candidate's bytes, and the
source substitutes the serialized values as literals, walking the same
plan `containerReads` produces. The scalars that sit inside a
container-reading subterm (`builders[builderIndex]!.balance`'s
`builderIndex`) are *coupled*: the seed handoff's walk names them, and
they fix over the value grid, so each read grounds at a known point and
the solver takes the remaining free scalars.

The source runs after the bit-vector source on every list, seeded lines
included (§9.2): on a case the seed fails, a draw beats no witness, and
the record's `source` names the one that won.

## Lean idioms annotated

- A draw's shapes are random, so a read can index a drawn container past
  its end (a `!`-read). Lean's panic answers the read with its type's
  default and prints to the build log; the grounded formula is then
  wrong, the point's candidate fails the check, and the loop moves on,
  so the misgrounding costs a wasted solve and a panic line, and no
  wrong vector passes. The grid walks its small values first and the
  drawn lists stay short, which bounds how often this fires.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- The reads' bytes at one solve point, layered like the candidate's own
overlay (`buildAssignment`): the drawn containers, then the probe's
seeds, then the coupled scalars at their grid values, then the zero
encodings. This is what the probe's `reads` decodes (§9.4). -/
private def readsBytesAt (ctx : SearchCtx) (stmt : Statement)
    (drawn : Array (Nat × ByteArray)) (fixedVals : Array (Nat × Nat)) :
    MetaM Assignment :=
  (Array.range stmt.inputs.size).mapM fun i =>
    match drawn.find? fun (p, _) => p == i with
    | some (_, b) => pure b
    | none =>
      match ctx.probe.seeds.find? fun (p, _) => p == i with
      | some (_, b) => pure b
      | none =>
        match fixedVals.find? fun (p, _) => p == i with
        | some (_, v) => do
          match ← scalarKind stmt.inputs[i]!.type with
          | some k => pure (scalarBytes k v)
          | none => pure (ctx.probe.defaults.getD i emptyBytes)
        | none => pure (ctx.probe.defaults.getD i emptyBytes)

/-- The serialized read values, substituted into the case's hypotheses as
literals (§9.4). The walk is `containerReads`, the same plan the probe's
`reads` face evaluated, so entry `k` pairs with subterm `k`. A `!`-read
past a drawn container's end answers its default instead of raising,
which misgrounds that one point, and the point's candidate fails the
check in `runPoint`. A read whose value's literal form the type does not
take leaves its subterm in the formula for the solver. The hypotheses
arrive zeta-reduced, the same form the walk saw. -/
private def substituteReads (ctx : SearchCtx) (c : Case)
    (plan : Array Expr) (bytes : Assignment) : MetaM (Array Expr) := do
  if plan.isEmpty then return c.hyps.map Prepare.zeta
  let rs := ctx.probe.reads c.index bytes
  if rs.size != plan.size then return c.hyps.map Prepare.zeta
  let mut lits : Array (Expr × Expr) := #[]
  for (r, b) in plan.zip rs do
    let ty ← Meta.inferType r
    match ← scalarKind ty with
    | none => pure ()
    | some k =>
      match scalarNatOf k b with
      | none => pure ()
      | some v =>
        match ← literalTerm ty v with
        | some lit => lits := lits.push (r, lit)
        | none => pure ()
  -- each plan entry is maximal, so no entry sits inside another
  pure (c.hyps.map fun h =>
    lits.foldl (fun acc (r, lit) =>
      acc.replace fun s => if s == r then some lit else none) (Prepare.zeta h))

/-- One solve point: ground the reads at the given bytes and hand the
residual to the solver. `some a` means the check accepted `a`; a
rejected candidate and a per-point `unsat` are the same no-answer
(§9.3), and a misgrounded read (§9.4's panic default) fails the check
with them. When the bytes already cover every input (a theorem whose
inputs are containers alone), the reads grounding and the solver have
nothing to do, and the point's answer is the check on the bytes
directly. The built source (§9.9) reaches it through `tryDraw` at each
grid step, with the built state in the `drawn` overlay. -/
private def runPoint (ctx : SearchCtx) (stmt : Statement) (c : Case)
    (plan : Array Expr) (drawn : Array (Nat × ByteArray))
    (fixed : Array (Nat × Expr)) (fixedVals : Array (Nat × Nat)) :
    MetaM (Option Assignment) := do
  let bytes ← readsBytesAt ctx stmt drawn fixedVals
  -- §9.4, from the stage-4 outcome: a point whose `!`-reads run past a
  -- drawn list's end is skipped before anything evaluates them, so no
  -- panic reaches compiled code and no wasted solve bills the budget
  unless (ctx.probe.safe c.index bytes).all (· == true) do
    return none
  let taken := (ctx.probe.seeds.map (·.1)) ++ (drawn.map (·.1)) ++
    (fixedVals.map (·.1))
  if !((Array.range stmt.inputs.size).any fun i => !taken.contains i) then
    -- the bytes are a complete assignment: the check is the answer
    if ctx.probe.check c.index bytes then pure (some bytes) else pure none
  else do
    let hyps ← substituteReads ctx c plan bytes
    let answer ← solveOnce ctx stmt c.index false hyps drawn fixed fixedVals
    match answer with
    | .solved a _ =>
      if ctx.probe.check c.index a then pure (some a) else pure none
    | _ => pure none

/-- One draw of the redraw loop (§9.4): walk the coupled scalars' grid
over the drawn containers, and hand each fixed point's residual to the
solver. A per-point `unsat` is a fact about the point, so the walk
continues, the seed handoff's rule; a point whose reads run past a drawn
list's end is skipped at the gate inside `runPoint`. `kinds` and
`coupled` come from the case alone and the caller computes them once. A
coupled scalar whose literal term the substitution cannot write makes
every grid point unfixable; the note names it, the same answer the
bit-vector source's `literalDetail` carries. The built source (§9.9)
drives this at each grid step with the built state as the one drawn
container, the same loop §9.9 names. -/
def tryDraw (ctx : SearchCtx) (stmt : Statement) (c : Case)
    (valuesCap : Nat) (containerIds : Array FVarId) (plan : Array Expr)
    (kinds : Array (Option ScalarKind)) (coupled : Array Nat)
    (drawn : Array (Nat × ByteArray)) : MetaM (Option Assignment) := do
  -- every container in play is drawn for the random source, and
  -- `drawBounded` caps a drawn list at `randomSize` elements, so a
  -- coupled scalar at or past that bound indexes out of range at every
  -- point of its grid: the random source caps the values there (§9.4).
  -- The built source's state is not drawn and its registries hold what
  -- the grid's knobs built, so it passes `0`, no cap, and the safe
  -- gate skips the points whose index runs past the built list
  if coupled.isEmpty then
    runPoint ctx stmt c plan drawn #[] #[]
  else do
    for fixedStx in ← coupledGrid kinds coupled valuesCap do
      let mut fixed : Array (Nat × Expr) := #[]
      let mut fixedVals : Array (Nat × Nat) := #[]
      let mut fixable := true
      for (i, v) in fixedStx do
        match ← literalTerm stmt.inputs[i]!.type v with
        | some t =>
          fixed := fixed.push (i, t)
          fixedVals := fixedVals.push (i, v)
        | none => fixable := false
      if fixable then
        match ← runPoint ctx stmt c plan drawn fixed fixedVals with
        | some a => return some a
        | none => pure ()
    -- a coupled scalar whose literal term the substitution cannot write
    -- makes every grid point unfixable; the case answers `nothing`, the
    -- same answer the bit-vector source's `literalDetail` carries
    return none

/-! ## The per-case plan the draw-driven sources share -/

/-- The per-case pieces the two draw-driven sources share (§9.4, §9.9):
the container positions with their free variables, the reads' plan, and
the coupled scalars. The random source draws over them and the built
source overlays a built state, and both walk the same plan, which is what
keeps the read substitution aligned with the compiled values (§9.4). -/
structure CasePlan where
  /-- The container positions, in binder order. -/
  containers : Array Nat
  /-- Their free variables, aligned with `containers`. -/
  containerIds : Array FVarId
  /-- The container-reading subterms of the case's hypotheses, in walk
  order (§9.4). -/
  plan : Array Expr
  /-- The free scalars inside a container-mentioning subterm (§9.4's
  coupled walk). -/
  coupled : Array Nat

/-- The plan of one case: the container test reads the statement's own
scalar-kind table, which the reader computed through the reducible
`whnf`, so an alias (`Gwei` for `UInt64`) never reads as a container
(§9.4). -/
def casePlanOf (ctx : SearchCtx) (stmt : Statement) (c : Case) :
    MetaM CasePlan := do
  let kinds := stmt.scalarKinds
  let containerFlags : Array (Option FVarId) :=
    (Array.range stmt.inputs.size).map fun i =>
      if kinds[i]?.any (·.isSome) then none
      else some ctx.inputFvars[i]!.fvarId!
  let containerIds : Array FVarId := containerFlags.filterMap id
  -- the reads' plan: one walk per case, shared by every draw and grid
  -- point
  let plan ← containerReads containerIds c.hyps
  -- the coupled scalars: the free scalars inside a container-mentioning
  -- subterm, the seed handoff's walk over the drawn containers (§9.4);
  -- computed once, the case's alone
  let scalarPos : Array Nat :=
    (Array.range stmt.inputs.size).filter fun i => (kinds[i]?).any (·.isSome)
  let inner : Array FVarId :=
    c.hyps.foldl (fun acc h => topSeededScalarIds containerIds h acc) #[]
  let coupled := scalarPos.filter fun i =>
    inner.contains (ctx.inputFvars[i]!.fvarId!)
  let containers : Array Nat :=
    (Array.range containerFlags.size).filter fun i =>
      containerFlags[i]?.any (·.isSome)
  return { containers, containerIds, plan, coupled }

/-- The memoized raw draw at one index (§9.4): a draw is a pure function
of the seed, the size, and the index, and the cases of one theorem share
the memo. The built source reads draw 0 for its non-state containers
through the same entry, so a built witness's drawn bytes and a random
witness's agree position by position (§9.9). -/
def drawAt (ctx : SearchCtx) (seed size draw : Nat) : MetaM (Array ByteArray) := do
  let slot ← ctx.drawMemo.get
  if h : draw < slot.size then
    match slot[draw] with
    | some b => pure b
    | none =>
      let b := ctx.probe.sample (seed + draw) size
      let i : Fin slot.size := ⟨draw, h⟩
      ctx.drawMemo.set (slot.set i b)
      pure b
  else
    let b := ctx.probe.sample (seed + draw) size
    ctx.drawMemo.set (slot ++ #[some b])
    pure b

/-- The random source (§9.4). Applies when at least one input is a
container and no block input is in play; the search answers `nothing`
when the container test was an alias (§9.4), and after
`theorem_vectors.randomDraws` failed draws. The draws run from the run's
`theorem_vectors.seed`, so a build is reproducible (§14.4). -/
def randomSource : WitnessSource where
  tag := .random
  applies _ stmt _ :=
    stmt.blockInputs.isEmpty &&
    stmt.scalarKinds.any (·.isNone)
  search ctx stmt c := do
    let drawBudget := theorem_vectors.randomDraws.get (← getOptions)
    let size := theorem_vectors.randomSize.get (← getOptions)
    let seed := theorem_vectors.seed.get (← getOptions)
    let kinds := stmt.scalarKinds
    -- `applies` read the same kind table, so at least one position is a
    -- container here
    let cp ← casePlanOf ctx stmt c
    for draw in [0:drawBudget] do
      -- one draw per index for the whole theorem: a draw is a pure
      -- function of the seed, the size, and the index, and the cases
      -- share the memo (§9.4)
      let rawBytes ← drawAt ctx seed size draw
      let drawn := cp.containers.map fun i => (i, rawBytes.getD i emptyBytes)
      match ← tryDraw ctx stmt c size cp.containerIds
          cp.plan kinds cp.coupled drawn with
      | some a => return .candidate a
      | none => pure ()
    return .nothing
      (some s!"no draw satisfied the case within {drawBudget} draws")

end EthCLLib.TheoremVectors
