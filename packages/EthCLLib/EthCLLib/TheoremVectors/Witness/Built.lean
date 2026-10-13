import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Witness.Random

/-!
# `EthCLLib.TheoremVectors.Witness.Built`: the state-builder source

The `built` source of §9.9: before the random source draws, the source
walks the fork binding's builder catalog over a knob grid, cheapest
first. A builder runs the spec itself, so its state is reachable. The
invariants the spec maintains hold of it: activation epochs behind the
slot, a balance list as long as the registry, a queue drained by the
fork's own onboarding step. A field-by-field draw breaks them.

At each grid step the source overlays the built bytes on the statement's
one state input, draws every other container input the way the random
source draws it (the shared memo, draw 0), and runs the same point loop
the random source runs over a draw (§9.9: "the same loop"): ground the
case's container reads at the built bytes, walk the coupled scalars'
grid, and hand the residual to the solver. The probe's check stays the
single arbiter.

The grid order is the shrink order (§9.9): the walk stops at the first
step whose point satisfies the case, so the winner is the cheapest
reachable state the grid found, and a built state is never shrunk by its
fields, which would break what the builder guaranteed.

The built bytes cache in the output tree, keyed by fork, preset, builder,
and knobs, with the binding module's Lake `.trace` text as the stamp. A
built state is a pure function of those, and the binding's trace folds
the artifacts of everything the bytes depend on (the fork body, the
builders, the crypto seams), so every theorem of the fork shares one
entry per grid step and a change to any of them invalidates the stamp at
once.

## Deviations the module carries

- The grid's "first epoch boundary" step needs `slotsPerEpoch` in preset
  units. The framework half reads the fork's own
  `Const.slotsPerEpoch` through the binding's fork name and evaluates it
  compiled; a fork without the constant takes the upstream minimal value
  8. (`IMPLEMENTATION_NOTES.md` records the deviation.)
- `Witness/Built.lean` imports `Witness.Random`, because §9.9 runs "the
  same loop the random source runs over a draw", and that loop
  (`tryDraw`, `casePlanOf`, `drawAt`) lives there.
- A builder constant carries the fork's own instance binders beside
  `Knobs`, those its body uses (`[Preset] [Config]`, plus
  `[CryptoBackend]` where a signature check reaches the seam), because
  running the spec needs the seams the fork body runs under; §9.9's
  sketch names `[Preset] [Config]` alone. The catalog's builders pin the
  hasher locally, so no builder binds `[HasherTag]`.

## Lean idioms annotated

- `IO` in a source's `search`: `SearchM` is `MetaM`, whose monad stack
  lifts `IO`, so the cache reads and writes are one `liftIO` away. The
  stamp check is a plain file-text comparison, never parsed.
- `Name.getPrefix` drops a name's last atom, which turns the binding
  constant's name into its module's name; the stamp reads that module's
  own trace file, found through `Lean.findOLean` in `LEAN_PATH`.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## The grid (§9.9) -/

/-- The per-preset default of `theorem_vectors.builtSteps` (§14.4):
the whole six-step grid at minimal, and the three cheap steps at mainnet,
where every spec run goes over 65536-long vectors; the steps the cap
cuts are the two 16-validator slot-40 states and the 64-validator
slot-40 one. -/
def builtStepsDefault : PresetId → Nat
  | .minimal => 6
  | .mainnet => 3

/-- The option's answer at one preset: an explicit positive
`theorem_vectors.builtSteps` applies at both presets, the default `0`
takes the preset's own cap. -/
def builtStepsOf (p : PresetId) : MetaM Nat := do
  let v := theorem_vectors.builtSteps.get (← getOptions)
  return if v == 0 then builtStepsDefault p else v

/-- The builder grid, cheapest first (§9.9's table). The builder names are
catalog display names; a name the binding's catalog lacks skips the step,
so a fork with a shorter catalog walks a shorter grid. -/
def Built.grid (epochBoundary : Nat) : Array (String × Knobs) :=
  #[("genesis", { validators := 8 }),
    ("advanced", { validators := 8, slot := epochBoundary }),
    ("upgraded", { validators := 8, slot := epochBoundary }),
    ("advanced", { validators := 16, slot := 40 }),
    ("withQueue", { validators := 16, slot := 40, queue := 4 }),
    ("advanced", { validators := 64, slot := 40 })]

/-- The first epoch boundary in preset units, for the grid's second and
third steps: the fork's own `Const.slotsPerEpoch`, named through the
binding's fork name and evaluated compiled. The fallback is 8, the
minimal preset's upstream value, taken when the fork names no such
constant or the constant does not reduce under the binding's preset. -/
def Built.epochBoundaryOf (binding : ForkBinding) (p : PresetId) :
    MetaM Nat := do
  let fallback := 8
  let name := (binding.fork ++ `Const) ++ `slotsPerEpoch
  unless (← getEnv).contains name do
    return fallback
  let some presetC := (Preset.constOf binding p .preset).toOption |
    return fallback
  try evalNatOp (mkApp (.const name []) (.const presetC []))
  catch _ => pure fallback

/-! ## The cache (§9.9) -/

/-- The cache path of one built state:
`<outDir>/built/<fork>/<preset>/<builder>/<validators>-<slot>-<balance>-<queue>.ssz`.
Every theorem of the fork shares the entry. -/
def Built.cachePath (outDir : System.FilePath) (forkTag : String)
    (preset : PresetId) (builderName : String) (k : Knobs) :
    System.FilePath :=
  outDir / "built" / forkTag / preset.tag / builderName /
    s!"{k.validators}-{k.slot}-{k.balance}-{k.queue}.ssz"

/-- The cached bytes at `path`, `none` when the entry is missing or its
`.stamp` no longer matches the current stamp. The stamp is the binding
module's trace text, compared whole: Lake folds every import's trace
into the file, so any change to the fork body, the builders, or the
seams the binding names changes the text. -/
def Built.read (stamp : String) (path : System.FilePath) :
    IO (Option ByteArray) := do
  unless ← path.pathExists do
    return none
  let stampPath := path.withExtension "stamp"
  unless ← stampPath.pathExists do
    return none
  if (← IO.FS.readFile stampPath) != stamp then
    return none
  some <$> IO.FS.readBinFile path

/-- Write one cache entry: the state bytes and the stamp beside them. -/
def Built.write (path : System.FilePath) (stamp : String)
    (bytes : ByteArray) : IO Unit := do
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeBinFile path bytes
  IO.FS.writeFile (path.withExtension "stamp") stamp

/-- The built bytes one grid step produces, through the cache: a hit
answers the stored bytes, a miss runs the builder once and writes the
entry, so a builder runs at most once per build for each grid step it
reaches, however many theorems use it (§9.9). -/
def Built.stateBytes (outDir : System.FilePath) (forkTag : String)
    (preset : PresetId) (builderName : String) (stamp : String)
    (probe : Probe) (builderIdx : Nat) (k : Knobs) : IO ByteArray := do
  let path := Built.cachePath outDir forkTag preset builderName k
  match ← Built.read stamp path with
  | some b => pure b
  | none =>
    let b := probe.build builderIdx k
    -- empty bytes cache nothing: a builder that answered nothing stays
    -- a per-call miss, so one divergent state test cannot pin empty
    -- bytes on an entry every theorem of the fork then reads
    unless b.isEmpty do
      Built.write path stamp b
    pure b

/-- The built bytes one catalog entry produces, through the cache, at the
search context's output root and stamp: the one face the source's walk,
the hint derivation, and the hint replay all call, which is what keeps a
builder at one run per build per grid step (§9.9). An entry the catalog
does not name answers the empty bytes, which the check rejects. -/
def Built.cachedBytes (ctx : SearchCtx) (builderName : String)
    (k : Knobs) : MetaM ByteArray := do
  let some bIdx := ctx.binding.builders.findIdx? (fun (n, _) => n == builderName) |
    return emptyBytes
  Built.stateBytes ctx.outDir ctx.binding.tag ctx.preset builderName
    ctx.builtStamp ctx.probe bIdx k

/-- One module's cache stamp: the text of its `.trace` file, read
through `LEAN_PATH`. A module that is not on disk yet stamps `""`; the
cache still works, an entry written under the empty stamp matches every
later empty-stamp run, and the entries rebuild once a trace text
appears or changes. -/
def Built.stampOf (mod : Name) : IO String := do
  let olean? ←
    (try some <$> Lean.findOLean mod catch _ => pure none)
  let some olean := olean? | pure ""
  let trace := olean.withExtension "trace"
  if ← trace.pathExists then
    IO.FS.readFile trace
  else
    pure ""

/-- The binding module's stamp, at the command's call site: the binding
constant's parent. Its Lake trace folds the artifacts of everything it
imports, the fork's Builders module and the fork body and the crypto
seams the binding names among them, so a change to any of them changes
the stamp and the cache rebuilds (§9.9). The framework half takes the
module name from the caller because the binding value carries no name of
its own. -/
def Built.stampOfBinding (bindingConst : Name) : IO String :=
  Built.stampOf bindingConst.getPrefix

/-! ## The source -/

/-- The grid step whose built bytes the assignment carries at the state
position, for the built hint row (§9.8): the builder's catalog display
name and the knobs. The walk rebuilds each step's state through the
cache, capped at the run's grid budget, so the derivation costs the
cache reads alone; the first byte-identical step is the one that won. A
name the binding's catalog lacks skips the step, so a hit always
carries a real catalog name. -/
def Built.findStep (ctx : SearchCtx) (cap : Nat) (a : Assignment)
    (statePos : Nat) : MetaM (Option (String × Knobs)) := do
  let some stateBytes := a[statePos]? | return none
  let grid := Built.grid ctx.epochBoundary
  for i in [0:cap] do
    if h : i < grid.size then
      let (bName, k) := grid[i]
      unless ctx.binding.builders.any (fun (n, _) => n == bName) do
        continue
      if (← Built.cachedBytes ctx bName k) == a.getD statePos emptyBytes then
        return some (bName, k)
    else
      break
  return none

/-- The `built` source (§9.9). Applies when no block input is in play and
exactly one input has the binding's state type. The walk stops at the
first grid step whose point satisfies the case, which is the knob shrink:
cheaper steps ran first and failed (§9.9). -/
def builtSource : WitnessSource where
  tag := .built
  applies ctx stmt _ :=
    stmt.blockInputs.isEmpty &&
    !ctx.binding.builders.isEmpty &&
    ((Array.range stmt.inputs.size).filter
      (fun i => isStateType ctx.binding stmt.inputs[i]!.type)).size == 1
  search ctx stmt c := do
    let some statePos := (Array.range stmt.inputs.size).find?
        (fun i => isStateType ctx.binding stmt.inputs[i]!.type) |
      return .nothing
    let steps ← builtStepsOf ctx.preset
    let grid := Built.grid ctx.epochBoundary
    -- the per-case pieces, shared with the random source (§9.4, §9.9)
    let cp ← casePlanOf ctx stmt c
    -- every other container input draws the random source's draw 0, the
    -- same memo, so a built witness's drawn bytes and a random one's
    -- agree position by position (§9.9)
    let seed := theorem_vectors.seed.get (← getOptions)
    let size := theorem_vectors.randomSize.get (← getOptions)
    let raw0 ← drawAt ctx seed size 0
    let others : Array (Nat × ByteArray) :=
      cp.containers.filterMap fun i =>
        if i == statePos then none else some (i, raw0.getD i emptyBytes)
    -- the cache reads carry the run's stamp (§9.9)
    let mut built : Nat := 0
    for step in [0:steps] do
      if h : step < grid.size then
        let (bName, k) := grid[step]
        -- a name the binding's catalog lacks skips the step (§9.9), and
        -- `cachedBytes` answers the empty bytes for one
        unless ctx.binding.builders.any (fun (n, _) => n == bName) do
          continue
        let bytes ← Built.cachedBytes ctx bName k
        built := built + 1
        let drawn := others.push (statePos, bytes)
        -- `0`: no coupled-values cap, the built registries hold what
        -- the knobs built, and the safe gate skips out-of-range points
        match ← tryDraw ctx stmt c 0 cp.containerIds cp.plan stmt.scalarKinds
            cp.coupled drawn with
        | some a => return .candidate a
        | none => pure ()
      else
        break
    return .nothing
      (some s!"no grid step of {built} satisfied the case")

end EthCLLib.TheoremVectors
