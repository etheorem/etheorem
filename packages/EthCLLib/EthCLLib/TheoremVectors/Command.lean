import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Preset
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.Seed
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.Outcome
import EthCLLib.Internal.ProofLedger

/-!
# `EthCLLib.TheoremVectors.Command`: the generator commands

The generator-file surface (`THEOREM_VECTORS_ARCHITECTURE.md` §14):

```lean
theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas

theorem_vectors characterized
theorem_vectors tagged
theorem_vectors survey
theorem_vectors canBuilderCoverBid_iff with (state := Seeds.Gloas.coverBidState)
theorem_vectors getPtcElseOffset_lt_same_slot presets minimal mainnet
theorem_vectors skip processOperations_run_ok_iff "block input, needs a body builder"
```

The header stores the binding constant's name in a module-local extension
(§14.2); every later line reads it, and a line in a file with no header is
an error. Each line elaborates into a `Line` value, stored in file order in
a second module-local extension. Both extensions export nothing to the
`.olean`, so one generator file's lines never reach another module.

The **whole-file precedence pass** (§14.3) runs after every line. It
resolves the file's selection against the lines seen so far: named lines
run first, in file order, then the discovered set in name order. A named
line wins over discovery for the same theorem, `skip` excludes a theorem
from discovery, and a discovery clause only contributes the theorems its
own kind selects. The pass runs every theorem whose resolved description
has not run yet. Once the file is complete, the last pass therefore holds
§14.3's full precedence, and nothing runs twice unless a later line
overrode it. One order rule follows from the line-at-a-time passes: a
`skip` validates against the clauses above it, so a `skip` line must
follow the discovery clause that selects its theorem.

**Stage 2.** A named or discovered theorem's run wires phases B1 through
B8 end to end for one preset: the prepare pass (§8.4's first form) builds
one case, the probe compiles (§11.2), the seed and base sources search
(§9.2, §9.4), the executor records `.eq` and `.bound` runs (§11.3), the
record round-trips (§12.5), and the outcome carries the real statuses.
`survey` runs phase A alone, with status `unselected` (§14.3), so the
report shows the whole corpus without searching anything.

One deviation from the sketch is recorded in `IMPLEMENTATION_NOTES.md`:
an `unsupported` outcome's shape field writes `unsupported`, because the
§16.1 example leaves the field's value for that case unspecified.

## Lean idioms annotated

- `SimpleScopedEnvExtension` with `exportEntry? := fun _ _ => none` is
  module-local state: the entries live for the current module and the
  `.olean` carries none of them, which is what makes a generator file's
  lines invisible to its importers.
- A `command` elaborator (`CommandElabM`) runs at `lake build` time with
  the full environment, which is why the pass can read theorem types
  (`Statement.readIn` runs `MetaM` under `liftTermElabM`), elaborate seed
  terms, and write the records and outcomes to disk.
- `resolveGlobalConstNoOverload` resolves a line's identifier through the
  file's `open`s; a named line falls back to the fork's proof namespace
  when the bare name does not resolve (§14.3).
-/

set_option autoImplicit false

open Lean
open Lean.Elab.Command

namespace EthCLLib.TheoremVectors

/-! ## Lines and the module-local store -/

/-- One generator-file line, as parsed (`THEOREM_VECTORS_ARCHITECTURE.md` §14.3). -/
inductive LineKind where
  /-- `theorem_vectors characterized`: every `@[characterizes]` theorem
  whose target the binding's fork owns. -/
  | characterized
  /-- `theorem_vectors tagged`: every `@[theorem_vectors]` theorem under
  the fork's proof namespace. -/
  | tagged
  /-- `theorem_vectors survey`: every public theorem under the fork's
  proof namespace that no other clause or line selects, phase A alone
  (§14.3). -/
  | survey
  /-- A named line, with the seeds its `with` spelled. -/
  | named (thm : Name) (strict : Bool) (seeds : Array (Name × Syntax))
  /-- A `skip` line, with its reason. -/
  | skipped (thm : Name) (reason : String)
  deriving Inhabited

/-- Kind equality, spelled out because the named case carries `Syntax`
seeds and `Syntax` has no decidable equality. -/
private def LineKind.sameKind : LineKind → LineKind → Bool
  | .characterized, .characterized => true
  | .tagged, .tagged => true
  | .survey, .survey => true
  | .named .., .named .. => true
  | .skipped .., .skipped .. => true
  | _, _ => false

/-- One line, with the preset list its `presets` clause spelled. -/
structure Line where
  kind      : LineKind
  presetIds : Array PresetId := #[PresetId.minimal]
  deriving Inhabited

/-- The generator file's lines, in file order. Module-local: the `.olean`
carries none of them. -/
initialize generatorLines :
    SimpleScopedEnvExtension Line (Array Line) ←
  registerSimpleScopedEnvExtension {
    initial      := #[]
    addEntry     := Array.push
    exportEntry? := fun _ _ => none
  }

/-- The binding constant the file's header named. -/
initialize forkHeader :
    SimpleScopedEnvExtension Name (Option Name) ←
  registerSimpleScopedEnvExtension {
    initial      := none
    addEntry     := fun _ b => some b
    exportEntry? := fun _ _ => none
  }

/-- The executions the pass already ran, keyed by theorem with a hash of
the resolved description. A pass skips a theorem whose description matches,
so only an overriding line re-runs it. -/
initialize executed :
    SimpleScopedEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimpleScopedEnvExtension {
    initial      := #[]
    addEntry     := Array.push
    exportEntry? := fun _ _ => none
  }

/-! ## Syntax -/

scoped syntax (name := tvForkCmd) "theorem_vectors_fork " ident : command

-- one rule per discovery kind: the elab reads the clause's presets off
-- its own syntax instead of dispatching on an alternative's node kind,
-- which is the atom's synthesized name and not the word itself
scoped syntax (name := tvCharacterizedCmd)
  "theorem_vectors " "characterized" optional("presets " ident+) : command

scoped syntax (name := tvTaggedCmd)
  "theorem_vectors " "tagged" optional("presets " ident+) : command

-- the survey takes no `presets` clause: nothing runs per preset (§14.3)
scoped syntax (name := tvSurveyCmd)
  "theorem_vectors " "survey" : command

scoped syntax (name := tvSkipCmd)
  "theorem_vectors " "skip" ident str : command

-- the strict marker rides on the identifier token: the lexer reads
-- `theorem_vectors!` as one ident, so this atom and the plain form's
-- leading atom never collide. The seeded and seedless forms are separate
-- rules, so the seeds and the presets clause sit at fixed indices.
scoped syntax (name := tvNamedStrictCmd)
  "theorem_vectors!" ident "with" many("(" ident " := " term ")")
  optional("presets " ident+) : command

-- §14.3 defines seeds only through `with`, so the seedless rules take
-- no seed group: a bare `(input := term)` group is a parse error.
scoped syntax (name := tvNamedStrictNoSeedCmd)
  "theorem_vectors!" ident optional("presets " ident+) : command

scoped syntax (name := tvNamedCmd)
  "theorem_vectors " ident "with" many("(" ident " := " term ")")
  optional("presets " ident+) : command

scoped syntax (name := tvNamedNoSeedCmd)
  "theorem_vectors " ident optional("presets " ident+) : command

/-- Every ident in a syntax subtree, in source order. The `presets` clauses
reach this through one access path whatever `optional` wrapped them in. -/
private partial def identsOf : Syntax → Array Name
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.flatMap identsOf
  | _ => #[]

/-- Parse a `presets` clause into preset ids. An unknown tag is a parse
error, the failure policy's malformed-invocation case. -/
private def onePreset (n : Name) : CommandElabM PresetId :=
  match PresetId.ofTag? n.toString with
  | some p => pure p
  | none =>
    throwError "theorem_vectors: unknown preset '{n}'; \
      the tags are `minimal` and `mainnet`"

/-- Parse a `presets` clause into preset ids. An absent clause means the
default preset list, one entry at `minimal` (§14.3: the default is
`minimal`). -/
private def parsePresets (stx : Syntax) : CommandElabM (Array PresetId) := do
  let ids := identsOf stx
  if ids.isEmpty then pure #[PresetId.minimal]
  else ids.mapM onePreset

/-- Read a `ForkBinding` value out of the environment. §6: "the command
reads it with `evalConst`." The safe face is `opaque` whose body never
runs; the implementation below evaluates the constant, which only the
compiled elaborator can do. The `#eval` machinery in core follows the same
shape (`elabEvalCore` with `@[implemented_by]`). -/
private unsafe def evalForkBindingImpl (env : Environment) (opts : Options)
    (constName : Name) : Except String ForkBinding :=
  env.evalConst ForkBinding opts constName

@[implemented_by evalForkBindingImpl]
private opaque evalForkBindingCore (env : Environment) (opts : Options)
    (constName : Name) : Except String ForkBinding := .error "unreachable"

/-- The binding value a generator file's header names. -/
private def evalForkBinding (constName : Name) : CommandElabM ForkBinding := do
  match evalForkBindingCore (← getEnv) (← getOptions) constName with
  | .ok b => return b
  | .error e =>
    throwError "theorem_vectors: cannot read the binding `{constName}`: {e}"

/-- Resolve a line's ident to a constant, falling back to the fork's proof
namespace for the unqualified form (§14.3). -/
private def resolveThmName (binding : ForkBinding) (ident : Syntax) :
    CommandElabM Name := do
  let fallback := EthCLLib.Internal.proofNamespaceOf binding.fork ++ ident.getId
  let resolved? ←
    (try do
      let n ← liftCoreM <| resolveGlobalConstNoOverload ident
      return some n
    catch _ => return none)
  match resolved? with
  | some n => return n
  | none =>
    if (← getEnv).contains fallback then
      return fallback
    else
      throwError "theorem_vectors: `{ident.getId}` does not resolve, not even \
        under `{EthCLLib.Internal.proofNamespaceOf binding.fork}`"

/-! ## The selection -/

/-- The theorem names one clause kind selects, from the environment's tags
and constants (§14.1, §14.3). -/
private def discoverySet (env : Environment) (binding : ForkBinding) :
    LineKind → NameSet
  | .characterized =>
    (EthCLLib.Internal.characterizations env).foldl (init := {}) fun acc (thm, target) =>
      if (EthCLLib.Internal.specFunctionOwner? env target).map (·.1)
          == some binding.fork then
        acc.insert thm
      else acc
  | .tagged =>
    let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
    (EthCLLib.Internal.theoremVectorTags env).foldl (init := {}) fun acc thm =>
      if proofNs.isPrefixOf thm then acc.insert thm else acc
  | .survey =>
    let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
    env.constants.fold (init := ({} : NameSet)) fun acc n info =>
      if proofNs.isPrefixOf n && info matches .thmInfo _ && !n.isInternal then
        acc.insert n
      else acc
  | _ => {}

/-- The output root the command writes into: the lakefile's weak setting
when present, the option's default otherwise (§14.4). -/
private def outDirOf : CommandElabM System.FilePath := do
  match ((← getOptions).get? `theorem_vectors.outDir : Option Lean.DataValue) with
  | some v => return v.str
  | none => return theorem_vectors.outDir.defValue

/-- The wire tag of a statement's shape, for the record's `shape` field
(§5.6). An unsupported statement never reaches a record; the `none` case
is unreachable there. -/
private def shapeTagOf (shape : Shape) : Option ShapeTag :=
  match shape with
  | .eq .. => some .eq
  | .iffTrue .. => some .iffTrue
  | .bound .. => some .bound
  | .runOk .. => some .runOk
  | .runError .. => some .runError
  | .unsupported _ => none

/-- The report line for one search failure (§18's reported facts). A
`notFound` on a theorem with block inputs is §18's `outOfScope`: only the
base source may run, it ran, and it failed (§1.2). -/
private def failureOf (blockInputs : Array Name) : Failure →
    RunStatus × String
  | .unsat => (.unsat, "unsat: the hypotheses are vacuous")
  | .notFound tried =>
    if blockInputs.isEmpty then
      (.skipped, s!"notFound after {String.intercalate ", "
        (tried.toList.map (·.tag))}")
    else
      (.outOfScope, s!"outOfScope: block inputs {String.intercalate ", "
        (blockInputs.toList.map (·.toString))} and the base source \
        failed ({String.intercalate ", " (tried.toList.map (·.tag))})")
  | .outOfScope inputs =>
    (.outOfScope, s!"outOfScope: block inputs {String.intercalate ", "
      (inputs.toList.map (·.toString))} and the base source failed")

/-- One phase-B run of one theorem at one preset (`THEOREM_VECTORS_ARCHITECTURE.md`
§3's B1 through B8). Runs inside the reader's telescope scope: the seed
terms still carry the telescope's instance variables, and the probe builds
from the statement's expressions. -/
private def runPreset (binding : ForkBinding) (outDir : System.FilePath)
    (thmLocal : String) (seedTerms : Array (Nat × Expr))
    (p : PresetId) (ctx : StatementCtx) (cases : Array Case) :
    MetaM RunOutcome := do
  let stmt := ctx.stmt
  let startMs ← IO.monoMsNow
  -- B0: the executor runs `.eq` and `.bound` in stage 2 (§11.3)
  if let some stage := Execute.handles? stmt.shape then
    return { preset := some p, status := .skipped, reason := some stage }
  if cases.isEmpty then
    return { preset := some p, status := .skipped,
             reason := some "the prepare pass produced no case" }
  -- B1: the probe for this preset (§10, §11). An `.error` answer is a
  -- skip reason, a fact about the theorem or the shape.
  let (info, probe) ← match ← Probe.ofStatement binding p ctx cases seedTerms with
    | .ok r => pure r
    | .error reason =>
      return { preset := some p, status := .skipped, reason := some reason }
  -- B3: the search, seed before base (§9.2, §9.4); a block input leaves
  -- only the base source running (§1.2)
  let sources : Array WitnessSource :=
    if stmt.blockInputs.isEmpty then #[seedSource, baseSource]
    else #[baseSource]
  let searchCtx : SearchCtx := { probe, info, binding, preset := p }
  let some shapeTag := shapeTagOf stmt.shape
    | return { preset := some p, status := .unsupported,
               reason := some "unsupported shape" }
  let mut written : Nat := 0
  let mut source? : Option String := none
  let mut failures : Array (Nat × RunStatus × String) := #[]
  for c in cases do
    match ← searchCase sources searchCtx stmt c with
    | .error failure =>
      let (status, text) := failureOf stmt.blockInputs failure
      failures := failures.push (c.index, status, text)
    | .ok (a, won) =>
      -- B5: run, and execute the shape's row (§11.3). A disagreement or a
      -- probe failure is a build error, per §18.
      let r ← match probe.run a with
        | .ok r => pure r
        | .error e =>
          throwError "theorem_vectors: the probe failed to run \
            `{stmt.thm}`: {e}"
      let (outVal, errVal) ← Execute.output stmt.thm stmt.shape info r
      let inputVals : Array VectorValue :=
        (Array.range info.inputNames.size).map fun i =>
          VectorValue.ofRun info.inputNames[i]! info.inputTypes[i]!
            (r.inputLiterals.getD i none) (r.inputRoots.getD i none)
      let record : VectorRecord :=
        { thm := stmt.thm, fork := binding.tag, preset := p,
          target := stmt.target, shape := shapeTag,
          caseIndex := c.index, side := c.side,
          inputs := inputVals, output := outVal, error := errVal,
          source := won }
      -- B6: write the record (§12.1, §12.4); the assignment's bytes are
      -- the record's bytes
      let dir := Record.caseDir outDir binding.tag p thmLocal c.index c.side
      Record.write outDir binding.tag record thmLocal a (some r.output)
      -- B7: read the directory back and run the probe on the stored bytes
      -- (§12.5). This checks the SSZ round trip of every value and the
      -- record writer itself; a mismatch is a build error (§18).
      let rb ← Record.read dir
      match probe.run rb.inputBytes with
      | .error e =>
        throwError "theorem_vectors: the read-back of `{stmt.thm}` case \
          {c.index} failed to decode: {e}"
      | .ok r2 =>
        unless compareBytes r2.output (rb.outputBytes.getD emptyBytes) do
          throwError "theorem_vectors: the read-back of `{stmt.thm}` case \
            {c.index} disagrees with the recorded output (§12.5): \
            recorded {EthCLLib.TheoremVectors.hexOf
              (rb.outputBytes.getD emptyBytes)}, \
            fresh {EthCLLib.TheoremVectors.hexOf r2.output}"
      -- §14.3: one info line per record, with the path
      logInfo m!"theorem_vectors [{binding.tag}] {stmt.thm}: record \
        {dir}"
      written := written + 1
      if source?.isNone then source? := some won.tag
  let endMs ← IO.monoMsNow
  let seconds := some ((endMs - startMs).toFloat / 1000.0)
  let failureText := String.intercalate "; "
    (failures.toList.map fun (i, _, text) => s!"case {i}: {text}")
  if written > 0 then
    return { preset := some p, status := .written, records := written,
             source := source?, seconds,
             reason := if failures.isEmpty then none
                       else some failureText }
  else
    -- every case failed: the status is the §18 fact the failures name
    let status : RunStatus :=
      if failures.any fun (_, st, _) => st == .unsat then .unsat
      else if failures.any fun (_, st, _) => st == .outOfScope then
        .outOfScope
      else .skipped
    return { preset := some p, status, reason := some failureText }

/-- The stage-2 run of one theorem: phase A, then phases B1 through B8 per
preset (§3, and the module docstring). The whole fold runs inside the
reader's telescope scope (`Statement.readIn`), because the statement's
expressions and the seed terms cannot leave it. -/
private def runTheorem (binding : ForkBinding) (origin : OutcomeOrigin)
    (strict : Bool) (thm : Name) (ps : Array PresetId)
    (seedStx : Array (Name × Syntax)) : CommandElabM Unit := do
  let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
  let localName := thm.replacePrefix proofNs .anonymous
  let outDir ← outDirOf
  liftTermElabM do
    Statement.readIn binding thm fun ctx => do
      let stmt ← Scope.classify binding ctx.stmt
      -- phase A: an unsupported statement is a reported skip (§7.5, §18)
      match stmt.shape.reason? with
      | some r =>
        -- §16.1: a survey line (no presets) carries one run with no
        -- preset field; a per-preset line carries one run per preset
        let runs := if ps.isEmpty then
          #[{ preset := none, status := .unsupported, reason := some r }]
        else
          ps.map fun p =>
            { preset := some p, status := .unsupported, reason := some r }
        let outcome : Outcome :=
          { «theorem» := thm, target := stmt.target, shape := "unsupported",
            origin, blockInputs := stmt.blockInputs, cases := 0, runs }
        Outcome.write outDir binding.tag outcome localName.toString
        logInfo m!"theorem_vectors [{binding.tag}] {thm}: \
          unsupported ({r})"
        -- §18: a claim the author made fails hard
        if strict then
          throwError "theorem_vectors: `{thm}` carries a claim (`!` or \
            `@[theorem_vectors]`) and the reader reported: {r}"
      | none =>
        -- phase A: prepare (§8.4's first form)
        let (cases, dropped) ← Prepare.pass stmt
        -- the author seeds (§14.3: "[Preset]-generic, elaborated at each
        -- preset"): each term elaborates against its input's type inside
        -- the telescope, so the theorem's own instances fill the seed's
        -- instance binders and `substInstances` fixes them per preset. A
        -- seed for an input the theorem does not have is an error here,
        -- and a seed of the wrong type is an elaboration error at the
        -- clause: §18's build error for an author claim.
        let seedTerms ← seedStx.mapM fun (n, stx) => do
          match stmt.inputs.findIdx? (fun i => i.name == n) with
          | none =>
            throwError "theorem_vectors: the seed names input `{n}`, \
              which `{thm}` does not have (§14.3)"
          | some i => do
            let t := stmt.inputs[i]!.type
            -- the expected type fills the seed's `[Preset]`-generic
            -- instance binders from the telescope; the check below holds
            -- the §18 line: a seed of the wrong type is an error at the
            -- clause, because the author claimed it works
            let term ←
              (Lean.Elab.Term.withoutErrToSorry
                (Lean.Elab.Term.elabTermAndSynthesize stx (some t))).run'
            let term ← Lean.instantiateMVars term
            unless ← Meta.isDefEq (← Meta.inferType term) t do
              throwError "theorem_vectors: the seed for `{n}` of \
                `{thm}` does not have the input's type (§14.3)"
            pure (i, term)
        -- phases B1 through B8, per preset in the line's list
        let runs ← ps.mapM fun p =>
          runPreset binding outDir localName.toString seedTerms p ctx cases
        -- §18: a strict claim that skipped fails hard; a non-strict line
        -- warns
        -- §18: `unsat` is always reported and never an error; the
        -- other three are skips, and a claim the author made fails hard
        for run in runs do
          if run.status matches .unsupported | .skipped | .outOfScope then
            let msg := m!"theorem_vectors [{binding.tag}] {thm} at \
              {run.preset.getD PresetId.minimal |>.tag}: {run.status.tag} \
              ({run.reason.getD "no reason"})"
            if strict then
              throwError "{msg}"
            else
              logWarning msg
        -- §16.1: the survey's one unselected run
        let runs := if runs.isEmpty then
          #[{ preset := none, status := .unselected }]
        else runs
        let outcome : Outcome :=
          { «theorem» := thm, target := stmt.target,
            shape := stmt.shape.wire, origin,
            blockInputs := stmt.blockInputs, cases := cases.size, runs }
        Outcome.write outDir binding.tag outcome localName.toString
        logInfo m!"theorem_vectors [{binding.tag}] {thm}: shape \
          {stmt.shape.wire}, {cases.size} case(s), origin {origin.tag}"
        -- §8.4: a dropped case is reported
        for d in dropped do
          logWarning m!"theorem_vectors [{binding.tag}] {thm}: {d}"

/-! ## The whole-file precedence pass -/

/-- The outcome a `skip` line records: origin `skipped` with the line's
reason, one skipped run per default preset. -/
private def recordSkip (binding : ForkBinding) (thm : Name)
    (reason : String) : CommandElabM Unit := do
  let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
  let localName := thm.replacePrefix proofNs .anonymous
  let outDir ← outDirOf
  let outcome : Outcome :=
    { «theorem» := thm, target := none, shape := "unsupported",
      origin := .skipped, blockInputs := #[], cases := 0,
      runs := #[{ preset := some .minimal, status := .skipped,
                  reason := some reason }] }
  Outcome.write outDir binding.tag outcome localName.toString

/-- The pass's description key for one theorem, so an overriding line
re-runs it and nothing else does. -/
private def execKey (origin : OutcomeOrigin) (ps : Array PresetId) : String :=
  origin.tag ++ ":" ++ String.intercalate "," (ps.toList.map (·.tag))

/-- The whole-file precedence pass (§14.3, and the module docstring).
Resolves the file's selection against the lines seen so far and runs what
has not run with this description yet. -/
private def runPass : CommandElabM Unit := do
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let binding ← evalForkBinding bindingName
  let lines := generatorLines.getState env
  -- named lines, in file order; two for one theorem is an error (§14.3)
  let named := lines.filterMap fun l =>
    match l.kind with
    | .named thm strict seeds => some (thm, strict, seeds, l.presetIds)
    | _ => none
  for i in [0:named.size] do
    for j in [0:named.size] do
      if i < j then
        let (a, _, _, _) := named[i]!
        let (b, _, _, _) := named[j]!
        if a == b then
          throwError "theorem_vectors: two named lines select `{b}`; \
            one theorem runs once (§14.3)"
  let namedSet : NameSet :=
    named.foldl (init := {}) fun acc (thm, _, _, _) => acc.insert thm
  -- skips, with the reason each records
  let skipList : Array (Name × String) := lines.filterMap fun l =>
    match l.kind with
    | .skipped thm reason => some (thm, reason)
    | _ => none
  let skipSet : NameSet :=
    skipList.foldl (init := {}) fun acc (thm, _) => acc.insert thm
  -- discovery clauses: a kind contributes only when the file has its
  -- line, and the clause's presets are the line's (§14.3: the clause
  -- runs "with the default budget, the default seeds (none), and the
  -- clause's preset list")
  let discLines (kind : LineKind) : Array (Array PresetId) :=
    lines.filterMap fun l =>
      if l.kind.sameKind kind then some l.presetIds else none
  let rawChar :=
    if (discLines .characterized).isEmpty then NameSet.empty
    else discoverySet env binding .characterized
  let rawTag :=
    if (discLines .tagged).isEmpty then NameSet.empty
    else discoverySet env binding .tagged
  let rawSurvey :=
    if (discLines .survey).isEmpty then NameSet.empty
    else discoverySet env binding .survey
  let charPs := ((discLines .characterized).getD 0 #[PresetId.minimal])
  let tagPs := ((discLines .tagged).getD 0 #[PresetId.minimal])
  -- a skip for a theorem no discovery clause selects is an error (§14.3);
  -- the test reads the raw sets, because the selection below removes what
  -- the skip excludes
  for (thm, _) in skipList do
    unless rawChar.contains thm || rawTag.contains thm
        || rawSurvey.contains thm do
      throwError "theorem_vectors: `skip {thm}` selects a theorem no \
        discovery clause selects (§14.3)"
  -- selection with §14.3's precedence: a named line wins over discovery,
  -- a skip excludes a theorem from discovery, a tagged theorem's claim
  -- outranks its characterization, and the survey takes the residual
  let keep (thm : Name) : Bool :=
    !namedSet.contains thm && !skipSet.contains thm
  let sel : Array (Name × OutcomeOrigin × Bool × Array PresetId) :=
    (rawTag.foldl (init := (#[] : Array (Name × OutcomeOrigin × Bool × Array PresetId))) fun acc thm =>
        if keep thm then acc.push (thm, .tagged, true, tagPs) else acc) ++
      (rawChar.foldl (init := (#[] : Array (Name × OutcomeOrigin × Bool × Array PresetId))) fun acc thm =>
        if keep thm && !rawTag.contains thm then
          acc.push (thm, .characterized, false, charPs)
        else acc) ++
      (rawSurvey.foldl (init := (#[] : Array (Name × OutcomeOrigin × Bool × Array PresetId))) fun acc thm =>
        if keep thm && !rawTag.contains thm && !rawChar.contains thm then
          acc.push (thm, .survey, false, #[])
        else acc)
      |>.qsort fun a b => a.1.toString < b.1.toString
  -- execute: named lines first, in file order; then the discovered set in
  -- name order (§14.3). A theorem whose description already ran is
  -- skipped; each run records itself at once, so a repeated pass neither
  -- repeats it nor loses it.
  let runOnce (thm : Name) (origin : OutcomeOrigin) (strict : Bool)
      (ps : Array PresetId) (seeds : Array (Name × Syntax)) :
      CommandElabM Unit := do
    let key := execKey origin ps
    let env ← getEnv
    unless (executed.getState env).any fun (t, k) => t == thm && k == key do
      modifyEnv (executed.addEntry · (thm, key))
      runTheorem binding origin strict thm ps seeds
  for (thm, strict, seeds, ps) in named do
    runOnce thm .named strict ps seeds
  for (thm, origin, strict, ps) in sel do
    runOnce thm origin strict ps #[]
  -- a skipped theorem records its outcome too (§14.3)
  for (thm, reason) in skipList do
    recordSkip binding thm reason

/-! ## The command elaborators -/

@[command_elab tvForkCmd]
def elabTvFork : CommandElab := fun stx => do
  let bindingName ← liftCoreM <| resolveGlobalConstNoOverload stx[1]
  modifyEnv (forkHeader.addEntry · bindingName)
  -- a fresh outcome subtree per build: a theorem the fork's lines no
  -- longer name must not linger in the report (§16.2)
  let binding ← evalForkBinding bindingName
  let forkOut := EthCLLib.TheoremVectors.Outcome.dir (← outDirOf) binding.tag
  if ← forkOut.isDir then
    IO.FS.removeDirAll forkOut
  runPass

@[command_elab tvSkipCmd]
def elabTvSkip : CommandElab := fun stx => do
  -- `"theorem_vectors " "skip" ident str`: the `skip` atom sits at 1,
  -- the theorem at 2, the reason at 3
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let binding ← evalForkBinding bindingName
  let thm ← resolveThmName binding stx[2]
  let reason := stx[3].isStrLit?.getD ""
  modifyEnv (generatorLines.addEntry ·
    { kind := .skipped thm reason })
  runPass

/-- The discovery lines share one elab shape: the kind is fixed by which
rule parsed the line, and the presets clause sits at 2. -/
private def elabTvDiscovery (kind : LineKind) : CommandElab := fun stx => do
  let env ← getEnv
  let some _ := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let ps ← parsePresets stx[2]
  modifyEnv (generatorLines.addEntry · { kind, presetIds := ps })
  runPass

@[command_elab tvCharacterizedCmd]
def elabTvCharacterized : CommandElab := elabTvDiscovery .characterized

@[command_elab tvTaggedCmd]
def elabTvTagged : CommandElab := elabTvDiscovery .tagged

@[command_elab tvSurveyCmd]
def elabTvSurvey : CommandElab := fun _stx => do
  let env ← getEnv
  let some _ := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  modifyEnv (generatorLines.addEntry · { kind := .survey })
  runPass

/-- The seeds of a named line, as `(input, term)` pairs in source order.
The seed shape is `"(" ident " := " term ")`, wrapped by `many`'s node and
possibly by the parser's own group nodes, so the walk keys on the token
layout and not on a wrapper's kind. -/
private partial def parseSeeds (stx : Syntax) : Array (Name × Syntax) :=
  let here : Array (Name × Syntax) :=
    if stx.getNumArgs ≥ 4
        && stx.getArg 0 matches .atom _ "("
        && stx.getArg 2 matches .atom _ ":=" then
      #[Prod.mk (stx.getArg 1).getId (stx.getArg 3)]
    else #[]
  (stx.getArgs.flatMap parseSeeds) ++ here

/-- The seeded named lines' elab: the ident sits at 1, the `with` atom at
2, the seed group at 3, the presets clause at 4. -/
private def elabNamedLine (strict : Bool) : CommandElab := fun stx => do
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  -- resolve through the binding for the proof-namespace fallback
  let binding ← evalForkBinding bindingName
  let thm ← resolveThmName binding stx[1]
  let seeds := parseSeeds stx[3]
  let ps ← parsePresets stx[4]
  modifyEnv (generatorLines.addEntry ·
    { kind := .named thm strict seeds, presetIds := ps })
  runPass

/-- The seedless named lines' elab: the ident sits at 1, the presets
clause at 2, and there are no seeds (§14.3 defines seeds only through
`with`). -/
private def elabNamedNoSeedLine (strict : Bool) : CommandElab := fun stx => do
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let binding ← evalForkBinding bindingName
  let thm ← resolveThmName binding stx[1]
  let ps ← parsePresets stx[2]
  modifyEnv (generatorLines.addEntry ·
    { kind := .named thm strict #[], presetIds := ps })
  runPass

@[command_elab tvNamedStrictCmd]
def elabTvNamedStrict : CommandElab := elabNamedLine true

@[command_elab tvNamedStrictNoSeedCmd]
def elabTvNamedStrictNoSeed : CommandElab := elabNamedNoSeedLine true

@[command_elab tvNamedCmd]
def elabTvNamed : CommandElab := elabNamedLine false

@[command_elab tvNamedNoSeedCmd]
def elabTvNamedNoSeed : CommandElab := elabNamedNoSeedLine false

end EthCLLib.TheoremVectors
