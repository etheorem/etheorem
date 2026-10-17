import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Preset
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Reuse
import EthCLLib.TheoremVectors.Witness.Hint
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.Manual
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Witness.Built
import EthCLLib.TheoremVectors.Witness.Random
import EthCLLib.TheoremVectors.Witness.Shrink
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
theorem_vectors canBuilderCoverBid_iff with (state := Manual.Gloas.coverBidState)
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
overrode it. Two order rules follow from the line-at-a-time passes: a
`skip` line must precede the discovery clauses that select its theorem, or
the clause's pass runs the theorem first and the skip can only replace the
outcome; and a named line must precede the discovery clauses, because a
clause's pass runs the theorem without the manual terms. Each rule is an error
whose message names the fix. A `skip` validates against the *potential*
selection of §14.1's tags and the fork's proof namespace, so the line can
sit above the clauses it excludes from and a stale exclusion is still
visible. A line a precedence rule rejects leaves no state: the
elaborator records it only after the pass succeeded, so a later line
meets only the lines above it that passed.

**Stage 2.** A named or discovered theorem's run wires phases B1 through
B8 end to end for one preset: the prepare pass (§8.4's first form) builds
one disjunct, the probe compiles (§11.2), the manual and base searchers
search (§9.2, §9.4), the executor records `.eq` and `.bound` runs (§11.3), the
record round-trips (§12.5), and the outcome carries the real statuses.
`survey` runs phase A alone, with status `unselected` (§14.3), so the
report shows the whole corpus without searching anything.

One deviation from the sketch is recorded in `IMPLEMENTATION_NOTES.md`:
an `unsupported` outcome's shape field writes `unsupported`, because the
§16.1 example leaves the field's value for that row unspecified.

**Stage 5.** The hint searcher (§9.8) prepends itself to every list: the
run resolves the mode (`THEOREM_VECTORS_HINTS` ahead of the
`theorem_vectors.hints` option), loads the committed file, and hands the
searcher a log ref. A winning disjunct records its hint entry, where a
replay re-records the entry it consumed, and the run merges its entries into
`<outDir>/hints/<fork>/<thm>.json`. The outcome line folds the log
into its `hint` field. Mode `require` errors on a disjunct whose hint
failed the check or whose witness came from a search, which is the
committed file's broken promise; a disjunct that finds no witness at all
falls through, because no entry could have existed for it.

## Lean idioms annotated

- `SimpleScopedEnvExtension` with `exportEntry? := fun _ _ => none` is
  module-local state: the entries live for the current module and the
  `.olean` carries none of them, which is what makes a generator file's
  lines invisible to its importers.
- A `command` elaborator (`CommandElabM`) runs at `lake build` time with
  the full environment, which is why the pass can read theorem types
  (`Statement.readIn` runs `MetaM` under `liftTermElabM`), elaborate manual
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
  /-- A named line, with the manual terms its `with` spelled. -/
  | named (thm : Name) (strict : Bool) (manuals : Array (Name × Syntax))
  /-- A `skip` line, with its reason. -/
  | skipped (thm : Name) (reason : String)
  deriving Inhabited

/-- Kind equality, spelled out because the named line carries `Syntax`
manual terms and `Syntax` has no decidable equality. -/
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

-- the strict marker lives in the identifier token: the lexer reads
-- `theorem_vectors!` as one ident, so this atom and the plain form's
-- leading atom never collide. The manual and termless forms are separate
-- rules, so the manual terms and the presets clause sit at fixed indices.
scoped syntax (name := tvNamedStrictCmd)
  "theorem_vectors!" ident "with" many("(" ident " := " term ")")
  optional("presets " ident+) : command

-- §14.3 defines manual terms only through `with`, so the termless rules
-- take no manual-term group: a bare `(input := term)` group alone is a
-- parse error.
scoped syntax (name := tvNamedStrictNoManualCmd)
  "theorem_vectors!" ident optional("presets " ident+) : command

scoped syntax (name := tvNamedCmd)
  "theorem_vectors " ident "with" many("(" ident " := " term ")")
  optional("presets " ident+) : command

scoped syntax (name := tvNamedNoManualCmd)
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

/-- The committed hints root: the lakefile's weak setting, or the empty
default that means the fork commits no hints (§9.8). -/
private def hintsRootOf : CommandElabM String := do
  match ((← getOptions).get? `theorem_vectors.hintsDir : Option Lean.DataValue) with
  | some v => return v.str
  | none => return theorem_vectors.hintsDir.defValue

/-- The hint mode (§9.8): the `THEOREM_VECTORS_HINTS` variable reads
ahead of the `theorem_vectors.hints` option, which is how the rebuild
recipe overrides a declarative lakefile (§17.2). A set variable wins even
when it holds an unknown value, so a typo in the recipe is a build error
and never a silent `use`. -/
private def hintModeOf : CommandElabM HintMode := do
  let envVal ← IO.getEnv "THEOREM_VECTORS_HINTS"
  let opts ← getOptions
  let raw :=
    match envVal with
    | some v => v
    | none => theorem_vectors.hints.get opts
  match HintMode.ofTag? raw with
  | some m => pure m
  | none =>
    throwError "theorem_vectors: `{raw}` is not a hint mode; the values \
      are `use`, `ignore`, and `require` (§9.8)"

/-- The report line for one search failure (§18's reported facts). A
`notFound` on a theorem with block inputs is §18's `outOfScope`: only the
base searcher may run, it ran, and it failed (§1.2). The details the
searchers reported follow the searcher list. -/
private def failureOf (blockInputs : Array Name) : Failure →
    RunStatus × String
  | .unsat => (.unsat, "unsat: the hypotheses are vacuous")
  | .notFound tried details =>
    let detailText := if details.isEmpty then ""
      else s!" ({String.intercalate "; " details.toList})"
    if blockInputs.isEmpty then
      (.skipped, s!"notFound after {String.intercalate ", "
        (tried.toList.map (·.tag))}{detailText}")
    else
      (.outOfScope, s!"outOfScope: block inputs {String.intercalate ", "
        (blockInputs.toList.map (·.toString))} and the base searcher \
        failed ({String.intercalate ", " (tried.toList.map (·.tag))})\
        {detailText}")
  | .outOfScope inputs =>
    (.outOfScope, s!"outOfScope: block inputs {String.intercalate ", "
      (inputs.toList.map (·.toString))} and the base searcher failed")

/-- One run's heartbeat budget (§14.3, §14.4): the option's value, with the
heartbeat clock reset at the run's start, so one line's solver calls and
compiled-read evaluations never share a budget with the theorems beside it.
The budget is a `Core.Context` reader field, and the reset follows the
toolchain's own `Lean.Core.withCurrHeartbeats`. -/
private def withRunHeartbeats {α : Type} (x : MetaM α) : MetaM α := do
  let budget := theorem_vectors.maxHeartbeats.get (← getOptions) * 1000
  let now ← IO.getNumHeartbeats
  withTheReader Lean.Core.Context (fun ctx =>
      { ctx with maxHeartbeats := budget, initHeartbeats := now }) x

/-- Does this winning searcher's witness go through the shrink loop? A
random-searcher witness does, and so does its replayed hint (§9.8: shrink
replays from the same draw). The other searchers' witnesses are the
author's manual terms, the defaults, and the solver's boundary values,
and shrinking moves all three. -/
private def shrinkableSearcher : WitnessSearcherTag → Bool
  | .random => true
  | .hinted (.random) => true
  | _ => false

/-- One phase-B run of one theorem at one preset (`THEOREM_VECTORS_ARCHITECTURE.md`
§3's B1 through B8). Runs inside the reader's telescope scope: the manual
terms still carry the telescope's instance variables, and the probe builds
from the statement's expressions. The hint mode and the committed hint
file come from the run (`runTheorem` resolved both once per theorem). -/
private def runPreset (binding : ForkBinding) (outDir : System.FilePath)
    (thmLocal : String) (manualTerms : Array (Nat × Expr)) (builtStamp : String)
    (winsRef : IO.Ref (Array ReuseWin)) (p : PresetId) (ctx : StatementCtx)
    (disjuncts : Array Disjunct) (mode : HintMode) (hintFile? : Option HintFile) :
    MetaM RunOutcome := do
  let stmt := ctx.stmt
  let startMs ← IO.monoMsNow
  -- B0: the executor runs every conclusion shape (§11.3). Phase A
  -- reports an `.unsupported` statement before phase B starts, so the
  -- gate answers `none` on every shape today; a future unrunnable shape
  -- would answer `some` reason here
  if let some stage := Execute.handles? stmt.shape then
    return { preset := some p, status := .skipped, reason := some stage }
  if disjuncts.isEmpty then
    return { preset := some p, status := .skipped,
             reason := some "the prepare pass produced no disjunct" }
  -- B1: the probe for this preset (§10, §11). An `.error` answer is a
  -- skip reason, a fact about the theorem or the shape.
  let (info, probe) ← match ← Probe.ofStatement binding p ctx disjuncts manualTerms with
    | .ok r => pure r
    | .error reason =>
      return { preset := some p, status := .skipped, reason := some reason }
  -- §10: the instance constants this preset fixes, which the bit-vector
  -- searcher substitutes into the manual terms and the reads (§11.2)
  let instConsts ← ctx.stmt.instances.mapM fun (_, kind) =>
    match Preset.constOf binding p kind with
    | .ok c => pure c
    | .error e => throwError e
  -- §9.9: the grid's boundary steps run at the fork's own first epoch
  -- boundary, evaluated once per preset run
  let epochBoundary ← Built.epochBoundaryOf binding p
  -- §10: the preset-free type check gates witness reuse. The command
  -- fills the search context's table only when every input type is free
  -- of the preset, so a nonempty table implies the check; a preset-bound
  -- statement always searches fresh, which is always correct
  let presetFree := Preset.presetFree (← getEnv) binding ctx
  let wins ← if presetFree then winsRef.get else pure #[]
  let searchCtx : SearchCtx :=
    { probe, info, binding, preset := p, inputFvars := ctx.inputFvars,
      instFvars := ctx.instFvars, instConsts, manualTerms,
      drawMemo := ← IO.mkRef #[], outDir, builtStamp, epochBoundary,
      earlierWins := wins }
  -- §9.8: the hint searcher runs first on every list. The log ref collects
  -- what one attempt did per disjunct, which the outcome's `hint` field folds
  -- up and which the `require` mode's error reads.
  let fingerprint := Hint.fingerprint stmt.thm info
  let hintLog ← IO.mkRef (#[] : Array (Nat × HintAttempt))
  let hintSearcher := Hint.searcher mode hintFile? fingerprint hintLog
  -- a fresh record directory per run: an overriding line's pass replaces
  -- the records an earlier pass wrote for the same theorem (§14.3)
  let thmDir := Record.thmDir outDir binding.tag p thmLocal
  if ← thmDir.isDir then
    IO.FS.removeDirAll thmDir
  -- B3: the search (§9.2, §9.4). The hint searcher prepends itself on
  -- every list, `ignore` included off it. §10 puts the reuse searcher
  -- immediately after the hint searcher, so a committed second-preset
  -- hint replays as
  -- `.hinted (.reused p)` while a fresh run wins as
  -- `.reused p` and writes that entry. A line with manual terms runs
  -- manual then the bit-vector handoff: a `default` candidate would
  -- ignore the author's fixed inputs. Without manual terms, base then
  -- bit-vector. The built searcher (§9.9) follows the bit-vector
  -- searcher, before the random searcher: a reachable built state is worth
  -- more to a client than a drawn one. A block input leaves only the base
  -- searcher running (§1.2); the base searcher itself never proposes
  -- `default` for the fork's state (§9.4), so a state theorem without
  -- manual terms runs the bit-vector, built, and random searchers in that
  -- order. The
  -- reuse searcher's `applies` gates on empty block inputs itself, so the
  -- block-input list stays base alone.
  let baseSearchers : Array WitnessSearcher :=
    if !stmt.blockInputs.isEmpty then #[baseSearcher]
    else if manualTerms.isEmpty then
      #[baseSearcher, bitVecSearcher, builtSearcher, randomSearcher]
    else #[manualSearcher, bitVecSearcher, builtSearcher, randomSearcher]
  let searchers : Array WitnessSearcher :=
    -- `ignore` runs no hint, so the reuse searcher leads the list; §9.8's
    -- "search everything" covers reuse, and a `use` build must read the
    -- same second-preset entries an `ignore` build writes (§9.8)
    if mode == .ignore then #[reuseSearcher] ++ baseSearchers
    else #[hintSearcher, reuseSearcher] ++ baseSearchers
  let some shapeTag := Shape.tag? stmt.shape
    | return { preset := some p, status := .unsupported,
               reason := some "unsupported shape" }
  -- §9.8: mode `require` turns a failing hint into the build error the
  -- mode promises. A disjunct that found no witness carries no claim the
  -- mode can enforce (§9.4: the manual terms' claim is the author's; a
  -- disjunct no searcher wins reports `notFound`), so it falls through; a
  -- disjunct that won
  -- from a searcher other than the hint, or whose hint the check rejected,
  -- is the error, because the committed file promised this disjunct a witness
  let enforceRequireHint (d : Disjunct) (win? : Option Bool) : MetaM Unit := do
    if mode == .require then
      let logged ← hintLog.get
      let attempt? := logged.find? fun (i, _) => i == d.index
      let hintFailed := attempt?.any fun (_, a) =>
        a == .failed || a == .staleFailed
      let hintReplayed := attempt?.any fun (_, a) =>
        a == .replayed || a == .staleReplayed
      let wrong := hintFailed ||
        (win?.getD false && !hintReplayed)
      if wrong then
        throwError "theorem_vectors: mode `require`: the hint for disjunct \
          {d.index} of `{stmt.thm}` at {p.tag} is missing or failed the \
          check (§9.8)"
  let mut written : Nat := 0
  let mut searcher? : Option String := none
  let mut manualWon := false
  let mut hintEntries : Array HintEntry := #[]
  let mut freshWins : Nat := 0
  let mut failures : Array (Nat × RunStatus × String) := #[]
  for d in disjuncts do
    -- the plan's stage-6 step 9: a notFound entry the run's own
    -- fingerprint covers is the run's own past answer, so `use` and
    -- `require` modes take it and skip the search; a stale one, or
    -- `ignore` mode, searches
    let skippedNotFound : Option HintEntry := do
      guard (mode != .ignore)
      let f ← hintFile?
      let e ← Hint.entryFor f p d.index d.side
      guard (e.notFound.isSome && (e.fingerprint.getD f.fingerprint) == fingerprint)
      pure e
    if let some e := skippedNotFound then
      -- the replayed answer: the hint log's `.replayed` folds the
      -- outcome's `hint` field to `replayed`, and the failure reads as
      -- the search's own. The consumed entry re-records into the run's
      -- file, so the skip survives the update recipe instead of living
      -- one build.
      hintLog.set ((← hintLog.get) ++ #[(d.index, HintAttempt.replayed)])
      hintEntries := hintEntries.push e
      let tried := (e.notFound.getD #[]).filterMap WitnessSearcherTag.ofTag?
      let (status, text) := failureOf stmt.blockInputs (.notFound tried #[])
      let reason := (e.notFoundReason.getD text)
      failures := failures.push (d.index, status,
        s!"{reason} (replayed from the hint)")
      continue
    match ← searchDisjunct searchers searchCtx stmt d with
    | .error failure =>
      enforceRequireHint d none
      let (status, text) := failureOf stmt.blockInputs failure
      failures := failures.push (d.index, status, text)
      -- the plan's stage-6 step 9: a disjunct every searcher failed
      -- records the fact, so the next build skips its search while the
      -- fingerprint stands. The search ran, so the answer is the run's
      -- own fact, and `ignore` mode records it the way it records found
      -- entries, which keeps the rebuild recipe's output in step with
      -- the committed files. A block input's disjunct records none: its
      -- search is the one base check, there is nothing to skip, and
      -- §1.2 already reports it.
      match failure with
      | .notFound tried _ =>
        if stmt.blockInputs.isEmpty then
          let entry : HintEntry :=
            { preset := p, disjunctIndex := d.index, side := d.side,
              witnessSearcher := .base,
              notFound := some (tried.map (·.tag)),
              notFoundReason := some text,
              fingerprint := some fingerprint }
          hintEntries := hintEntries.push entry
      | _ => pure ()
    | .ok (a, won) =>
      enforceRequireHint d (some (!(won matches .hinted _)))
      -- §9.8: the hint entry records the pre-shrink assignment, whose
      -- container bytes the draw memo still holds; the solver's scalars
      -- are the shrink's boundary, so the entry is the shrunk witness's
      -- too
      let seedOpt := theorem_vectors.seed.get (← getOptions)
      let sizeOpt := theorem_vectors.randomSize.get (← getOptions)
      -- §9.8: a replay re-records the entry it consumed, so the file a
      -- replayed build writes is the file it read; a fresh win records
      -- the candidate the search found (before the shrink, whose
      -- container cuts the draw memo does not hold)
      let entry? ←
        match won with
        | .hinted _ =>
          -- a replay re-records the entry it consumed, stamped with the
          -- current fingerprint: the replay is the refresh (§9.8)
          pure (match hintFile? with
            | none => none
            | some f =>
              (Hint.entryFor f p d.index d.side).map
                fun e => { e with fingerprint := some fingerprint })
        | _ => Hint.entryOf searchCtx stmt d a won seedOpt sizeOpt fingerprint
      -- §9.6: a witness from the random searcher shrinks while the check
      -- holds, within the step budget, and so does its replayed hint
      -- (§9.8: shrink replays from the same draw), which is what keeps
      -- the replay's records byte-identical. The other searchers'
      -- witnesses are the author's manual terms, the defaults, and the
      -- solver's boundary values, and shrinking moves all three. A
      -- replayed random entry carries its shrink path (the plan's
      -- stage-6 step 8), and the replay walks the recorded candidates
      -- alone.
      let shrinkable := shrinkableSearcher won
      let mut shrinkTrace? : Option (Array (Array Nat)) := none
      let a ← if shrinkable then do
        let steps := theorem_vectors.shrinkSteps.get (← getOptions)
        match won with
        | .hinted _ =>
          let recorded := do
            let f ← hintFile?
            (Hint.entryFor f p d.index d.side).bind (·.shrink)
          match recorded with
          | some trace =>
            let r ← shrinkReplayWitness probe d.index trace a
            match r with
            | some shrunk =>
              shrinkTrace? := some trace
              pure shrunk
            | none =>
              -- a recorded path the candidate list no longer reaches:
              -- the replayed draw stands, the full walk re-derives the
              -- endpoint, and the refreshed entry records the walk's own
              -- path
              let (shrunk, tr) ← shrinkTraceWitness probe d.index steps a
              shrinkTrace? := some tr
              pure shrunk
          | none =>
            let (shrunk, tr) ← shrinkTraceWitness probe d.index steps a
            shrinkTrace? := some tr
            pure shrunk
        | _ =>
          let (shrunk, tr) ← shrinkTraceWitness probe d.index steps a
          shrinkTrace? := some tr
          pure shrunk
      else pure a
      -- §10: the final assignment that passed the check goes into the
      -- ref, so a later preset of this line proposes it through the
      -- reuse searcher. A `.reused` win lands here too: it passed this
      -- preset's check, so the next preset may try the same bytes, and
      -- that preset's own check arbitrates. The push runs only for a
      -- preset-free statement: the read side gates on the same flag, so
      -- a preset-bound win would sit in the ref with no reader and only
      -- cost memory.
      if presetFree then
        winsRef.set ((← winsRef.get).push
          { disjunctIndex := d.index, side := d.side, assignment := a,
            fromPreset := p })
      let entry? := match entry? with
        | some e => some { e with shrink := shrinkTrace? }
        | none => none
      unless won matches .hinted _ do
        freshWins := freshWins + 1
      if let some e := entry? then
        hintEntries := hintEntries.push e
      -- B5: run, and execute the shape's row (§11.3). A disagreement or a
      -- probe failure is a build error, per §18.
      let r ← match probe.run a with
        | .ok r => pure r
        | .error e =>
          throwError "theorem_vectors: the probe failed to run \
            `{stmt.thm}`: {e}"
      let (outVal, errVal) ← Execute.output stmt.thm stmt.shape info r
      let inputVals : Array VectorValue ←
        (Array.range info.inputNames.size).mapM fun i =>
          VectorValue.ofRun info.inputNames[i]! info.inputTypes[i]!
            (r.inputLiterals.getD i none) (r.inputRoots.getD i none)
      let record : VectorRecord :=
        { «theorem» := stmt.thm, fork := binding.tag, preset := p,
          target := stmt.target, specName := stmt.specName,
          shape := shapeTag,
          disjunctIndex := d.index, side := d.side,
          inputs := inputVals, output := outVal, error := errVal,
          witnessSearcher := won }
      -- B6: write the record (§12.1, §12.4); the assignment's bytes are
      -- the record's bytes, and a record with no output (`.runError`)
      -- writes no `output.ssz` (§12.1)
      let dir := Record.disjunctDir outDir binding.tag p thmLocal d.index d.side
      Record.write outDir binding.tag record thmLocal a
        (record.output.map fun _ => r.output)
      -- B7: read the directory back and run the probe on the stored bytes
      -- (§12.5). This checks the SSZ round trip of every value and the
      -- record writer itself; a mismatch is a build error (§18).
      let rb ← Record.read dir
      match probe.run rb.inputBytes with
      | .error e =>
        throwError "theorem_vectors: the read-back of `{stmt.thm}` disjunct \
          {d.index} failed to decode: {e}"
      | .ok r2 =>
        unless compareBytes r2.output (rb.outputBytes.getD emptyBytes) do
          throwError "theorem_vectors: the read-back of `{stmt.thm}` disjunct \
            {d.index} disagrees with the recorded output (§12.5): \
            recorded {EthCLLib.TheoremVectors.hexOf
              (rb.outputBytes.getD emptyBytes)}, \
            fresh {EthCLLib.TheoremVectors.hexOf r2.output}"
      -- §14.3: one info line per record, with the path
      logInfo m!"theorem_vectors [{binding.tag}] {stmt.thm}: record \
        {dir}"
      written := written + 1
      -- §16.1 pairs the run's searcher with its hint answer: the origin
      -- the hint replayed, the record's own field carrying the
      -- `.hinted` wrapper (§5.4)
      let searcherTag := match won with
        | .hinted o => o.tag
        | t => t.tag
      if searcher?.isNone then searcher? := some searcherTag
      -- a replayed manual win counts for §18's manual claim, the same
      -- way its original win did (§9.8)
      if won == .manual || won matches .hinted (.manual) then
        manualWon := true
  let endMs ← IO.monoMsNow
  let seconds := some ((endMs - startMs).toFloat / 1000.0)
  -- §9.8: the run's entries merge into the output tree's hint file, and
  -- the outcome line folds the attempts into its `hint` field
  let hintField := Hint.runHintField mode hintFile? p disjuncts.size freshWins
    (← hintLog.get)
  -- §9.8: the run's entries merge into the output tree's hint file,
  -- whether or not the run won anything: an overriding line that wins
  -- nothing replaces the preset's stored entries with none, so a
  -- survey's candidate never outlives the line that overrode it
  Hint.mergeWrite outDir binding.tag thmLocal p
    { «theorem» := stmt.thm, fingerprint, entries := hintEntries }
  -- §18: a fully-covering set of manual terms that wins no disjunct
  -- breaks the build, because the author claimed it works; a partial
  -- failure falls through (§9.4)
  if !manualTerms.isEmpty && manualTerms.size == stmt.inputs.size && !manualWon then
    throwError "theorem_vectors: the manual terms of `{stmt.thm}` win no \
      disjunct at {p.tag}; fix the manual term or drop the `with` clause \
      (§9.4, §18)"
  let failureText := String.intercalate "; "
    (failures.toList.map fun (i, _, text) => s!"disjunct {i}: {text}")
  if written > 0 then
    return { preset := some p, status := .written, records := written,
             witnessSearcher := searcher?, hint := hintField, seconds,
             reason := if failures.isEmpty then none
                       else some failureText }
  else
    -- every disjunct failed: the status is the §18 fact the failures name
    let status : RunStatus :=
      if failures.any fun (_, st, _) => st == .unsat then .unsat
      else if failures.any fun (_, st, _) => st == .outOfScope then
        .outOfScope
      else .skipped
    return { preset := some p, status, hint := hintField,
             reason := some failureText }

/-- The stage-2 run of one theorem: phase A, then phases B1 through B8 per
preset (§3, and the module docstring). The whole fold runs inside the
reader's telescope scope (`Statement.readIn`), because the statement's
expressions and the manual terms cannot leave it. `binding` is the header's
value and `bindingName` its constant, whose parent names the module the
built cache's stamp reads (§9.9); the binding value carries no name of
its own. -/
private def runTheorem (binding : ForkBinding) (bindingName : Name)
    (origin : OutcomeOrigin)
    (strict : Bool) (thm : Name) (ps : Array PresetId)
    (manualStx : Array (Name × Syntax)) : CommandElabM Unit := do
  let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
  let localName := thm.replacePrefix proofNs .anonymous
  let outDir ← outDirOf
  -- §9.8: the hint mode and the committed file resolve once per theorem
  -- and pass down to every preset's run
  let mode ← hintModeOf
  let hintFile? : Option HintFile ← do
    let root ← hintsRootOf
    if root.isEmpty then pure none
    else liftIO <| Hint.read? (Hint.file root binding.tag localName.toString)
  -- §9.9: the built searcher's cache stamp, the binding module's trace
  -- text, read once per theorem. The binding module imports the fork's
  -- Builders module, so its trace folds the builders' artifacts beside
  -- the fork body and the crypto seams the binding names, and a change
  -- to any of them invalidates the cache at once.
  let builtStamp ← liftIO (Built.stampOfBinding bindingName)
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
            origin, blockInputs := stmt.blockInputs, disjuncts := 0, runs }
        Outcome.write outDir binding.tag outcome localName.toString
        logInfo m!"theorem_vectors [{binding.tag}] {thm}: \
          unsupported ({r})"
        -- §18: a claim the author made fails hard
        if strict then
          throwError "theorem_vectors: `{thm}` carries a claim (`!` or \
            `@[theorem_vectors]`) and the reader reported: {r}"
      | none =>
        -- phase A: prepare (§8.4's first form)
        let (disjuncts, dropped) ← Prepare.pass stmt
        -- the author's manual terms (§14.3: "[Preset]-generic,
        -- elaborated at each preset"): each term elaborates against its
        -- input's type inside the telescope, so the theorem's own
        -- instances fill the term's instance binders and
        -- `substInstances` fixes them per preset. A term for an input
        -- the theorem does not have is an error here, and a term of the
        -- wrong type is an elaboration error at the clause: §18's build
        -- error for an author claim.
        let manualTerms ← manualStx.mapM fun (n, stx) => do
          match stmt.inputs.findIdx? (fun i => i.name == n) with
          | none =>
            throwError "theorem_vectors: the manual term names input \
              `{n}`, which `{thm}` does not have (§14.3)"
          | some i => do
            let t := stmt.inputs[i]!.type
            -- the expected type fills the manual term's `[Preset]`-generic
            -- instance binders from the telescope; the check below holds
            -- the §18 line: a manual term of the wrong type is an error
            -- at the clause, because the author claimed it works
            let term ←
              (Lean.Elab.Term.withoutErrToSorry
                (Lean.Elab.Term.elabTermAndSynthesize stx (some t))).run'
            let term ← Lean.instantiateMVars term
            unless ← Meta.isDefEq (← Meta.inferType term) t do
              throwError "theorem_vectors: the manual term for `{n}` of \
                `{thm}` does not have the input's type (§14.3)"
            pure (i, term)
        -- phases B1 through B8, per preset in the line's list, each under
        -- its own heartbeat budget (§14.3). §10: the fold carries one
        -- earlier-wins ref across the line's presets, so a witness won at
        -- an earlier preset proposes at a later one when the preset-free
        -- type check and the later preset's check both pass.
        let winsRef ← IO.mkRef (#[] : Array ReuseWin)
        let runs ← ps.foldlM (init := #[]) fun acc p => do
          let r ← withRunHeartbeats
            (runPreset binding outDir localName.toString manualTerms builtStamp
              winsRef p ctx disjuncts mode hintFile?)
          pure (acc.push r)
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
            blockInputs := stmt.blockInputs, disjuncts := disjuncts.size,
            runs }
        Outcome.write outDir binding.tag outcome localName.toString
        logInfo m!"theorem_vectors [{binding.tag}] {thm}: shape \
          {stmt.shape.wire}, {disjuncts.size} disjunct(s), origin
          {origin.tag}"
        -- §8.4: a dropped disjunct is reported
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
      origin := .skipped, blockInputs := #[], disjuncts := 0,
      runs := #[{ preset := some .minimal, status := .skipped,
                  reason := some reason }] }
  Outcome.write outDir binding.tag outcome localName.toString

/-- The pass's description key for one theorem, so an overriding line
re-runs it and nothing else does. -/
private def execKey (origin : OutcomeOrigin) (ps : Array PresetId) : String :=
  origin.tag ++ ":" ++ String.intercalate "," (ps.toList.map (·.tag))

/-- The whole-file precedence pass (§14.3, and the module docstring).
Resolves the file's selection against the lines seen so far and runs what
has not run with this description yet.

The caller passes the line list with its own line already appended, and
the elaborator records the line only after the pass returns, so a line a
precedence rule rejects leaves no state (see the module docstring). -/
private def runPass (lines : Array Line) : CommandElabM Unit := do
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let binding ← evalForkBinding bindingName
  -- named lines, in file order; two for one theorem is an error (§14.3)
  let named := lines.filterMap fun l =>
    match l.kind with
    | .named thm strict manuals => some (thm, strict, manuals, l.presetIds)
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
  -- §14.3: a named line and a skip line for one theorem contradict. The
  -- skip would overwrite the named run's outcome and leave its records
  -- with no outcome that names them.
  for (thm, _, _, _) in named do
    if skipSet.contains thm then
      throwError "theorem_vectors: `{thm}` has a named line and a skip \
        line; one or the other (§14.3)"
  -- §14.3: the named lines come before the discovery clauses. A discovery
  -- clause above a named line already ran its theorem without the manual
  -- terms and warned; the message names the fix. The same rule holds
  -- for a skip line: above the clauses, or the clause's pass ran the
  -- theorem first.
  let discoveryRan (thm : Name) : Bool :=
    (executed.getState env).any fun (t, k) =>
      t == thm && (k.startsWith "tagged:" || k.startsWith "characterized:" ||
        k.startsWith "survey:")
  for (thm, _, _, _) in named do
    if discoveryRan thm then
      throwError "theorem_vectors: `{thm}` already ran under a discovery \
        clause above this line; move the named line above the discovery \
        clauses (§14.3)"
  -- a skip validates against the potential selection (§14.1's tags and
  -- the fork's proof namespace), so the line can sit above the clauses it
  -- excludes from and a stale exclusion is still visible
  let potential : NameSet :=
    (discoverySet env binding .characterized).insertMany
      (discoverySet env binding .tagged) |>.insertMany
      (discoverySet env binding .survey)
  for (thm, _) in skipList.reverse do
    -- the loop walks the lines newest first, so the message names the
    -- line the user just wrote
    if discoveryRan thm then
      throwError "theorem_vectors: `{thm}` already ran under a discovery \
        clause above this skip line; move the skip line above the \
        discovery clauses (§14.3)"
    unless potential.contains thm do
      throwError "theorem_vectors: `skip {thm}` selects a theorem no \
        discovery clause selects (§14.3)"
  -- discovery clauses: a kind contributes only when the file has its
  -- line, and the clause's presets are the line's (§14.3: the clause
  -- runs with the default budget, no manual terms, and the clause's own
  -- preset list)
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
      (ps : Array PresetId) (manuals : Array (Name × Syntax)) :
      CommandElabM Unit := do
    let key := execKey origin ps
    let env ← getEnv
    unless (executed.getState env).any fun (t, k) => t == thm && k == key do
      modifyEnv (executed.addEntry · (thm, key))
      runTheorem binding bindingName origin strict thm ps manuals
  for (thm, strict, manuals, ps) in named do
    runOnce thm .named strict ps manuals
  for (thm, origin, strict, ps) in sel do
    runOnce thm origin strict ps #[]
  -- a skipped theorem records its outcome too (§14.3)
  for (thm, reason) in skipList do
    recordSkip binding thm reason

/-- Run one line's pass, then record the line: a line a precedence rule
rejects leaves no state behind. -/
private def addLine (line : Line) : CommandElabM Unit := do
  let lines := generatorLines.getState (← getEnv)
  runPass (lines.push line)
  modifyEnv (generatorLines.addEntry · line)

/-! ## The command elaborators -/

@[command_elab tvForkCmd]
def elabTvFork : CommandElab := fun stx => do
  let bindingName ← liftCoreM <| resolveGlobalConstNoOverload stx[1]
  modifyEnv (forkHeader.addEntry · bindingName)
  -- a fresh outcome subtree per build: a theorem the fork's lines no
  -- longer name must not linger in the report (§16.2)
  let binding ← evalForkBinding bindingName
  let outDir ← outDirOf
  -- a fresh outcome and record subtree per build: a theorem the fork's
  -- lines no longer name must not linger in the report or the render pass
  -- (§16.2)
  let forkOut := EthCLLib.TheoremVectors.Outcome.dir outDir binding.tag
  if ← forkOut.isDir then
    IO.FS.removeDirAll forkOut
  let forkRecords := EthCLLib.TheoremVectors.Record.dir outDir / binding.tag
  if ← forkRecords.isDir then
    IO.FS.removeDirAll forkRecords
  -- §9.8: the hints subtree clears with the outcomes, so the update
  -- recipe never copies a theorem's stale file over the committed one
  let forkHints := EthCLLib.TheoremVectors.Hint.dir outDir binding.tag
  if ← forkHints.isDir then
    IO.FS.removeDirAll forkHints
  runPass (generatorLines.getState (← getEnv))

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
  addLine { kind := .skipped thm reason }

/-- The discovery lines share one elab shape: the kind is fixed by which
rule parsed the line, and the presets clause sits at 2. -/
private def elabTvDiscovery (kind : LineKind) : CommandElab := fun stx => do
  let env ← getEnv
  let some _ := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let ps ← parsePresets stx[2]
  addLine { kind, presetIds := ps }

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
  addLine { kind := .survey }

/-- The manual terms of a named line, as `(input, term)` pairs in source
order. The term shape is `"(" ident " := " term ")`, wrapped by `many`'s
node and possibly by the parser's own group nodes, so the walk keys on
the token layout and not on a wrapper's kind. -/
private partial def parseManuals (stx : Syntax) : Array (Name × Syntax) :=
  let here : Array (Name × Syntax) :=
    if stx.getNumArgs ≥ 4
        && stx.getArg 0 matches .atom _ "("
        && stx.getArg 2 matches .atom _ ":=" then
      #[Prod.mk (stx.getArg 1).getId (stx.getArg 3)]
    else #[]
  (stx.getArgs.flatMap parseManuals) ++ here

/-- The manual named lines' elab: the ident sits at 1, the `with` atom at
2, the manual-term group at 3, the presets clause at 4. -/
private def elabNamedLine (strict : Bool) : CommandElab := fun stx => do
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  -- resolve through the binding for the proof-namespace fallback
  let binding ← evalForkBinding bindingName
  let thm ← resolveThmName binding stx[1]
  let manuals := parseManuals stx[3]
  let ps ← parsePresets stx[4]
  addLine { kind := .named thm strict manuals, presetIds := ps }

/-- The termless named lines' elab: the ident sits at 1, the presets
clause at 2, and there are no manual terms (§14.3 defines them only
through `with`). -/
private def elabNamedNoManualLine (strict : Bool) : CommandElab := fun stx => do
  let env ← getEnv
  let some bindingName := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  let binding ← evalForkBinding bindingName
  let thm ← resolveThmName binding stx[1]
  let ps ← parsePresets stx[2]
  addLine { kind := .named thm strict #[], presetIds := ps }

@[command_elab tvNamedStrictCmd]
def elabTvNamedStrict : CommandElab := elabNamedLine true

@[command_elab tvNamedStrictNoManualCmd]
def elabTvNamedStrictNoManual : CommandElab := elabNamedNoManualLine true

@[command_elab tvNamedCmd]
def elabTvNamed : CommandElab := elabNamedLine false

@[command_elab tvNamedNoManualCmd]
def elabTvNamedNoManual : CommandElab := elabNamedNoManualLine false

end EthCLLib.TheoremVectors
