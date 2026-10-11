import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Outcome
import EthCLLib.Internal.ProofLedger

/-!
# `EthCLLib.TheoremVectors.Command`: the generator commands

The generator-file surface (`THEOREM_VECTORS_ARCHITECTURE.md` §14):

```lean
theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Gloas.gloas

theorem_vectors characterized
theorem_vectors tagged
theorem_vectors probe
theorem_vectors canBuilderCoverBid_iff with (state := Seeds.Gloas.coverBidState)
theorem_vectors! processBuilderPendingPayments_run presets minimal mainnet
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

**Stage 1.** A theorem's run is phase A only: read the statement (§7),
classify its scope, write the outcome with status `unsupported` where the
reader gave a reason and the placeholder `pending` otherwise, and log one
info line. No witness is searched. Stage 2 fills the search and the real
statuses.

Two spellings deviate from §14.3's grammar, both recorded in
`IMPLEMENTATION_NOTES.md`:

- the `probe` clause. The plan's stage 1 reads, classifies, and lists every
  public theorem of the fork (its goal, its acceptance, and decision point
  A all need the whole corpus), and §14.3's discovery grammar has no
  whole-corpus clause. `probe` selects every public theorem under the
  fork's proof namespace that no other clause or line selects, with origin
  `probe`. The generator files drop it when stage 2 wires the search, and
  the `probe` origin value goes unused with it.
- an `unsupported` outcome's shape field writes `unsupported`, because the
  §16.1 example leaves the field's value for that case unspecified.

## Lean idioms annotated

- `SimpleScopedEnvExtension` with `exportEntry? := fun _ _ => none` is
  module-local state: the entries live for the current module and the
  `.olean` carries none of them, which is what makes a generator file's
  lines invisible to its importers.
- A `command` elaborator (`CommandElabM`) runs at `lake build` time with
  the full environment, which is why the pass can read theorem types
  (`Statement.read` runs `MetaM` under `liftTermElabM`) and write files.
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
  /-- `theorem_vectors probe`: the stage-1 sizing clause, every public
  theorem under the fork's proof namespace. See the module docstring. -/
  | probe
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
  | .probe, .probe => true
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

scoped syntax (name := tvProbeCmd)
  "theorem_vectors " "probe" optional("presets " ident+) : command

scoped syntax (name := tvSkipCmd)
  "theorem_vectors " "skip" ident str : command

-- the strict marker rides on the identifier token: the lexer reads
-- `theorem_vectors!` as one ident, so this atom and the plain form's
-- leading atom never collide, and the children sit at the same indices
scoped syntax (name := tvNamedStrictCmd)
  "theorem_vectors!" ident many("(" ident " := " term ")")
  optional("presets " ident+) : command

scoped syntax (name := tvNamedCmd)
  "theorem_vectors " ident many("(" ident " := " term ")")
  optional("presets " ident+) : command

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
and constants. `probe` enumerates the public theorems under the fork's
proof namespace (§14.1, §14.3, and the module docstring). -/
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
  | .probe =>
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

/-- The stage-1 run of one theorem: phase A only (the module docstring).
Reads the statement, classifies the scope, writes the outcome, and logs
one info line. The whole fold runs inside the reader's telescope scope
(`Statement.readIn`), because the statement's expressions cannot leave it. -/
private def runTheorem (binding : ForkBinding) (origin : OutcomeOrigin)
    (strict : Bool) (thm : Name) (ps : Array PresetId) :
    CommandElabM Unit := do
  let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
  let localName := thm.replacePrefix proofNs .anonymous
  let outDir ← outDirOf
  liftTermElabM do
    Statement.readIn binding thm fun stmt => do
      let stmt ← Scope.classify binding stmt
      let (status, reason) :=
        match stmt.shape.reason? with
        | some r => (RunStatus.unsupported, some r)
        | none => (RunStatus.pending, none)
      let runs := ps.map fun p =>
        { preset := p, status, reason }
      let outcome : Outcome :=
        { «theorem» := thm, target := stmt.target, shape := stmt.shape.wire,
          origin, blockInputs := stmt.blockInputs, cases := 0, runs }
      Outcome.write outDir binding.tag outcome localName.toString
      logInfo m!"theorem_vectors [{binding.tag}] {thm}: shape \
        {stmt.shape.wire}, {status.tag}, origin {origin.tag}"
      -- §18: a claim the author made fails hard; the placeholder does not
      if strict && status matches .unsupported then
        throwError "theorem_vectors: `{thm}` carries a claim (`!` or \
          `@[theorem_vectors]`) and the reader reported: \
          {reason.getD "unsupported"}"

/-! ## The whole-file precedence pass -/

/-- The outcome a `skip` line records: origin `skipped` with the line's
reason, one placeholder run per default preset. -/
private def recordSkip (binding : ForkBinding) (thm : Name)
    (reason : String) : CommandElabM Unit := do
  let proofNs := EthCLLib.Internal.proofNamespaceOf binding.fork
  let localName := thm.replacePrefix proofNs .anonymous
  let outDir ← outDirOf
  let outcome : Outcome :=
    { «theorem» := thm, target := none, shape := "unsupported",
      origin := .skipped, blockInputs := #[], cases := 0,
      runs := #[{ preset := .minimal, status := .skipped,
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
  let rawProbe :=
    if (discLines .probe).isEmpty then NameSet.empty
    else discoverySet env binding .probe
  let charPs := ((discLines .characterized).getD 0 #[PresetId.minimal])
  let tagPs := ((discLines .tagged).getD 0 #[PresetId.minimal])
  let probePs := ((discLines .probe).getD 0 #[PresetId.minimal])
  -- a skip for a theorem no discovery clause selects is an error (§14.3);
  -- the test reads the raw sets, because the selection below removes what
  -- the skip excludes
  for (thm, _) in skipList do
    unless rawChar.contains thm || rawTag.contains thm
        || rawProbe.contains thm do
      throwError "theorem_vectors: `skip {thm}` selects a theorem no \
        discovery clause selects (§14.3)"
  -- selection with §14.3's precedence: a named line wins over discovery,
  -- a skip excludes a theorem from discovery, a tagged theorem's claim
  -- outranks its characterization, and the probe takes the residual
  let keep (thm : Name) : Bool :=
    !namedSet.contains thm && !skipSet.contains thm
  let sel : Array (Name × OutcomeOrigin × Bool × Array PresetId) :=
    (rawTag.foldl (init := (#[] : Array (Name × OutcomeOrigin × Bool × Array PresetId))) fun acc thm =>
        if keep thm then acc.push (thm, .tagged, true, tagPs) else acc) ++
      (rawChar.foldl (init := (#[] : Array (Name × OutcomeOrigin × Bool × Array PresetId))) fun acc thm =>
        if keep thm && !rawTag.contains thm then
          acc.push (thm, .characterized, false, charPs)
        else acc) ++
      (rawProbe.foldl (init := (#[] : Array (Name × OutcomeOrigin × Bool × Array PresetId))) fun acc thm =>
        if keep thm && !rawTag.contains thm && !rawChar.contains thm then
          acc.push (thm, .probe, false, probePs)
        else acc)
      |>.qsort fun a b => a.1.toString < b.1.toString
  -- execute: named lines first, in file order; then the discovered set in
  -- name order (§14.3). A theorem whose description already ran is
  -- skipped; each run records itself at once, so a repeated pass neither
  -- repeats it nor loses it.
  let runOnce (thm : Name) (origin : OutcomeOrigin) (strict : Bool)
      (ps : Array PresetId) : CommandElabM Unit := do
    let key := execKey origin ps
    let env ← getEnv
    unless (executed.getState env).any fun (t, k) => t == thm && k == key do
      modifyEnv (executed.addEntry · (thm, key))
      runTheorem binding origin strict thm ps
  for (thm, strict, _, ps) in named do
    runOnce thm .named strict ps
  for (thm, origin, strict, ps) in sel do
    runOnce thm origin strict ps
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

@[command_elab tvProbeCmd]
def elabTvProbe : CommandElab := elabTvDiscovery .probe

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

/-- The named-line elaborator shared by the plain and `!` forms. The two
rules' leading tokens differ (`theorem_vectors` against the single token
`theorem_vectors!`), so the children sit at the same indices. -/
private def elabNamedLine (strict : Bool) : CommandElab := fun stx => do
  let env ← getEnv
  let some _ := forkHeader.getState env
    | throwError "theorem_vectors: no `theorem_vectors_fork` header precedes \
        this line; the header must come first in the file"
  -- resolve through the binding for the proof-namespace fallback
  let some bindingName := forkHeader.getState env
    | unreachable!
  let binding ← evalForkBinding bindingName
  let thm ← resolveThmName binding stx[1]
  let seeds := parseSeeds stx[2]
  let ps ← parsePresets stx[3]
  modifyEnv (generatorLines.addEntry ·
    { kind := .named thm strict seeds, presetIds := ps })
  runPass

@[command_elab tvNamedStrictCmd]
def elabTvNamedStrict : CommandElab := elabNamedLine true

@[command_elab tvNamedCmd]
def elabTvNamed : CommandElab := elabNamedLine false

end EthCLLib.TheoremVectors
