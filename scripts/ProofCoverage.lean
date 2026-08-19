import Lean
import EthCLLib.Internal.Capture
import EthCLLib.Internal.ProofLedger

/-!
# `scripts/ProofCoverage.lean`: the proof-coverage report

One number that says how much of the executable spec is formally verified, and a
ratchet that keeps the number from drifting down unnoticed. Run it from the repo
root, after `lake build`:

```
lake env lean --run scripts/ProofCoverage.lean            # the report
lake env lean --run scripts/ProofCoverage.lean -- --check  # the ratchet, for CI
lake env lean --run scripts/ProofCoverage.lean -- --update  # rewrite the baseline
```

The script imports the built environment and reads it. Nothing here scrapes
source text for declaration names: `captureExt` already records every `forkdef`
into the `.olean`, and `characterizesExt` records every `@[characterizes]` tag,
so the names are exact and a rename can never rot them. The one filesystem read
is module *discovery* under `packages/SizzLean/SizzLean/Proofs/`, so a new proof
module joins the report without an edit here.

## The three tiers

A **spec function** is a constant a `forkdef` produced. Each one sits in a tier:

* **Tier 0, executable.** It compiles and the pyspec vectors exercise it. Every
  spec function is here by construction, so tier 0 is the denominator and never
  a claim.
* **Tier 1, touched.** Some theorem *statement* under `EthCLSpecs.Proofs`
  mentions the constant. Statements only, never proof terms, so a proof that
  merely unfolds through a function claims nothing about it.
* **Tier 2, characterized.** A theorem carries
  `@[characterizes <function>]`, a person's claim that the theorem states the
  function's main contract. `EthCLLib/Internal/ProofLedger.lean` validates the
  tag where the proof is written.

The headline is the tier 2 count; tier 1 stands beside it. A report of "has some
theorem" alone would score one offset bound the same as a full
characterization.

## The denominator, per fork

A fork's denominator is its **effective surface**: the spec functions its own
source declares plus every ancestor `forkdef` it re-elaborated through
`inherit`. Both groups are constants in the fork's own namespace, both run under
that fork's conformance vectors, and a proof about `EthCLSpecs.Gloas.getPtc`
says nothing about the separately elaborated `EthCLSpecs.Heze.getPtc`. So the
surface is what the fork must answer for. The fork's **authored diff**, what its
own source declares, prints beside the surface for scale; it is not the
denominator.

## What the report does not count

Containers, abbrevs, instances, tier declarations, and plain `def`s written
inside a fork body stay out of the denominator, because `forkdef` is the form
that declares a spec function. SSZ properties over containers are a separate
metric with its own home in `SizzLean`, and the `SizzLean` section below reports
it as a matrix rather than a ratio.

## Lean idioms annotated on first appearance

* `importModules (loadExts := true)`: builds an `Environment` from compiled
  `.olean`s. `loadExts` is what replays the environment extensions, so
  `captureExt` and `characterizesExt` arrive populated. The script's own
  `import` list stays free of `EthCLSpecs`, because the interpreter would then
  have to resolve the FFI hasher's native symbols at load time.
* `Lean.CollectAxioms.collect`: the core axiom walk behind `#print axioms`,
  run directly as `ReaderT Environment (StateM …)` so the script needs no
  `CoreM`.
* `privateToUserName?` / `Name.isInternal` / `isReservedName`: the three tests
  that separate the theorems a person wrote from the declarations the
  elaborator generated beside them (`_simp_1_1` lemmas, `.eq_1` equation
  lemmas, structure congruence lemmas). Counting the generated ones would
  inflate every tier.
-/

set_option autoImplicit false

open Lean EthCLLib.Internal

namespace ProofCoverage

/-! ## Paths and pinned names

Every path is relative to the repo root, which is where the `just` recipes run
the script from. -/

/-- The committed baseline the ratchet compares against. -/
def baselinePath : System.FilePath := "packages/EthCLSpecs/docs/proof-coverage.baseline"

/-- The human-maintained ledger of proposed and finished proofs. The report
cross-checks it loosely, and `CONSENSUS_PROOF_CANDIDATES.md` is the file that
already holds those rows, so the ledger needs no second home. -/
def ledgerPath : System.FilePath :=
  "packages/EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md"

/-- The README whose verification-status block the report regenerates. -/
def readmePath : System.FilePath := "packages/EthCLSpecs/README.md"

/-- The `SizzLean` package directory, the root a module path is relative to. -/
def sizzleanPackageDir : System.FilePath := "packages/SizzLean"

/-- The directory the `SizzLean` proof modules live in. -/
def sizzleanProofsDir : System.FilePath := sizzleanPackageDir / "SizzLean" / "Proofs"

/-- The module prefix that makes a theorem part of the fork-body proof set. -/
def forkProofsRoot : Name := `EthCLSpecs.Proofs

/-- The module prefix that makes a theorem part of the SSZ proof set. -/
def sszProofsRoot : Name := `SizzLean.Proofs

/-- The `SSZType` universe. A gating predicate is an inductive over it. -/
def sszTypeName : Name := `SizzLean.Spec.SSZType

/-- The namespace every fork body sits under. The ledger cross-check reads only
the rows below it, so another package's ledger table passes by untouched. -/
def specsRoot : Name := `EthCLSpecs

/-- Markers around the generated block in the README. -/
def readmeBeginMarker : String := "<!-- proof-coverage:begin -->"

/-- The closing marker; see `readmeBeginMarker`. -/
def readmeEndMarker : String := "<!-- proof-coverage:end -->"

/-! ## Small shared helpers -/

/-- Sort names the way the baseline file wants them, by their printed form, so a
diff of the baseline reads alphabetically. -/
def sortNames (ns : Array Name) : Array Name :=
  ns.qsort fun a b => toString a < toString b

/-- The printed form of a name, in backticks, for the markdown tables. -/
def code (n : Name) : String := s!"`{n}`"

/-- ASCII whitespace off both ends. `String.trim` is deprecated in favour of
`String.trimAscii`, which answers with a `String.Slice`. -/
def trim (s : String) : String := s.trimAscii.toString

/-! ## Loading the environment

The report needs the fork bodies, their proofs, and the `SizzLean` proofs. The
`SizzLean` proof modules have no aggregator module, so the script discovers them
from the directory and imports each one. -/

/-- Every module under `packages/SizzLean/SizzLean/Proofs/`, as module names.

The walk is recursive, so a proof module in a new subdirectory is picked up. -/
def sizzleanProofModules : IO (Array Name) := do
  unless ← sizzleanProofsDir.pathExists do
    throw <| IO.userError
      s!"{sizzleanProofsDir} not found: run the script from the repo root."
  let files ← sizzleanProofsDir.walkDir
  let mut modules : Array Name := #[]
  for file in files do
    if file.extension == some "lean" then
      -- `packages/SizzLean/SizzLean/Proofs/Sub/Foo.lean` ⇒ `SizzLean.Proofs.Sub.Foo`:
      -- the module path is what is left once the package directory is dropped.
      let parts := file.withExtension "" |>.components.drop
        sizzleanPackageDir.components.length
      modules := modules.push (parts.foldl (fun n p => n ++ p.toName) Name.anonymous)
  return sortNames modules

/-- The compiled environment the whole report reads. -/
def loadEnvironment : IO Environment := do
  initSearchPath (← findSysroot)
  let sizzlean ← sizzleanProofModules
  let modules := #[`EthCLSpecs, `EthCLSpecs.Proofs] ++ sizzlean
  importModules (loadExts := true) (modules.map fun m => { module := m }) {}

/-! ## The theorems a person wrote

The elaborator adds declarations beside the ones in the source: equation lemmas,
`simp` variants, congruence lemmas, and the auxiliary `_proof_` terms a tactic
emits. They are theorems in the environment and they live in the same module, so
every tier and every axiom listing has to filter them out. -/

/-- One theorem the report grades. -/
structure Thm where
  /-- The declaration's name, private prefix and all. -/
  name : Name
  /-- The module it was declared in. -/
  module : Name
  /-- Its statement. Tiers read this, never the proof term. -/
  type : Expr

/-- Did a person write `name`, or did the elaborator generate it?

Three tests, and each one earns its place. `privateToUserName?` unwraps
`_private.Module.0.Ns.foo` so a `private theorem` still counts as written.
`Name.isInternal` then rejects any component starting with `_`, which covers the
`_simp_1_1` and `_proof_1` families. `isReservedName` rejects the names the
elaborator reserves for a declaration it derives from another, `.eq_1` and
friends. The declaration range is the last word: a generated declaration
inherits no source span, and a written one always has one. -/
def isWritten (env : Environment) (name : Name) : Bool :=
  let user := (privateToUserName? name).getD name
  !user.isInternal && !isReservedName env name
    && (declRangeExt.find? env name).isSome

/-- Every written theorem whose module sits under one of `roots`, in one pass
over the environment. The pass is the expensive part of the report, so both the
fork-body tiers and the `SizzLean` matrix share it. -/
def writtenTheorems (env : Environment) (roots : Array Name) : Array Thm := Id.run do
  let mut thms : Array Thm := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo t := info then
      if let some idx := env.getModuleIdxFor? name then
        let module := env.header.moduleNames[idx.toNat]!
        if roots.any (·.isPrefixOf module) && isWritten env name then
          thms := thms.push { name, module, type := t.type }
  return thms

/-- The theorems whose module sits under `root`. -/
def under (thms : Array Thm) (root : Name) : Array Thm :=
  thms.filter fun t => root.isPrefixOf t.module

/-! ## Tier 1 and tier 2 -/

/-- The spec functions a theorem's statement mentions. -/
def mentions (surface : NameSet) (t : Thm) : Array Name :=
  t.type.getUsedConstants.filter surface.contains

/-- One fork's row in the report. -/
structure ForkRow where
  /-- The fork's namespace. -/
  fork : Name
  /-- Its effective surface, the denominator. -/
  surface : Array Name
  /-- How many of those its own source declares. -/
  authored : Nat
  /-- Tier 1: surface functions some statement mentions. -/
  touched : Array Name
  /-- Tier 2: surface functions a `characterizes` tag names. A subset of
  `touched`, because the attribute rejects a tag the statement does not
  mention. -/
  characterized : Array Name

/-- The characterizing theorems per spec function, tags grouped by target. -/
def characterizedBy (env : Environment) : Std.HashMap Name (Array Name) :=
  (characterizations env).foldl (init := {}) fun acc (thm, target) =>
    acc.insert target ((acc.getD target #[]).push thm)

/-- Grade every registered fork. -/
def gradeForks (env : Environment) (thms : Array Thm) : Array ForkRow :=
  let tags := characterizedBy env
  (registeredForks env).map fun fork =>
    let surface := specFunctions env fork
    let touched := thms.foldl (init := ({} : NameSet)) fun acc t =>
      (mentions surface t).foldl (·.insert ·) acc
    { fork
      surface       := sortNames surface.toArray
      authored      := (authoredSpecFunctions env fork).size
      touched       := sortNames touched.toArray
      characterized := sortNames (surface.toArray.filter tags.contains) }

/-! ## The axiom audit

Every written theorem in both proof sets, the fork bodies and the SSZ library,
must rest on the classes below and nothing else. `sorryAx` is what this catches
above all, and the same walk feeds the trust-base listing in the report. -/

/-- The axioms a proof in this repo may rest on.

`propext`, `Classical.choice`, and `Quot.sound` are Lean's own three.
`Lean.ofReduceBool` and `Lean.trustCompiler` are what `native_decide` and
`bv_decide` add, per the tactics policy in CLAUDE.md. The two `SizzLean` entries
are the named FFI ≡ pure-Lean SHA-256 equivalences; a theorem that uses them
says so in its docstring. -/
def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound,
    `Lean.ofReduceBool, `Lean.trustCompiler,
    `SizzLean.sha256Hash_eq_spec, `SizzLean.sha256Combine_eq_spec]

/-- The axioms `n`'s proof rests on, transitively. -/
def axiomsOf (env : Environment) (n : Name) : Array Name :=
  (((CollectAxioms.collect n).run env).run {}).2.axioms

/-- Peel the components after a `bv_decide` marker: `foo._native.bv_decide.ax_1_6`
yields `foo._native`. A name with no such marker yields `none`.

Structural recursion down the `Name` spine, so no `partial def` is needed. -/
def dropAfterBvDecide : Name → Option Name
  | .anonymous  => none
  | .str p s    => if s == "bv_decide" then some p else dropAfterBvDecide p
  | .num p _    => dropAfterBvDecide p

/-- The theorem a `bv_decide` certificate axiom was emitted for.

`bv_decide` closes a goal by checking a SAT certificate with compiled code, and
names the resulting axiom under the declaration it closed
(`foo._native.bv_decide.ax_1_6`). So the family cannot be a fixed list; the
audit recognises a member by its shape and confirms the owner is a theorem. -/
def bvDecideOwner? (a : Name) : Option Name :=
  match dropAfterBvDecide a with
  | some (.str owner "_native") => some owner
  | _                          => none

/-- The trust class `a` belongs to, or `none` when `a` is not allowed at all.

The class, never the axiom name, is what the report prints and what the baseline
would record: one certificate axiom per `bv_decide` call would otherwise make
the trust base grow a row per proof. -/
def axiomClass (env : Environment) (a : Name) : Option String :=
  if allowedAxioms.contains a then
    some (toString a)
  else
    match bvDecideOwner? a with
    | some owner =>
      match env.find? owner with
      | some (.thmInfo _) => some "<theorem>._native.bv_decide.ax_* (bv_decide certificate)"
      | _                 => none
    | none => none

/-- Each theorem paired with the axioms it rests on.

The walk is the expensive half of the report, so it runs once per theorem and both
the audit and the trust base read the result. -/
def auditAxioms (env : Environment) (thms : Array Thm) : Array (Thm × Array Name) :=
  thms.map fun t => (t, axiomsOf env t.name)

/-- Every theorem resting on an axiom outside every trust class, with the
offending axioms. `sorryAx` is what this catches above all. -/
def axiomViolations (env : Environment) (audited : Array (Thm × Array Name)) :
    Array (Name × Array Name) :=
  audited.filterMap fun (t, axioms) =>
    let bad := axioms.filter fun a => (axiomClass env a).isNone
    if bad.isEmpty then none else some (t.name, bad)

/-- The trust base: how many theorems rest on each class, the allowed axioms first
in their declared order, then the `bv_decide` certificate family. Rows with a zero
count stay in, so the listing shows the whole allowance and not only what today's
proofs happen to use. -/
def trustBase (env : Environment) (audited : Array (Thm × Array Name)) :
    Array (String × Nat) :=
  let classes := allowedAxioms.map toString
    |>.push "<theorem>._native.bv_decide.ax_* (bv_decide certificate)"
  classes.map fun cls =>
    (cls, audited.countP fun (_, axioms) =>
      axioms.any fun a => axiomClass env a == some cls)

/-! ## The `SizzLean` matrix

The SSZ proofs are stated once over the whole `SSZType` universe, gated by an
inductive predicate. Three theorems already cover an infinite family of types, so
counting theorems here would mislead; the frontier is the predicate. The metric
is a matrix instead: one row per property, one column per fragment of the
universe, and every cell computed from the gating predicate's constructors. -/

/-- One column: a fragment of the `SSZType` universe.

`admits` classifies a predicate constructor by its last component, which is how a
new constructor turns cells green with no edit to the report. An unclassified
constructor fails the run instead of landing in no column silently. -/
structure Fragment where
  /-- The slug the baseline records. -/
  key : String
  /-- The column header. -/
  label : String
  /-- Does a constructor with this last component belong to the fragment? -/
  admits : String → Bool

/-- The four fragments, in table order. -/
def fragments : Array Fragment := #[
  { key := "basic-arms", label := "Basic arms",
    admits := fun c => c == "bool" || c.startsWith "uintN" },
  { key := "bit-shapes", label := "Bit shapes",
    admits := fun c => c.startsWith "bit" },
  { key := "fixed-composites", label := "Fixed-elem composites",
    admits := fun c => c.endsWith "Fixed" },
  { key := "variable-composites", label := "Variable-size composites",
    admits := fun c => c.endsWith "Var" }]

/-- One row: a property, and the theorems that state it. -/
structure Property where
  /-- The slug the baseline records. -/
  key : String
  /-- The row label, as markdown. -/
  label : String
  /-- The theorems in the SSZ proof set that state this property. -/
  select : Array Thm → Array Thm

/-- Does `t`'s statement mention a constant named `hashTreeRoot`, under `ns`?

The two merkleization rows have no theorem to name yet, so they are selected by
what a statement talks about rather than by a theorem name. -/
def mentionsHashTreeRoot (ns : Name) (t : Thm) : Bool :=
  t.type.getUsedConstants.any fun c =>
    c.getString! == "hashTreeRoot" && ns.isPrefixOf c

/-- The five property rows, in table order.

The first three name their theorem, so a rename shows up as a red `--check`
rather than a quietly emptied row. The last two are the proposed work, and both
are selected by statement, since neither theorem exists to be named. -/
def properties : Array Property := #[
  { key := "decode_encode", label := "`decode_encode`",
    select := fun thms => thms.filter (·.name == `SizzLean.Proofs.decode_encode) },
  { key := "serialize_injective", label := "`serialize_injective`",
    select := fun thms => thms.filter (·.name == `SizzLean.Proofs.serialize_injective) },
  { key := "encode_size_le_max", label := "`encode_size_le_max`",
    select := fun thms => thms.filter (·.name == `SizzLean.Proofs.encode_size_le_max) },
  { key := "hash-tree-root", label := "any `hashTreeRoot` property",
    select := fun thms => thms.filter (mentionsHashTreeRoot `SizzLean.Spec) },
  { key := "cached-tree", label := "cached tree ≡ uncached `hashTreeRoot`",
    select := fun thms => thms.filter fun t =>
      mentionsHashTreeRoot `SizzLean.Spec t && mentionsHashTreeRoot `SizzLean.Cache t }]

/-- Is `p` an inductive predicate over the `SSZType` universe, `SSZType → Prop`?

The domain must be the `SSZType` constant itself, which is what keeps the mutual
field-list companion (`… : List SSZType → Prop`) out: its domain is an
application, not a constant. -/
def isGatingPredicate (env : Environment) (p : Name) : Bool :=
  match env.find? p with
  | some (.inductInfo info) =>
    match info.type with
    | .forallE _ domain body _ => domain.isConstOf sszTypeName && body.isProp
    | _ => false
  | _ => false

/-- The gating predicates a theorem's statement carries. -/
def gatingPredicates (env : Environment) (t : Thm) : Array Name :=
  t.type.getUsedConstants.filter (isGatingPredicate env)

/-- The arms a set of gating predicates admits, as constructor last components. -/
def admittedArms (env : Environment) (predicates : Array Name) : Array String :=
  predicates.foldl (init := #[]) fun acc p =>
    match env.find? p with
    | some (.inductInfo info) =>
      info.ctors.foldl (init := acc) fun acc c =>
        let arm := c.getString!
        if acc.contains arm then acc else acc.push arm
    | _ => acc

/-- One computed row of the matrix. -/
structure MatrixRow where
  /-- The property the row grades. -/
  property : Property
  /-- The gating predicates its theorems carry. -/
  gates : Array Name
  /-- How many arms each fragment admits, parallel to `fragments`. -/
  cells : Array Nat
  /-- Admitted arms no fragment claims. A non-empty list fails the run. -/
  unclassified : Array String

/-- Grade every property row against the SSZ proof set. -/
def gradeSsz (env : Environment) (thms : Array Thm) : Array MatrixRow :=
  properties.map fun property =>
    let selected := property.select thms
    let gates := selected.foldl (init := #[]) fun acc t =>
      (gatingPredicates env t).foldl (fun acc p => if acc.contains p then acc else acc.push p) acc
    let arms := admittedArms env gates
    { property
      gates
      cells        := fragments.map fun f => (arms.filter f.admits).size
      unclassified := arms.filter fun arm => !fragments.any (·.admits arm) }

/-! ## Rendering

The report, the README block, and the baseline all read from the same computed
values, so no two of them can disagree. The tables are markdown in every mode:
the terminal reads them fine, and the README needs them that way. -/

/-- A markdown table from a header row and body rows. -/
def table (header : Array String) (rows : Array (Array String)) : String :=
  let line := fun (cells : Array String) => "| " ++ String.intercalate " | " cells.toList ++ " |"
  String.intercalate "\n"
    (line header :: line (header.map fun _ => "---") :: (rows.map line).toList)

/-- The per-fork coverage table. -/
def renderForkTable (rows : Array ForkRow) : String :=
  let body := rows.map fun r =>
    #[code r.fork, toString r.characterized.size, toString r.touched.size,
      toString r.surface.size, toString r.authored]
  let total := #["**Total**",
    toString (rows.foldl (· + ·.characterized.size) 0),
    toString (rows.foldl (· + ·.touched.size) 0),
    toString (rows.foldl (· + ·.surface.size) 0),
    toString (rows.foldl (· + ·.authored) 0)]
  table #["Fork", "Characterized", "Touched", "Spec functions", "Authored"] (body.push total)

/-- The `SizzLean` property-by-fragment matrix. -/
def renderMatrix (rows : Array MatrixRow) : String :=
  let body := rows.map fun r =>
    #[r.property.label] ++ r.cells.map fun n => if n == 0 then "❌" else s!"✅ {n}"
  table (#["Property"] ++ fragments.map (·.label)) body

/-- The trust-base table. -/
def renderTrustBase (rows : Array (String × Nat)) : String :=
  table #["Axiom", "Theorems resting on it"]
    (rows.map fun (cls, n) => #[s!"`{cls}`", toString n])

/-! ## The computed report

One structure holds everything the three modes read, so the report, the README
block, and the baseline cannot disagree about the same fact. -/

/-- Everything the report computed, plus the problems that fail the run. -/
structure Report where
  /-- Per-fork coverage. -/
  forks : Array ForkRow
  /-- The `SizzLean` property matrix. -/
  matrix : Array MatrixRow
  /-- The trust base of the fork-body proof set. -/
  forkTrust : Array (String × Nat)
  /-- The trust base of the SSZ proof set. -/
  sszTrust : Array (String × Nat)
  /-- How many written theorems the fork-body proof set holds. -/
  forkTheorems : Nat
  /-- How many written theorems the SSZ proof set holds. -/
  sszTheorems : Nat
  /-- Every `characterizes` tag, as `(theorem, function)`. -/
  tags : Array (Name × Name)
  /-- Why the run must fail. Empty on a healthy repo. -/
  problems : Array String

/-- Compute the whole report from a loaded environment. -/
def buildReport (env : Environment) : Report :=
  let thms := writtenTheorems env #[forkProofsRoot, sszProofsRoot]
  let forkThms := under thms forkProofsRoot
  let sszThms := under thms sszProofsRoot
  let forkAudit := auditAxioms env forkThms
  let sszAudit := auditAxioms env sszThms
  let forks := gradeForks env forkThms
  let matrix := gradeSsz env sszThms
  let tags := characterizations env
  let surfaced := forks.foldl (init := #[]) fun acc r => acc ++ r.surface
  let problems :=
    (axiomViolations env (forkAudit ++ sszAudit)).map (fun (thm, bad) =>
        s!"{thm} rests on an axiom outside the allowed classes: {bad.toList}")
    ++ matrix.filterMap (fun r =>
        if r.unclassified.isEmpty then none
        else some s!"property `{r.property.key}` admits arms no fragment claims: \
          {r.unclassified.toList}. Extend `fragments` with the new column.")
    ++ tags.filterMap (fun (thm, target) =>
        if surfaced.contains target then none
        else some s!"`characterizes` tag on {thm} names {target}, which no fork's \
          surface holds. Did the function move fork?")
    ++ tags.filterMap (fun (thm, _) =>
        if forkThms.any (·.name == thm) then none
        else some s!"`characterizes` tag on {thm} sits outside {forkProofsRoot}, so \
          the report would count a claim it cannot grade.")
  { forks, matrix
    forkTrust    := trustBase env forkAudit
    sszTrust     := trustBase env sszAudit
    forkTheorems := forkThms.size
    sszTheorems  := sszThms.size
    tags, problems }

/-- The block the `EthCLSpecs` README carries between its markers: the fork
table and the fork-body trust base.

The `SizzLean` matrix stays out of it. `packages/SizzLean/README.md` already
carries a finer per-constructor table of the same three properties, and one fact
gets one home; the matrix's mechanical half is the baseline, which fails the
build when an admitted arm disappears. -/
def renderReadmeBlock (report : Report) : String :=
  String.intercalate "\n\n"
    [renderForkTable report.forks, renderTrustBase report.forkTrust]

/-- The full report, for a person reading a terminal. -/
def renderReport (report : Report) : String :=
  let tierLists := report.forks.foldl (init := "") fun acc r =>
    if r.touched.isEmpty then acc else
      let line := fun (fn : Name) =>
        let tier := if r.characterized.contains fn then "tier 2" else "tier 1"
        let by_ := (report.tags.filterMap fun (thm, target) =>
          if target == fn then some (code thm) else none)
        if by_.isEmpty then s!"* {tier}  {code fn}"
        else s!"* {tier}  {code fn}, from {String.intercalate ", " by_.toList}"
      acc ++ s!"\n### {r.fork}\n\n"
        ++ String.intercalate "\n" (r.touched.map line).toList ++ "\n"
  s!"# Proof coverage

Tier 1 is *touched*: a theorem statement mentions the spec function. Tier 2 is
*characterized*: a `characterizes` tag claims the theorem states the function's
main contract. Tier 0 is every spec function, the denominator.

## The fork bodies

{renderForkTable report.forks}

{report.forkTheorems} written theorems under {forkProofsRoot}.
{tierLists}
## SSZ properties (SizzLean)

{renderMatrix report.matrix}

{report.sszTheorems} written theorems under {sszProofsRoot}. A cell counts the
arms of the `SSZType` universe the property's gating predicate admits.

## Trust base

The fork-body proof set:

{renderTrustBase report.forkTrust}

The SSZ proof set:

{renderTrustBase report.sszTrust}

`LeanSha256` and the `LeanHazmat` families carry no coverage ratio by design.
The hazmat packages are `@[extern] opaque` bindings, so there is no Lean body to
prove anything about, and `LeanSha256`'s own claim is empirical (the NIST CAVP
vectors). What they contribute is the two named equivalence axioms above.
`EthCLLib` is out of scope: its correctness claim is that the replayed forks
build and pass conformance, which the replay tests and the pyspec vectors
enforce. `LeanPoseidon` proves `permute_eq_permuteRef` in the standalone
`LeanPoseidonProofs` package, which pins mathlib outside the umbrella and so
outside this run; `packages/LeanPoseidon/docs/PLAN.md` Phase 3 tracks it.
"

/-! ## The baseline

One line per covered spec function, one per green matrix cell. Functions, never
theorem names, so splitting or renaming a theorem does not churn the file while
coverage holds. -/

/-- The two comment lines at the head of the baseline file. -/
def baselineHeader : Array String :=
  #["# Proof-coverage baseline. Rewrite with `just proof-coverage-update`.",
    "# Every line is a claim `just proof-coverage-check` enforces exactly."]

/-- The baseline's data lines, sorted. -/
def baselineLines (report : Report) : Array String :=
  let forkLines := report.forks.flatMap fun r =>
    r.touched.map fun fn =>
      let tier := if r.characterized.contains fn then "tier2" else "tier1"
      s!"{tier} {fn}"
  let sszLines := report.matrix.flatMap fun r =>
    (fragments.zip r.cells).filterMap fun (f, arms) =>
      if arms == 0 then none else some s!"sizzlean {r.property.key} {f.key} {arms}"
  (forkLines ++ sszLines).qsort (· < ·)

/-- The baseline file's whole text. -/
def renderBaseline (report : Report) : String :=
  String.intercalate "\n" (baselineHeader ++ baselineLines report).toList ++ "\n"

/-- The lines of a baseline file, comments and blanks dropped. -/
def parseBaseline (text : String) : Array String :=
  (text.splitOn "\n").toArray.filterMap fun line =>
    let line := trim line
    if line.isEmpty || line.startsWith "#" then none else some line

/-! ## The ledger cross-check

`docs/CONSENSUS_PROOF_CANDIDATES.md` is the ledger: one row per candidate spec
function, its rationale, and the words `**Proved**` once a theorem discharges it.
The cross-check reads those rows and warns where they and the `characterizes`
tags disagree. It only ever warns: the ledger is prose, and a table this script
cannot parse is still a table a person can read.
-/

/-- One parsed ledger row. -/
structure LedgerRow where
  /-- The spec function the row is about, resolved to a full constant. -/
  function : Name
  /-- Does the row claim the property is proved? -/
  proved : Bool

/-- Strip backticks and surrounding space from a table cell. -/
def plainCell (cell : String) : String := trim (cell.replace "`" "")

/-- Does `haystack` hold `needle`? -/
def holds (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

/-- Every ledger row, resolved against the fork it cites.

A row's second cell cites the spec body it lives in
(`` `Gloas/Operations.lean:456` ``), and the leading path component is the fork,
so `` `getPtc` `` in that row resolves to `EthCLSpecs.Gloas.getPtc`. Header rows,
separator rows, and prose all fail one of the shape tests, so none of them needs
a special case. -/
def parseLedger (text : String) : Array LedgerRow :=
  (text.splitOn "\n").toArray.filterMap fun line =>
    let line := trim line
    if !line.startsWith "|" then none else
      let cells := (line.splitOn "|").toArray
      if cells.size < 5 then none else
        let name := trim cells[1]!
        let location := plainCell cells[2]!
        if !name.startsWith "`" then none else
          match location.splitOn "/" with
          | fork :: _ :: _ =>
            some { function := specsRoot ++ fork.toName ++ (plainCell name).toName
                   proved   := holds cells[3]! "**Proved**" }
          | _ => none

/-- What the ledger and the computed coverage disagree about.

A row about something no `forkdef` declared passes by in silence: the ledger
lists candidates the coverage metric does not measure, plain `def`s inside a fork
body among them. -/
def ledgerWarnings (env : Environment) (report : Report) (rows : Array LedgerRow) :
    Array String :=
  let characterized := report.forks.foldl (init := #[]) fun acc r => acc ++ r.characterized
  rows.filterMap (fun row =>
      if !row.proved || !isSpecFunction env row.function then none
      else if characterized.contains row.function then none
      else some s!"the ledger marks `{row.function}` proved, and no `characterizes` \
        tag claims it. Either the theorem states something narrower than the \
        function's contract, or the tag is missing.")
    ++ characterized.filterMap fun fn =>
        if rows.any fun row => row.function == fn && row.proved then none
        else some s!"`{fn}` carries a `characterizes` tag, and the ledger has no \
          proved row for it. Add the row so the ledger stays the forward half."

/-! ## The README block -/

/-- Replace the README's generated block, or report why it cannot be found. -/
def spliceReadme (text : String) (block : String) : Except String String :=
  match text.splitOn readmeBeginMarker with
  | [before, rest] =>
    match rest.splitOn readmeEndMarker with
    | [_, after] =>
      .ok (before ++ readmeBeginMarker ++ "\n" ++ block ++ "\n" ++ readmeEndMarker ++ after)
    | _ => .error s!"{readmePath} needs exactly one {readmeEndMarker}."
  | _ => .error s!"{readmePath} needs exactly one {readmeBeginMarker}."

/-- The block the README carries today. -/
def readmeBlock (text : String) : Except String String :=
  match text.splitOn readmeBeginMarker with
  | [_, rest] =>
    match rest.splitOn readmeEndMarker with
    | [block, _] => .ok (trim block)
    | _ => .error s!"{readmePath} needs exactly one {readmeEndMarker}."
  | _ => .error s!"{readmePath} needs exactly one {readmeBeginMarker}."

/-! ## The three modes -/

/-- How the script was invoked. -/
inductive Mode where
  /-- Print the report. -/
  | report
  /-- Compare against the committed baseline, the ratchet CI runs. -/
  | check
  /-- Rewrite the baseline and the README block. -/
  | update
  deriving DecidableEq

/-- Read the mode off the command line.

`lake env lean --run … -- --check` hands the bare `--` through to the script, so
the separator is dropped before the match. -/
def parseMode (args : List String) : IO Mode :=
  match args.filter (· != "--") with
  | []           => pure .report
  | ["--check"]  => pure .check
  | ["--update"] => pure .update
  | rest         => throw <| IO.userError
      s!"unexpected arguments {rest}: pass nothing, `--check`, or `--update`."

/-- Lines the baseline holds and the environment does not, and the reverse. -/
def baselineDrift (committed computed : Array String) : Array String :=
  committed.filterMap (fun line =>
      if computed.contains line then none
      else some s!"- {line}   (in the baseline, not in the build)")
    ++ computed.filterMap fun line =>
        if committed.contains line then none
        else some s!"+ {line}   (in the build, not in the baseline)"

/-- The ratchet. Exact equality both ways, so a swap of one proof for another
cannot slip through a floor-only count. -/
def runCheck (report : Report) : IO UInt32 := do
  let mut failed := false
  if ← baselinePath.pathExists then
    let drift := baselineDrift (parseBaseline (← IO.FS.readFile baselinePath))
                               (baselineLines report)
    unless drift.isEmpty do
      failed := true
      IO.eprintln s!"{baselinePath} and the build disagree:"
      for line in drift do IO.eprintln s!"  {line}"
  else
    failed := true
    IO.eprintln s!"{baselinePath} is missing. Run `just proof-coverage-update`."
  match readmeBlock (← IO.FS.readFile readmePath) with
  | .error e => failed := true; IO.eprintln e
  | .ok block =>
    unless block == trim (renderReadmeBlock report) do
      failed := true
      IO.eprintln s!"{readmePath}'s verification-status block is stale."
  if failed then
    IO.eprintln "Restore the proofs, or run `just proof-coverage-update` and commit \
      the bump under review."
    return 1
  IO.println s!"Proof coverage matches the baseline: \
    {(baselineLines report).size} claims."
  return 0

/-- Rewrite the two generated files. -/
def runUpdate (report : Report) : IO UInt32 := do
  IO.FS.writeFile baselinePath (renderBaseline report)
  IO.println s!"wrote {baselinePath}: {(baselineLines report).size} claims."
  match spliceReadme (← IO.FS.readFile readmePath) (renderReadmeBlock report) with
  | .error e => IO.eprintln e; return 1
  | .ok text =>
    IO.FS.writeFile readmePath text
    IO.println s!"wrote {readmePath}'s verification-status block."
    return 0

/-- Print the report, and the ledger's disagreements as warnings. -/
def runReport (env : Environment) (report : Report) : IO UInt32 := do
  IO.println (renderReport report)
  if ← ledgerPath.pathExists then
    let warnings := ledgerWarnings env report (parseLedger (← IO.FS.readFile ledgerPath))
    unless warnings.isEmpty do
      IO.eprintln s!"{ledgerPath} warnings (the ledger is prose; these never fail \
        the run):"
      for warning in warnings do IO.eprintln s!"  {warning}"
  return 0

end ProofCoverage

open ProofCoverage

/-- Load the environment, compute the report, and run the requested mode.

The problems `buildReport` found fail every mode, `--check` included: a
`sorryAx` dependency or a stale tag is not a difference the baseline should be
able to absorb. -/
def main (args : List String) : IO UInt32 := do
  let mode ← parseMode args
  let env ← loadEnvironment
  let report := buildReport env
  unless report.problems.isEmpty do
    IO.eprintln "proof coverage found problems:"
    for problem in report.problems do IO.eprintln s!"  {problem}"
    return 1
  match mode with
  | .report => runReport env report
  | .check  => runCheck report
  | .update => runUpdate report

