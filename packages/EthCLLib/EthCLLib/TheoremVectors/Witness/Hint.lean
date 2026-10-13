import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Source
import EthCLLib.TheoremVectors.Witness.Built

/-!
# `EthCLLib.TheoremVectors.Witness.Hint`: the hint source

A hint records how a witness was found, with enough data to rebuild the
candidate without searching (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8). It is a hint and
nothing more: the probe's `check` still decides, and a hint the check
rejects sends the case through the full search.

The file is one JSON document per theorem and fork:

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "fingerprint": "0x…",
  "entries": [
    { "preset": "minimal", "case": 0, "side": true,
      "source": "random", "seed": 7, "size": 8, "draw": 3,
      "scalars": { "builderIndex": "3", "bidAmount": "32000000000" } } ] }
```

Only what the search decided goes in, never the witness bytes. The
base and seed sources need nothing beyond their tag. The bit-vector
source needs the scalar literals. The random source needs the generator
seed, the size, and the draw index, because a draw is a pure function
of those three and `Gen` replays it. The built source needs the builder
name and the knobs, because the cached bytes rebuild from them (§9.9);
when a statement holds containers beside its state, its built entry
carries the drawn containers' key as a random entry does. A random
entry also carries the shrink path the walk accepted (§9.6), whose
replay walks the recorded candidates alone. The full loop runs for a
traceless entry, and for a recorded path that no longer replays.

The source runs first on every list (§9.2). The command loads the
committed file, computes the fingerprint, and hands both to `source`
together with a log ref; after the case loop it folds the log into the
outcome line's `hint` field (§16.1) and merges the run's entries into
`<outDir>/hints/<fork>/<thm>.json`, which the update recipe copies over
the committed files.

## Lean idioms annotated

- `«case»` carries French quotes because `case` is a keyword, the same
  way `«theorem»` does in the record and outcome structures; the derived
  JSON writes the wire spelling the §9.8 example fixes.
- The scalars map stores decimal *strings*, because a `UInt64` can exceed
  the integer range a JSON reader is sure to keep (§9.8); a small wrapper
  structure carries the map so the derived instances keep the object
  spelling.
- `Json.getObj?` answers a `Std.TreeMap.Raw`, so the scalars reader walks
  `toList` and takes the map's own order; a map has no reader-visible
  order commitment.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-! ## The mode -/

/-- What the hint source does about a missing or failing hint (§9.8). -/
inductive HintMode where
  /-- Read hints; search when one is missing or fails; write new hints. -/
  | use
  /-- Search everything; write new hints. -/
  | ignore
  /-- A hint that is missing or fails is a build error. -/
  | require
  deriving DecidableEq, Repr, Inhabited

/-- The wire tag of a mode, as the option and the `THEOREM_VECTORS_HINTS`
variable spell it (§17.2). -/
def HintMode.tag : HintMode → String
  | .use     => "use"
  | .ignore  => "ignore"
  | .require => "require"

/-- Read a mode back from its tag. -/
def HintMode.ofTag? : String → Option HintMode
  | "use"     => some .use
  | "ignore"  => some .ignore
  | "require" => some .require
  | _         => none

/-! ## The schema -/

/-- The scalars one entry fixes (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8): the input names the
theorem binds, each with the value the solver chose or the read walk
recovered from the winning assignment. -/
structure HintScalars where
  scalars : Array (String × Nat) := #[]
  deriving Inhabited, Repr, BEq

/-- The scalars object's JSON: names to decimal strings, so a `UInt64`
never meets a JSON reader's integer range (§9.8). -/
instance : ToJson HintScalars where
  toJson s :=
    Json.mkObj (s.scalars.toList.map fun (n, v) => (n, Json.str (toString v)))

instance : FromJson HintScalars where
  fromJson? j := do
    let obj ← j.getObj?
    let mut out : Array (String × Nat) := #[]
    for (n, v) in obj.toList do
      let s ← v.getStr?
      match s.toNat? with
      | some k => out := out.push (n, k)
      | none => throw s!"hint scalar '{n}' is not a decimal string"
    return { scalars := out }

/-- What one hint entry holds (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8). The optional fields
fill for the sources that need them: the random source's `seed`, `size`,
and `draw`; the built source's `builder` and `knobs`. -/
structure HintEntry where
  /-- The preset the entry replays at. -/
  preset : PresetId
  /-- The zero-based case index. -/
  «case» : Nat
  /-- The `.iffTrue` side, when the shape is `.iffTrue`. -/
  side   : Option Bool
  /-- The source whose witness the entry rebuilds. -/
  source : WitnessSourceTag
  /-- The random draw's generator seed (§9.8). -/
  seed   : Option Nat := none
  /-- The random draw's `Gen` size parameter (§9.8). -/
  size   : Option Nat := none
  /-- The random draw's index in the redraw loop (§9.8). -/
  draw   : Option Nat := none
  /-- The built source's builder display name (§9.8, §9.9). -/
  builder : Option String := none
  /-- The built source's knobs (§9.8, §9.9). -/
  knobs  : Option Knobs := none
  /-- The scalar literals the search chose. -/
  scalars : HintScalars := {}
  /-- The random source's shrink path (§9.6, the plan's stage-6 step 8):
  one entry per accepted `probe.shrink` call, holding the indices of the
  candidates that call accepted. The replay walks these instead of the
  calls' full lists. -/
  shrink : Option (Array (Array Nat)) := none
  /-- The sources the search tried on a case none of them satisfied
  (the plan's stage-6 step 9). An entry this field holds records the
  case's empty answer: `use` and `require` modes skip the search for it
  while it is not stale, and the search runs when it is. Its `source`
  field is the placeholder `.base`, because no witness exists for the
  entry to name; the `notFound` list is the entry's content, and
  `notFoundReason` carries the failure text the fresh run reported, so
  a replayed outcome reads like the searched one. -/
  notFound : Option (Array String) := none
  /-- The failure text the fresh run reported, for the replayed
  outcome's reason. -/
  notFoundReason : Option String := none
  /-- The preset's fingerprint when the entry was written (§9.8). The
  shape hashes in a fingerprint move with the preset, because a derived
  container's caps are the preset's, and the file carries one
  fingerprint field, so the operative staleness comparison is the
  entry's own. -/
  fingerprint : Option String := none
  deriving FromJson, Repr, BEq, Inhabited

/-- The entry's JSON. The absent optional fields write no key at all,
which keeps the committed files close to §9.8's example and their review
diffs to the fields that changed; a missing key reads back as `null`
through the derived parser, so the reader stays derived. -/
instance : ToJson HintEntry where
  toJson e :=
    Json.mkObj (Json.opt "preset" (some e.preset) ++ Json.opt "case" (some e.«case») ++
      Json.opt "side" e.side ++ Json.opt "source" (some e.source) ++
      Json.opt "seed" e.seed ++ Json.opt "size" e.size ++
      Json.opt "draw" e.draw ++
      Json.opt "builder" e.builder ++ Json.opt "knobs" e.knobs ++
      Json.opt "scalars" (some e.scalars) ++
      Json.opt "shrink" e.shrink ++ Json.opt "notFound" e.notFound ++
      Json.opt "notFoundReason" e.notFoundReason ++
      Json.opt "fingerprint" e.fingerprint)

/-- One theorem's hint file (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8): the theorem's full
constant name, the fingerprint, and one entry per preset, case, and side
the search won. -/
structure HintFile where
  /-- The theorem's full constant name. `theorem` is a keyword, so the
  field carries French quotes and the derived JSON writes the wire
  spelling §9.8 fixes. -/
  «theorem»   : Name
  /-- The fingerprint of the statement and the input type names (§9.8). -/
  fingerprint : String
  /-- One entry per preset, case, and side. -/
  entries     : Array HintEntry
  deriving ToJson, FromJson, Repr, BEq

/-! ## The fingerprint -/

/-- FNV-1a over the UTF-8 bytes of `s`, rendered in the wire `0x…`
form. A plain 64-bit hash is enough: the fingerprint only flags
staleness, and the check decides either way (§9.8). -/
def fingerprintOf (s : String) : String := Id.run do
  let mut h : Nat := 0xcbf29ce484222325
  for b in s.toUTF8 do
    h := ((h ^^^ b.toNat) * 0x100000001b3) % 0x10000000000000000
  return hexOf (leBytes 8 h)

/-- The fingerprint of one statement at one preset (§9.8): the theorem's
name, the input types as the probe rendered them, the output type, the
statement's parts, and the preset's wire-description hashes. The
rendering substitutes the preset's constants, and the shape hashes are
the preset's, so the fingerprint is a per-preset value and lives on the
hint entry. A changed hypothesis or conclusion changes its own
rendering, and a new container field changes its shape hash, which is
what marks a fork's random hints stale after a spec change (§9.8). -/
def Hint.fingerprint (thm : Name) (info : ProbeInfo) : String :=
  fingerprintOf (thm.toString ++ "|" ++
    String.intercalate "|" (info.inputTypes.toList) ++ "|" ++ info.outputType ++
    "|" ++ String.intercalate "|" (info.stmtParts.toList) ++ "|" ++
    String.intercalate "|" (info.shapeParts.toList))

/-! ## The files -/

/-- The output-tree path of a fork's hints directory,
`<outDir>/hints/<fork>`. -/
def Hint.dir (outDir : System.FilePath) (forkTag : String) : System.FilePath :=
  outDir / "hints" / forkTag

/-- The path of one theorem's hint file, under the output tree and under
the committed tree alike: `<hintsRoot>/<fork>/<thm>.json`. -/
def Hint.file (hintsRoot : System.FilePath) (forkTag : String)
    (thmLocal : String) : System.FilePath :=
  hintsRoot / forkTag / (thmLocal ++ ".json")

/-- Read one hint file back, `none` when the file is missing or does not
parse. A file the generator wrote either parses or is a stale stray; a
stray is a missing hint, and the search runs (§9.8: the check decides). -/
def Hint.read? (path : System.FilePath) : IO (Option HintFile) := do
  unless ← path.pathExists do
    return none
  match Json.parse (← IO.FS.readFile path) with
  | .error _ => return none
  | .ok j =>
    match fromJson? (α := HintFile) j with
    | .ok f => return some f
    | .error _ => return none

/-- Write one hint file, creating the directory. -/
def Hint.write (path : System.FilePath) (f : HintFile) : IO Unit := do
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path ((toJson f).render.pretty (width := 100) ++ "\n")

/-- Merge one run's entries into the output tree's hint file (§9.8). The
run's entries replace the stored entries of `preset`, because the run
re-searched every case of the theorem at that preset; the other presets'
entries stay, so a second preset's run never clobbers the first's. -/
def Hint.mergeWrite (outDir : System.FilePath) (forkTag : String)
    (thmLocal : String) (preset : PresetId) (f : HintFile) : IO Unit := do
  let path := Hint.file (outDir / "hints") forkTag thmLocal
  let old? ← Hint.read? path
  let merged : HintFile :=
    match old? with
    | none => f
    | some old =>
      let kept := old.entries.filter (·.preset != preset)
      { old with fingerprint := f.fingerprint, entries := kept ++ f.entries }
  Hint.write path merged

/-! ## Rebuild: the candidate from an entry -/

/-- The source a hint entry records, with a replayed entry's own wrapper
unwrapped. `none` for a source this module cannot rebuild (the reused
source lands in stage 8); the search runs for such an entry (§9.8). -/
private def entrySource (t : WitnessSourceTag) : Option WitnessSourceTag :=
  match t with
  | .hinted o => some o
  | .reused _ => none
  | t => some t

/-- The scalar value a hint entry fixes for one input position, `0` when
the entry holds no value for it: the candidate's builder wrote the same
zero for an unsolved scalar (§9.4). -/
private def entryScalar (e : HintEntry) (stmt : Statement) (i : Nat) : Nat :=
  (e.scalars.scalars.find? fun (n, _) => n == stmt.inputs[i]!.name.toString).map
    (·.2) |>.getD 0

/-- Rebuild the candidate one hint entry recorded (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8).
The overlay follows the winning assignment's construction: the drawn
containers win over the seeds in a random replay, the seeds win at the
positions they fix in a bit-vector replay, and the hint's scalars fill
the solver's choices. `none` when the entry does not describe a candidate
this module can rebuild. -/
def Hint.rebuild (ctx : SearchCtx) (stmt : Statement) (e : HintEntry) :
    MetaM (Option Assignment) := do
  let some src := entrySource e.source | return none
  let seeded := ctx.probe.seeds.map (·.1)
  let seedBytes (i : Nat) : ByteArray :=
    (ctx.probe.seeds.find? fun (p, _) => p == i).map (·.2) |>.getD emptyBytes
  let scalarVal (i : Nat) : Nat := entryScalar e stmt i
  let scalarByte (i : Nat) : MetaM (Option ByteArray) := do
    match stmt.scalarKinds[i]? |>.join with
    | none => return none
    | some k => return some (scalarBytes k (scalarVal i))
  match src with
  | .base => pure (some ctx.probe.defaults)
  | .seed =>
    pure (some (ctx.probe.seeds.foldl (init := ctx.probe.defaults)
      fun acc p =>
        let (pos, b) := p
        acc.setIfInBounds pos b))
  | .bitVec =>
    let mut a : Array ByteArray := #[]
    for i in [0:stmt.inputs.size] do
      if seeded.contains i then
        a := a.push (seedBytes i)
      else
        match ← scalarByte i with
        | none => return none
        | some b => a := a.push b
    pure (some a)
  | .random =>
    let some seed := e.seed | return none
    let some size := e.size | return none
    let some draw := e.draw | return none
    -- the redraw loop sampled `seedOpt + draw` (§9.4), so the replay
    -- samples the same sum
    let raw := ctx.probe.sample (seed + draw) size
    let mut a : Array ByteArray := #[]
    for i in [0:stmt.inputs.size] do
      if stmt.scalarKinds[i]?.join.isNone then
        -- the drawn containers win over the seeds (§9.4's overlay)
        a := a.push (raw.getD i emptyBytes)
      else if seeded.contains i then
        a := a.push (seedBytes i)
      else
        match ← scalarByte i with
        | none => return none
        | some b => a := a.push b
    -- the pre-shrink candidate: the recorded shrink path, when the
    -- entry carries one, walks in the command's shrink step (the plan's
    -- stage-6 step 8), the same place the original walk ran, so the
    -- path applies once and the candidate the hint source checks is the
    -- one the original search checked
    pure (some a)
  | .built =>
    -- §9.9: the built bytes at the statement's one state input, through
    -- the cache the search used, the other containers drawn from the
    -- entry's key when it carries one, the scalars from the entry
    let some name := e.builder | return none
    let some k := e.knobs | return none
    let some statePos := (Array.range stmt.inputs.size).find?
        (fun i => isStateType ctx.binding stmt.inputs[i]!.type) |
      return none
    -- the entry's key samples directly, never through the run's memo:
    -- the memo assumes the run's own seed and size, and the entry's may
    -- differ (§9.8)
    let drawn : Array (Nat × ByteArray) ← do
      match e.seed, e.size, e.draw with
      | some seed, some size, some draw =>
        let raw := ctx.probe.sample (seed + draw) size
        pure ((Array.range stmt.inputs.size).filterMap fun i =>
          if i == statePos || (stmt.scalarKinds[i]? |>.join).isSome then none
          else some (i, raw.getD i emptyBytes))
      | _, _, _ => pure #[]
    let builtBytes ← Built.cachedBytes ctx name k
    let mut a : Array ByteArray := #[]
    for i in [0:stmt.inputs.size] do
      if i == statePos then
        a := a.push builtBytes
      else match drawn.find? fun (p, _) => p == i with
        | some (_, b) => a := a.push b
        | none =>
          if seeded.contains i then
            a := a.push (seedBytes i)
          else
            match ← scalarByte i with
            | none => return none
            | some b => a := a.push b
    pure (some a)
  | _ => return none

/-! ## Build: the entry from a winning assignment -/

/-- The draw index whose raw bytes the winning assignment carries at the
container positions, found in the search's draw memo (§9.4). The memo
holds every draw of the theorem's run, and a draw is a pure function of
the seed, the size, and the index, so the index is the hint's replay
key. The caller reads the memo and runs this before the shrink, whose
candidates the memo does not hold. -/
private def findDrawIndex (slots : Array (Option (Array ByteArray)))
    (containers : Array Nat) (a : Assignment) : Option Nat :=
  slots.findIdx? fun slot? =>
    match slot? with
    | none => false
    | some raw =>
      containers.all fun i =>
        (raw.getD i emptyBytes) == (a.getD i emptyBytes)

/-- The scalar literals of a winning assignment (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8):
one entry per scalar input, read back from the candidate's wire bytes
through the kind's strict decode. `none` when a read fails, which makes
an honest no-hint instead of a hint that replays to a different
candidate. -/
private def scalarsOf (stmt : Statement) (a : Assignment) :
    MetaM (Option HintScalars) := do
  let mut out : Array (String × Nat) := #[]
  for i in [0:stmt.inputs.size] do
    let some k ← pure (stmt.scalarKinds[i]?.join)
      | continue
    let some b := a[i]? | return none
    let some v := scalarNatOf k b | return none
    out := out.push (stmt.inputs[i]!.name.toString, v)
  return some { scalars := out }

/-- The container positions of a statement: the inputs whose kind the
scalar family does not cover. -/
private def containerPositions (stmt : Statement) : Array Nat :=
  (Array.range stmt.inputs.size).filter fun i => stmt.scalarKinds[i]?.join.isNone

/-- The hint entry a winning candidate records (§9.8), unwrapping a
replayed `.hinted` tag back to the source the hint already recorded.
`none` when the source carries no rebuildable data yet or a scalar read
failed. -/
def Hint.entryOf (ctx : SearchCtx) (stmt : Statement) (c : Case)
    (a : Assignment) (won : WitnessSourceTag) (seedOpt sizeOpt : Nat)
    (fingerprint : String) : MetaM (Option HintEntry) := do
  let some src := entrySource won | return none
  let head : HintEntry :=
    { preset := ctx.preset, «case» := c.index, side := c.side, source := src,
      fingerprint := some fingerprint }
  match src with
  | .base | .seed => pure (some head)
  | .bitVec => do
    let some scalars ← scalarsOf stmt a | return none
    pure (some { head with scalars := scalars })
  | .random => do
    let containers := containerPositions stmt
    let some draw := findDrawIndex (← ctx.drawMemo.get) containers a
      | return none
    let some scalars ← scalarsOf stmt a | return none
    pure (some { head with seed := some seedOpt, size := some sizeOpt, draw := some draw, scalars := scalars })
  | .built => do
    -- §9.8, §9.9: the builder name, the knobs, the solved scalars, and
    -- the other containers' draw key when the statement has containers
    -- beside the state. The search drew them at draw 0, so the key is
    -- the run's own seed and size with draw 0.
    let some statePos := (Array.range stmt.inputs.size).find?
        (fun i => isStateType ctx.binding stmt.inputs[i]!.type) | return none
    let cap ← builtStepsOf ctx.preset
    let some (name, k) ← Built.findStep ctx cap a statePos | return none
    let some scalars ← scalarsOf stmt a | return none
    let hasOthers := (Array.range stmt.inputs.size).any fun i =>
      i != statePos && (stmt.scalarKinds[i]? |>.join).isNone
    -- the draw key is present only when containers beside the state
    -- were drawn; in this position an `if` term does not parse as a
    -- structure field value, so the three optionals bind first
    let keySeed : Option Nat := if hasOthers then some seedOpt else none
    let keySize : Option Nat := if hasOthers then some sizeOpt else none
    let keyDraw : Option Nat := if hasOthers then some 0 else none
    -- one `with` clause per line: at this column the with-form instance
    -- does not continue across a newline
    let entry0 : HintEntry := { head with builder := some name, knobs := some k }
    let entry1 : HintEntry := { entry0 with seed := keySeed, size := keySize, draw := keyDraw }
    let entry : HintEntry := { entry1 with scalars := scalars }
    pure (some entry)
  | _ => return none

/-! ## What one attempt did -/

/-- The per-case answer of one hint attempt, which the outcome line's
`hint` field folds up (§16.1). Staleness is the fingerprint's answer;
the check decides the replay itself: a stale hint that replays is
`staleReplayed`. -/
inductive HintAttempt where
  | replayed
  | staleReplayed
  | failed
  | staleFailed
  deriving DecidableEq, Repr, Inhabited

/-- The outcome line's `hint` field for one run (§16.1). One value per
run, so the answers fold by their worst reader-relevant case: a failure
outranks a missing entry, a missing entry outranks a replay, and
staleness refines whichever it touched. A case that won from a search is
missing, whether the file holds other cases' entries or none: the
committed file did not cover it, and in `use` mode that is witness churn
a reader must see. `none` when no case ran. -/
def Hint.runHintField (mode : HintMode) (file? : Option HintFile)
    (preset : PresetId) (caseCount : Nat) (wonFresh : Nat)
    (attempts : Array (Nat × HintAttempt)) : Option String :=
  if caseCount == 0 then none
  else if mode == .ignore then some "ignored"
  else
    let empty : HintFile := { «theorem» := .anonymous, fingerprint := "", entries := #[] }
    let entryCases :=
      ((file?.getD empty).entries.filter (·.preset == preset)).map (·.«case»)
    if entryCases.isEmpty then some "missing"
    else
      let found := entryCases.filterMap fun i =>
        attempts.find? fun (j, _) => j == i
      if found.any (·.2 == .staleFailed) then some "stale-failed"
      else if found.any (·.2 == .failed) then some "failed"
      else if wonFresh > 0 || found.size != entryCases.size then
        some "missing"
      else if found.any (·.2 == .staleReplayed) then some "stale-replayed"
      else some "replayed"

/-! ## The source -/

/-- The entry one file holds for a preset, case, and side. -/
def Hint.entryFor (f : HintFile) (preset : PresetId) (caseIndex : Nat)
    (side : Option Bool) : Option HintEntry :=
  f.entries.find? fun e =>
    e.preset == preset && e.«case» == caseIndex && e.side == side

/-- The hint source (§9.8). `applies` reads the loaded file, so the run
loads it once and the search never touches the disk. `search` rebuilds
the candidate and checks it with the probe, so the log knows the answer;
the search loop's own check runs the same pure function again and is the
single arbiter (§9.3). The mode is the caller's: `ignore` never applies,
and `require` is the command's error at the loop, because a source's
`nothing` cannot fail a build. -/
def Hint.source (mode : HintMode) (file? : Option HintFile)
    (fingerprint : String) (log : IO.Ref (Array (Nat × HintAttempt))) :
    WitnessSource where
  -- the tag never names a record: every candidate carries its origin
  -- override, and the tag shows only in a `notFound` reason's tried
  -- list, where it reads as the hint source's attempt
  tag := .hinted .base
  applies ctx _ c :=
    mode != .ignore &&
    (match file? with
      | none => false
      | some f =>
        match Hint.entryFor f ctx.preset c.index c.side with
        | none => false
        -- a notFound entry records the case's empty answer; the
        -- command's case loop answers it before the sources run (the
        -- plan's stage-6 step 9)
        | some e => e.notFound.isNone && (entrySource e.source).isSome)
  search ctx stmt c := do
    let some f := file? | return .nothing
    let some e := Hint.entryFor f ctx.preset c.index c.side
      | return .nothing
    let stale := (e.fingerprint.getD f.fingerprint) != fingerprint
    let attempt : HintAttempt :=
      match stale with
      | false => .failed
      | true => .staleFailed
    match ← Hint.rebuild ctx stmt e with
    | none =>
      log.set ((← log.get) ++ #[(c.index, attempt)])
      return .nothing
        (some "the hint's source carries no rebuildable candidate")
    | some a =>
      -- §9.4, the stage-4 outcome: the bounds gate runs before the
      -- check, so a stale hint's rebuilt candidate never sends an
      -- out-of-range read into the compiled `decide`
      if (ctx.probe.safe c.index a).all (· == true) then
        if ctx.probe.check c.index a then
          let ok : HintAttempt :=
            match stale with
            | false => .replayed
            | true => .staleReplayed
          log.set ((← log.get) ++ #[(c.index, ok)])
          -- the replayed winner: the record's source names the hint with
          -- the source it replays, unwrapped once, so a hand-edited
          -- `hinted-x` entry still writes a tag the record reader reads
          -- back (§9.8)
          let orig := (entrySource e.source).getD .base
          return .candidate a (some (.hinted orig))
      log.set ((← log.get) ++ #[(c.index, attempt)])
      return .nothing
        (some "the hint's candidate failed the check")

end EthCLLib.TheoremVectors
