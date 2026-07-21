import EthCLSpecs

/-!
# `EthCLSpecs.PySpecTests.Server`: the long-lived pyspec server (`pyspec_server`)

The runner exe instantiates the generic `PySpecTests` driver at a fork and runs
the request/result loop the Python `pytest-xdist` harness talks to
(`FRAMEWORK_ARCHITECTURE.md` §13.3). One server per `xdist` worker, held through a
`session`-scoped fixture, so there is no per-vector Lean startup and the crypto
cache stays warm across a worker's stream of vectors.

## The wire protocol

The Python side snappy-decompresses each case's SSZ blobs to temp files and sends
one tab-separated request line per case; the server reads the files, runs the
case through `runCase`, and writes one result line. Keeping the bytes on disk and
passing paths avoids framing binary SSZ on the line.

Request (8 tab-separated fields):
```
runner ⇥ handler ⇥ prePath ⇥ postPath ⇥ blsSetting ⇥ blocksCount ⇥ forkEpoch ⇥ inputPaths
```
`postPath` / `forkEpoch` are `-` when absent (an absent `post` marks an invalid
vector); `inputPaths` is comma-separated (possibly empty).

Result (the driver's `CaseResult.render`):
```
pass|fail ⇥ bucket ⇥ detail
```

## Crash recovery

Every request is processed inside a `try`/`catch`: a malformed request or an
unreadable file reports `fail ⇥ bug ⇥ <reason>` and the loop continues, so one
bad case never hangs the worker. A request that dies harder (the process is
killed) is handled on the Python side: the fixture re-spawns the server and the
in-flight case reports failed. The empty line / EOF ends the loop cleanly.
-/

open EthCLLib.Spec
open EthCLLib.PySpecTests
open EthCLSpecs.Fulu

namespace EthCLSpecs.PySpecTests

/-- Parse `forkEpoch` / `postPath` sentinel `-` as "absent". -/
private def dashToNone (s : String) : Option String :=
  if s == "-" then none else some s

/-- Parse a Gloas PTC vote token (`t`/`f`/`n` per slot, comma-joined) into the
three-valued vote array a `payload_*_vote` check compares against. -/
private def parseVotes (s : String) : Array (Option Bool) :=
  (s.splitOn ",").toArray.map fun c => if c == "t" then some true else if c == "f" then some false else none

/-- Read a request's referenced files and build a `CaseRequest`. -/
private def buildRequest (fields : Array String) : IO CaseRequest := do
  if fields.size < 9 then
    throw (IO.userError s!"malformed request: expected ≥9 tab-fields, got {fields.size}")

  let runner  := fields[0]!
  let handler := fields[1]!
  -- `pre` is `-` for formats with no single pre-state file (`fork_choice`'s
  -- step/check cases); an empty buffer stands in until those formats are wired.
  let pre ← match dashToNone fields[2]! with
    | none   => pure ByteArray.empty
    | some p => IO.FS.readBinFile p
  let post ← match dashToNone fields[3]! with
    | none   => pure none
    | some p => some <$> IO.FS.readBinFile p
  let blsSetting  := fields[4]!.toNat!
  let blocksCount := fields[5]!.toNat!
  let forkEpoch   := (dashToNone fields[6]!).map (·.toNat!)
  let inputPaths  := if fields[7]!.isEmpty then #[] else (fields[7]!.splitOn ",").toArray
  let forkBlock   := (dashToNone fields[8]!).map (·.toNat!)
  -- Optional 10th field: `execution_valid` for `operations/execution_payload` (the
  -- mocked EL verdict); absent ⇒ `true`.
  let executionValid := (fields[9]?.getD "1") == "1"

  let mut inputs : Array ByteArray := #[]
  for p in inputPaths do
    inputs := inputs.push (← IO.FS.readBinFile p)

  return {
    runner, handler, pre, post, inputs,
    caseMeta := { blsSetting, blocksCount, forkEpoch, forkBlock, executionValid }
  }

/-- One hex digit's value (`0` for a non-digit, the caller controls the input). -/
private def hexDigit (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Parse a `0x`-prefixed hex string into a `ByteArray`. -/
private def hexToBytes (s : String) : ByteArray := Id.run do
  let cs0 := s.toList.toArray
  let cs := if s.startsWith "0x" then cs0.extract 2 cs0.size else cs0

  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (hexDigit cs[2*i]! * 16 + hexDigit cs[2*i+1]!))
  return out

/-- The `ssz_static` request path: read the decompressed container bytes, run them
through the fork's `sszStatic` (decode → hash-tree-root → round-trip), and compare
the root to the vector's `roots.yaml` value. Request fields:
`ssz_static ⇥ typeName ⇥ serializedPath ⇥ expectedRootHex`. A type the fork does
not model returns `todo` (xfail); a root or round-trip mismatch is a bug. -/
private def handleSszStatic (iface : ForkInterface) (fields : Array String) : IO String := do
  let typeName := fields[1]!
  let bytes ← IO.FS.readBinFile fields[2]!
  let expected := hexToBytes fields[3]!
  match iface.sszStatic typeName bytes with
  | .ok (root, roundTripOk) =>
    if root != expected then
      return "fail\tbug\troot mismatch"
    else if !roundTripOk then
      return "fail\tbug\tround-trip mismatch (re-serialize ≠ input)"
    else
      return "pass\tpassing\t"
  | .error (.spec (.todo d))       => return s!"fail\ttodo\t{d}"
  | .error (.spec (.outOfScope d)) => return s!"fail\tskip\t{d}"
  | .error e =>
    let detail := (match e with
      | .decode what => s!"{what} decode failed"
      | _            => "ssz_static error").replace "\t" " " |>.replace "\n" " "
    return s!"fail\tbug\t{detail}"

/-- The fork-choice request path: read the anchor state / block and the step
script (a line per `steps.yaml` entry, referencing decompressed SSZ files by
path), decode the steps, and run the fork's `runForkChoice` interpreter. -/
private def handleForkChoice (iface : ForkInterface) (fields : Array String) : IO String := do
  let anchorState ← IO.FS.readBinFile fields[2]!
  let inputs := if fields[7]!.isEmpty then #[] else (fields[7]!.splitOn ",").toArray
  let anchorBlock ← IO.FS.readBinFile inputs[0]!
  let scriptTxt ← IO.FS.readFile inputs[1]!

  -- Decode the step script: one `steps.yaml` entry per line, the leading token names
  -- the step and the rest reference its decompressed SSZ files / scalar arguments.
  let mut steps : Array FcStep := #[]
  for rawLine in scriptTxt.splitOn "\n" do
    let parts := ((rawLine.splitOn " ").filter (· != "")).toArray
    if h : parts.size > 0 then
      match parts[0] with
      | "tick"              => steps := steps.push (.tick parts[1]!.toNat!)
      | "block"             =>
        let b ← IO.FS.readBinFile parts[1]!
        -- Optional 4th token: comma-separated PeerDAS column-sidecar paths (`-` if none).
        let cols ← if parts.size > 3 && parts[3]! != "-" then
            (parts[3]!.splitOn ",").toArray.mapM (fun (p : String) => IO.FS.readBinFile (System.FilePath.mk p))
          else pure #[]
        steps := steps.push (.block b cols (parts[2]! == "1"))
      | "attestation"       => let b ← IO.FS.readBinFile parts[1]!; steps := steps.push (.attestation b (parts.size ≤ 2 || parts[2]! == "1"))
      | "attester_slashing" => let b ← IO.FS.readBinFile parts[1]!; steps := steps.push (.attesterSlashing b (parts.size ≤ 2 || parts[2]! == "1"))
      | "head"              => steps := steps.push (.checkHead (hexToBytes parts[1]!) parts[2]!.toNat!)
      | "get_proposer_head" => steps := steps.push (.checkProposerHead (hexToBytes parts[1]!))
      | "execution_payload" => let b ← IO.FS.readBinFile parts[1]!; steps := steps.push (.executionPayload b (parts[2]! == "1"))
      | "payload_attestation_message" => let b ← IO.FS.readBinFile parts[1]!; steps := steps.push (.payloadAttestationMessage b (parts[2]! == "1"))
      | "head_payload_status" => steps := steps.push (.checkHeadPayloadStatus parts[1]!.toNat!)
      | "payload_timeliness_vote"        => steps := steps.push (.checkPayloadTimelinessVote (hexToBytes parts[1]!) (parseVotes parts[2]!))
      | "payload_data_availability_vote" => steps := steps.push (.checkPayloadDataAvailabilityVote (hexToBytes parts[1]!) (parseVotes parts[2]!))
      | "justified"         => steps := steps.push (.checkJustified parts[1]!.toNat! (hexToBytes parts[2]!))
      | "finalized"         => steps := steps.push (.checkFinalized parts[1]!.toNat! (hexToBytes parts[2]!))
      | "boost"             => steps := steps.push (.checkBoost (hexToBytes parts[1]!))
      | "time"              => steps := steps.push (.checkTime parts[1]!.toNat!)
      | "genesis_time"      => steps := steps.push (.checkGenesisTime parts[1]!.toNat!)
      | "unsupported"       =>
        -- `harness.py` passes the specific descriptor (`should_override_forkchoice_update`, or an
        -- unrecognized step key like `on_inclusion_list`), so the xfail reason is accurate.
        let reason := if parts.size > 1 then String.intercalate " " (parts.toList.drop 1) else "unmodeled step"
        steps := steps.push (.unsupported s!"unsupported fork-choice step: {reason}")
      -- An unrecognized token surfaces as `unsupported` (a `todo` xfail) rather than silently
      -- dropping the step; `harness.py` already maps unknown steps.yaml keys to `unsupported`,
      -- so this is the second line of defense.
      | other               => steps := steps.push (.unsupported s!"unrecognized fork-choice step: {other}")

  match iface.runForkChoice anchorState anchorBlock steps with
  | .ok ()   => return "pass\tpassing\t"
  | .error e =>
    -- Classify the runner error: a `spec todo` means unfinished work (reported `xfail`), a
    -- `spec outOfScope` means deliberately unmodeled (reported `skip`); everything else (a
    -- decode failure, a check mismatch, an unexpected rejection, a missing store key) is
    -- a bug on the fork-choice path (per-step `valid:false` rejections are resolved inside
    -- the interpreter and never reach here).
    let detail := (match e with
      | .decode what           => s!"{what} decode failed"
      | .spec (.assert d)      => d
      | .spec (.todo d)        => d
      | .spec (.outOfScope d)  => d
      | .spec (.missingKey _)  => "missing store key"
      | .spec (.transition te) => reprStr te).replace "\t" " " |>.replace "\n" " "
    match e with
    | .spec (.todo _)       => return s!"fail\ttodo\t{detail}"
    | .spec (.outOfScope _) => return s!"fail\tskip\t{detail}"
    | _                     => return s!"fail\tbug\t{detail}"

/-- Process one request line into a result line, against a given fork's interface.
Exceptions become a `fail ⇥ bug` result so a single bad case never crashes the
loop. -/
private def handleLine (iface : ForkInterface) (line : String) : IO String := do
  try
    let fields := (line.splitOn "\t").toArray
    if fields[0]? == some "ssz_static" then
      handleSszStatic iface fields
    else if fields[0]? == some "fork_choice" then
      handleForkChoice iface fields
    else
      let req ← buildRequest fields
      return (@runCase iface req).render
  catch e =>
    -- Single-line, tab-free reason so the harness parses it.
    let reason := (toString e).replace "\t" " " |>.replace "\n" " "
    return s!"fail\tbug\t{reason}"

/-- The request/result loop at one fork's interface. Reads a line, emits a
result, flushes, repeats; the empty line / EOF ends it. -/
partial def serve (iface : ForkInterface) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO UInt32 := do
    -- Strip the line ending while keeping interior / trailing tabs (the final
    -- `inputPaths` field is empty, hence a trailing tab, when a case has no inputs).
    let line := ((← stdin.getLine).dropEndWhile (fun c => c == '\n' || c == '\r')).toString
    if line.isEmpty then
      return 0
    let result ← handleLine iface line
    stdout.putStrLn result
    stdout.flush
    loop
  loop

/-- Lowercase hex of a byte buffer, for the `stateroot` debug mode. -/
def toHex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length == 1 then "0" ++ s else s)

/-- Resolve a fork name to its minimal-preset interface; `none` for an unknown name.
`main` uses this to error on a bad fork argument instead of inheriting
`pickInterface`'s silent Fulu default (kept only for the documented no-argument
invocation). -/
def forkInterface? (forkName : String) : Option ForkInterface :=
  match forkName with
  | "fulu"  => some EthCLSpecs.Fulu.Interface.fuluInterface
  | "gloas" => some EthCLSpecs.Gloas.Interface.gloasInterface
  | "heze"  => some EthCLSpecs.Heze.Interface.hezeInterface
  | _       => none

/-- Select a fork's interface at a preset. -/
@[reducible] def pickInterface (forkName preset : String) : ForkInterface :=
  match forkName, preset with
  | "gloas", "mainnet" => EthCLSpecs.Gloas.Interface.gloasInterfaceMainnet
  | "gloas", _         => EthCLSpecs.Gloas.Interface.gloasInterface
  | "heze",  "mainnet" => EthCLSpecs.Heze.Interface.hezeInterfaceMainnet
  | "heze",  _         => EthCLSpecs.Heze.Interface.hezeInterface
  | _,       "mainnet" => EthCLSpecs.Fulu.Interface.fuluInterfaceMainnet
  | _,       _         => EthCLSpecs.Fulu.Interface.fuluInterface

/-- Serve at a named fork/preset, erroring on the names `pickInterface` would silently
default. An unknown fork or preset here is a typo'd invocation (the pytest harness passes
exact names), and silently decoding another fork's SSZ shows up as a wall of opaque decode
failures instead of one clear message. -/
def serveKnown (forkName preset : String) : IO UInt32 := do
  if (forkInterface? forkName).isNone then
    IO.eprintln s!"unknown fork: {forkName} (expected fulu / gloas / heze)"; return 2
  else if preset != "minimal" && preset != "mainnet" then
    IO.eprintln s!"unknown preset: {preset} (expected minimal / mainnet)"; return 2
  else
    serve (pickInterface forkName preset)

end EthCLSpecs.PySpecTests

/-- The exe entry point. `pyspec_server [fork [preset]]` runs the server loop at
the named fork's interface and preset; the no-argument invocation defaults to
`fulu` / `minimal`, and a named-but-unknown fork or preset is an error rather
than a silent Fulu fallback. The `stateroot [fork] <path>` mode decodes a
`BeaconState` and prints its root (a decode / container-layer sanity check). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["stateroot", path] =>
    -- `stateroot <fork>` with the path forgotten lands here with `path` bound to the
    -- fork name (and would decode a file of that name as Fulu); catch it explicitly.
    if (EthCLSpecs.PySpecTests.forkInterface? path).isSome then
      IO.eprintln s!"stateroot: missing <path> after fork name {path}"; return 2
    else
      let bytes ← IO.FS.readBinFile path
      match EthCLSpecs.Fulu.Interface.fuluInterface.stateRoot bytes with
      | .ok root => IO.println (EthCLSpecs.PySpecTests.toHex root); return 0
      | .error e => IO.eprintln s!"decode failed: {repr e}"; return 1
  -- The pattern binder cannot be named `fork`, because `fork` is a keyword of the spec
  -- DSL; use `forkName`, as in the serve arms below.
  | ["stateroot", forkName, path] =>
    match EthCLSpecs.PySpecTests.forkInterface? forkName with
    | none => IO.eprintln s!"unknown fork: {forkName} (expected fulu / gloas / heze)"; return 2
    | some iface =>
      let bytes ← IO.FS.readBinFile path
      match iface.stateRoot bytes with
      | .ok root => IO.println (EthCLSpecs.PySpecTests.toHex root); return 0
      | .error e => IO.eprintln s!"decode failed: {repr e}"; return 1
  | [forkName, preset] => EthCLSpecs.PySpecTests.serveKnown forkName preset
  | [forkName]         => EthCLSpecs.PySpecTests.serveKnown forkName "minimal"
  | []                 => EthCLSpecs.PySpecTests.serve EthCLSpecs.Fulu.Interface.fuluInterface
  | _ =>
    IO.eprintln "usage: pyspec_server [fork [preset]] | pyspec_server stateroot [fork] <path>"
    return 2
