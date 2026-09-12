import SizzLeanBench.CompBench.Hashers
import SizzLeanBench.CompBench.Scenarios

/-!
# `SizzLeanBench.CompBenchMain`: the `ssz_compbench` exe driver

The SizzLean side of the comparative benchmark. Two subcommands:

```
ssz_compbench emit <path>          # write the shared fixture's wire bytes
ssz_compbench run  <path> <reps>   # run the scenarios over those bytes
ssz_compbench hashers              # price one Merkle step, both FFI paths
```

`emit` runs first. It serializes
`SizzLeanBench.CompBench.Fixture.mkBeaconState` and writes the
buffer, so the Rust and the Python harnesses decode the very bytes
this one does. It prints the buffer's length and the value's root
on stderr, which is where the driver reads the fixture's shape
from.

`run` prints one JSON object per line on stdout, one line per
repetition of each configuration and scenario. Every other harness
prints the same line shape, so the driver reads all three the same
way. Diagnostics go to stderr, which keeps stdout parseable.

`hashers` prices the two FFI SHA-256 entry points on their own, so a
reader can multiply by a tree's node count and see how much of a
root is hashing. It takes no fixture and the driver does not call
it; run it by hand when a root's cost needs accounting for.

The driver is `scripts/comparative_benchmark.py`.
-/

set_option autoImplicit false

open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open SizzLeanBench.CompBench
open SizzLeanBench.CompBench.Scenarios

/-- One result line. The field names are the contract between the
three harnesses and the driver; the Rust and the Python copies
print the same keys. -/
private def printLine (impl scenario : String) (rep : Nat) (s : Sample)
    (root1 root2 : String) : IO Unit :=
  IO.println <| String.join
    [ "{\"impl\": \"", impl, "\", \"scenario\": \"", scenario, "\", \"rep\": ", toString rep
    , ", \"deser_ns\": ", toString s.deserNs
    , ", \"wrap_ns\": ", toString s.wrapNs
    , ", \"root1_ns\": ", toString s.root1Ns
    , ", \"update_ns\": ", toString s.updateNs
    , ", \"root2_ns\": ", toString s.root2Ns
    , ", \"root1\": \"", root1, "\", \"root2\": \"", root2, "\"}" ]

/-- Run one configuration against one scenario, `reps` times. -/
private def runConfig (impl scenario : String) (reps : Nat)
    (bytes : ByteArray) (sink : IO.Ref Nat)
    (go : ByteArray → IO.Ref Nat → IO (Sample × String × String)) : IO Unit := do
  for rep in [:reps] do
    let (sample, root1, root2) ← go bytes sink
    printLine impl scenario rep sample root1 root2

/-- Write the fixture's wire bytes, and report its size and root
on stderr. -/
private def emit (path : String) : IO UInt32 := do
  let value := Fixture.mkBeaconState
  let bytes := SSZ.serialize value
  IO.FS.writeBinFile (System.FilePath.mk path) bytes
  let root := SSZ.hashTreeRoot Sha256 value
  IO.eprintln s!"fixture bytes: {bytes.size}"
  IO.eprintln s!"fixture root: {rootHex root}"
  return 0

/-- Run the four (configuration × scenario) pairs over the emitted
bytes. `SSZ.FastBox` is the cached production path; `SSZ.PureBox`
recomputes every root. Both pin the FFI SHA-256. -/
private def run (path : String) (reps : Nat) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile (System.FilePath.mk path)
  let sink ← IO.mkRef (0 : Nat)
  runConfig "sizzlean-fast" "update1" reps bytes sink
    (runOnce (fun v => SSZ.FastBox v) writeOne)
  runConfig "sizzlean-fast" "update1000" reps bytes sink
    (runOnce (fun v => SSZ.FastBox v) writeThousand)
  runConfig "sizzlean-pure" "update1" reps bytes sink
    (runOnce (fun v => SSZ.PureBox v) writeOne)
  runConfig "sizzlean-pure" "update1000" reps bytes sink
    (runOnce (fun v => SSZ.PureBox v) writeThousand)
  -- The sink forces every root the run computed; a zero here would
  -- mean the compiler dropped the work the timings claim to cover.
  if (← sink.get) == 0 then IO.eprintln "warning: result sink is zero"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", path] => emit path
  | ["hashers"] =>
    SizzLeanBench.CompBench.Hashers.runAll 100000
    return 0
  | ["run", path, reps] =>
    match reps.toNat? with
    | some n => run path n
    | none =>
      IO.eprintln s!"ssz_compbench: repetition count is not a number: {reps}"
      return 1
  | _ =>
    IO.eprintln "usage: ssz_compbench emit <path> | ssz_compbench run <path> <reps> \
      | ssz_compbench hashers"
    return 1
