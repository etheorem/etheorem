import Lean
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Witness.Built
import EthCLLib.TheoremVectors.Tests.ToyFork

/-!
# `EthCLLib.TheoremVectors.Tests.Built`: the builder grid and the cache

Build-gate checks for stage 6 (`THEOREM_VECTORS_ARCHITECTURE.md` §9.9), over the
framework half alone:

- the grid is the architecture's six steps, cheapest first, and the
  epoch boundary is in preset units;
- the `builtSteps` option answers per preset, and an explicit positive
  value applies at both;
- the knobs round trip through their JSON, the form the built hint row
  writes;
- the cache returns the same bytes on a second call, answers a same-stamp
  call from the file even when the file was clobbered, and rebuilds when
  the stamp changes;
- the stamp of a real module is the non-empty trace text, and a module
  that is not on disk stamps `""`.

The toy `Probe` here builds bytes from its arguments, so a cache hit and
a rebuild are distinguishable by content. The scratch tree lives under
this package's `.lake/build`, which the gitignore carries, and the last
step removes it.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors.Tests.Built

/-- The scratch cache root, under the package's gitignored build tree. -/
def scratchRoot : System.FilePath := ".lake/build/test-theorem-vectors-built"

/-- A toy binding with its own tag, so the cache paths in this file
never meet another test's entries. The cache pins pass builder indexes
directly, and the stamp test reads the binding constant's own module
through `stampOfBinding`, so the catalog stays empty. -/
def toyBinding : ForkBinding :=
  { Tests.ToyFork.toyBinding with tag := "toybuilt" }

/-- A toy probe whose `build` face derives its bytes from the builder
index and the knobs, so cache hits and rebuilds differ by content. -/
def toyProbe : Probe where
  check _ _ := true
  sample _ _ := #[]
  shrink _ := #[]
  reads _ _ := #[]
  safe _ _ := #[]
  seeds := #[]
  defaults := #[]
  build i k := leBytes 8 (i * 1000 + k.validators + k.slot + k.queue + 1)
  run _ := .error "the toy probe does not run"

end EthCLLib.TheoremVectors.Tests.Built

open Lean Elab.Command
open EthCLLib.TheoremVectors
open EthCLLib.TheoremVectors.Tests.Built in
run_cmd do
  liftTermElabM do
    -- ── the grid: the architecture's six steps, cheapest first, with the
    -- boundary in preset units
    let grid := Built.grid 8
    unless grid.size == 6 do
      throwError s!"the grid holds {grid.size} steps, expected six"
    unless (grid.map (·.1)) == #["genesis", "advanced", "upgraded",
        "advanced", "withQueue", "advanced"] do
      throwError "the grid's builder order drifted"
    unless grid[1]!.2.slot == 8 && grid[2]!.2.slot == 8 do
      throwError "the boundary steps do not carry the boundary slot"
    unless grid[0]!.2.validators == 8 && grid[3]!.2.validators == 16 &&
        grid[4]!.2.queue == 4 && grid[5]!.2.validators == 64 do
      throwError "the grid's knobs drifted"

    -- ── the `builtSteps` option: per-preset defaults, explicit override
    unless (← builtStepsOf .minimal) == 6 do
      throwError "minimal's default grid cap is six"
    unless (← builtStepsOf .mainnet) == 3 do
      throwError "mainnet's default grid cap is three"
    let capped := do
      withOptions (fun o => theorem_vectors.builtSteps.set o 4) (builtStepsOf .mainnet)
    unless (← capped) == 4 do
      throwError "an explicit positive cap applies at both presets"

    -- ── the knobs' JSON round trip, the built hint row's form
    let k : Knobs := { validators := 16, slot := 40, balance := 32000000000, queue := 4 }
    match fromJson? (α := Knobs) (toJson k) with
    | .ok k2 =>
      unless k2 == k do
        throwError s!"the knobs' JSON round trip changed them: {repr k2}"
    | .error e => throwError s!"the knobs' JSON round trip failed: {e}"

    -- ── the cache: same bytes on a second call, a same-stamp call reads
    -- the file, a changed stamp rebuilds
    if ← scratchRoot.pathExists then IO.FS.removeDirAll scratchRoot
    let stampA := "stamp-a"
    let path := Built.cachePath scratchRoot toyBinding.tag .minimal "advanced"
      { validators := 8, slot := 8 }
    let first ← Built.stateBytes scratchRoot toyBinding.tag .minimal "advanced"
      stampA toyProbe 1 { validators := 8, slot := 8 }
    unless first == leBytes 8 (1000 + 8 + 8 + 0 + 1) do
      throwError "the first call did not build the toy bytes"
    -- the entry and its stamp are on disk
    unless ← path.pathExists do
      throwError "the cache entry is missing after the first call"
    -- a second call with the same stamp returns the same bytes
    let second ← Built.stateBytes scratchRoot toyBinding.tag .minimal "advanced"
      stampA toyProbe 1 { validators := 8, slot := 8 }
    unless second == first do
      throwError "the second call rebuilt instead of reading the cache"
    -- a same-stamp call answers from the file even when the file was
    -- clobbered
    IO.FS.writeBinFile path (leBytes 8 999)
    let clobbered ← Built.stateBytes scratchRoot toyBinding.tag .minimal "advanced"
      stampA toyProbe 1 { validators := 8, slot := 8 }
    unless clobbered == leBytes 8 999 do
      throwError "a same-stamp call did not read the cached file"
    -- a changed stamp rebuilds and rewrites the entry; the old stamp's
    -- view is gone, the new one holds the built bytes
    let rebuilt ← Built.stateBytes scratchRoot toyBinding.tag .minimal "advanced"
      "stamp-b" toyProbe 1 { validators := 8, slot := 8 }
    unless rebuilt == first do
      throwError "a changed stamp did not rebuild"
    unless (← Built.read "stamp-b" path).any (· == first) do
      throwError "the rebuilt entry does not read back under the new stamp"
    unless (← Built.read stampA path).isNone do
      throwError "the old stamp still reads the rewritten entry"
    -- the grid steps share one entry per distinct knobs: two steps with
    -- the same builder name but different knobs write different files
    let p2 := Built.cachePath scratchRoot toyBinding.tag .minimal "advanced"
      { validators := 16, slot := 40 }
    unless p2.toString != path.toString do
      throwError "two knob sets mapped to one cache path"

    -- ── the stamps: a real module's trace text is non-empty, a missing
    -- module stamps empty, and the binding stamp drops the last atom
    let realStamp ← Built.stampOf `EthCLLib.TheoremVectors.Tests.ToyFork
    if realStamp.isEmpty then
      throwError "a built module's stamp is empty"
    let missingStamp ← Built.stampOf `EthCLLib.TheoremVectors.Tests.NoSuchModule
    unless missingStamp.isEmpty do
      throwError "a missing module stamped non-empty text"
    unless (← Built.stampOfBinding
        `EthCLLib.TheoremVectors.Tests.ToyFork.toyBinding) == realStamp do
      throwError "the binding stamp did not read the binding module's trace"

    -- the epoch boundary reads the fork's own constant; the toy fork
    -- names none, so the fallback answers
    unless (← Built.epochBoundaryOf toyBinding .minimal) == 8 do
      throwError "a fork without `Const.slotsPerEpoch` takes the fallback 8"

    -- the scratch tree goes away
    IO.FS.removeDirAll scratchRoot
