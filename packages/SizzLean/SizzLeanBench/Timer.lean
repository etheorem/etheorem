/-!
# `SizzLeanBench.Timer`: wall-clock helpers for microbenchmarks

Thin wrappers around Lean's built-in `IO.monoNanosNow : BaseIO Nat`
that produce per-iteration nanosecond samples for the bench
runner's TSV output. No FFI; no clock-source assumptions beyond
what Lean already trusts.

`monoNanosNow` is the right clock for microbenchmarks here: it is
the system's *monotonic* clock (immune to wall-clock adjustments
during the run), reports in nanoseconds, and has resolution
well below the millisecond range every microbench below cares
about.

## Usage

```lean
let (root, ns) ← Timer.timeAction do
  pure (someFixture.hashTreeRoot)
IO.println s!"once: {ns} ns"

let samples ← Timer.timeIterations 1000 do
  pure (someFixture.hashTreeRoot)
let s := Stats.ofSamples samples
IO.println s!"{s.mean} ± {s.stddev} ns ({s.min}..{s.max}, median {s.median})"
```
-/

set_option autoImplicit false

namespace SizzLeanBench.Timer

/-- Run one `IO` action and return its result paired with the
elapsed nanoseconds (monotonic clock). Convenient when a single
shot of a benchmark is enough; for repeated runs use
`timeIterations` instead. -/
def timeAction {α : Type} (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Run an `IO` action `n` times and return an array of per-
iteration elapsed nanoseconds. The action's *value* is discarded
each iteration, we only care about timing. Each invocation is
independent: the action runs from scratch every iteration so
JIT effects, allocator state, and any caches re-warm with each
sample.

For one-shot setup that must NOT be timed, sequence it before
calling `timeIterations`:

```lean
let fixture := buildFixture          -- one-shot setup
let samples ← timeIterations 1000 do
  pure (someOp fixture)              -- only this is timed
```
-/
def timeIterations {α : Type} (n : Nat) (act : IO α) : IO (Array Nat) := do
  let mut samples : Array Nat := Array.mkEmpty n
  for _ in [:n] do
    let t0 ← IO.monoNanosNow
    let _ ← act
    let t1 ← IO.monoNanosNow
    samples := samples.push (t1 - t0)
  return samples

end SizzLeanBench.Timer
