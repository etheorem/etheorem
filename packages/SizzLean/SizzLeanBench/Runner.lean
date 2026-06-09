import SizzLeanBench.Timer

/-!
# `SizzLeanBench.Runner`: labelled benchmark driver, TSV output

A microbenchmark in SizzLean is a labelled `IO α` action plus an
iteration count. The runner samples it via `Timer.timeIterations`,
computes simple statistics (median / mean / stddev / min / max),
and prints one TSV row per benchmark. Output goes to stdout; the
`ssz_bench` exe driver redirects it to `bench/<timestamp>.tsv`.

TSV is chosen over JSON / Markdown because diffs across two runs
are the workflow ("before" vs "after" a code change), and
`diff -u before.tsv after.tsv` is the simplest possible comparator.
Columns are fixed-width-friendly: a benchmark whose label changes
between runs is treated as a new row, never a renamed one.

## TSV column shape

```
label                                    iterations   median_ns   mean_ns   stddev_ns   min_ns   max_ns
merkleRootWithCache cold (depth 5)              100        4523      4711         312     4102     5891
merkleRootWithCache warm (cache hit)            100          18        19           4       12       28
```

The header is printed once per `runBench` invocation by default.
For multi-bench-file runs, pass `header := false` after the first
to keep one header per TSV.
-/

set_option autoImplicit false

namespace SizzLeanBench.Runner

open SizzLeanBench.Timer

/-- Summary statistics over a per-iteration nanosecond sample
array. Sample size must be ≥ 1 (use a guard in `runBench`). -/
structure Stats where
  iterations : Nat
  median     : Nat
  mean       : Nat
  stddev     : Nat
  min        : Nat
  max        : Nat
  deriving Repr

private def sumArray (xs : Array Nat) : Nat :=
  xs.foldl (init := 0) (· + ·)

private def minArray (xs : Array Nat) : Nat :=
  xs.foldl (init := xs[0]!) Nat.min

private def maxArray (xs : Array Nat) : Nat :=
  xs.foldl (init := 0) Nat.max

private def sortAscending (xs : Array Nat) : Array Nat :=
  xs.qsort (· < ·)

/-- Build a `Stats` over a non-empty sample array. Variance is
computed as the population variance (denominator `n`, not
`n − 1`); `stddev = sqrt variance`. For sub-millisecond samples
the population vs sample distinction is in the noise. -/
def Stats.ofSamples (xs : Array Nat) : Stats :=
  let n := xs.size
  if n == 0 then
    { iterations := 0, median := 0, mean := 0, stddev := 0, min := 0, max := 0 }
  else
    let total := sumArray xs
    let mean := total / n
    let sorted := sortAscending xs
    let median := sorted[n / 2]!
    let lo := minArray xs
    let hi := maxArray xs
    -- Variance: avg of squared deviations. Nat-safe form.
    let sqDevSum := xs.foldl (init := 0) fun acc x =>
      let d := if x ≥ mean then x - mean else mean - x
      acc + d * d
    let variance := sqDevSum / n
    -- Integer sqrt via Newton's method, capped at 64 iters.
    let rec isqrt (n iters : Nat) (g : Nat) : Nat :=
      if iters == 0 || g == 0 then g
      else
        let g' := (g + n / g) / 2
        if g' >= g then g else isqrt n (iters - 1) g'
    let stddev := isqrt variance 64 (variance + 1)
    { iterations := n, median := median, mean := mean,
      stddev := stddev, min := lo, max := hi }

/-- Emit the TSV header row to stdout. Call once per
`ssz_bench` invocation. -/
def printHeader : IO Unit :=
  IO.println "label\titerations\tmedian_ns\tmean_ns\tstddev_ns\tmin_ns\tmax_ns"

/-- Emit one TSV row for a labelled benchmark. The Stats numbers
are tab-separated and column-stable across runs so `diff` over
two TSVs reads as "did each row move." -/
def printRow (label : String) (s : Stats) : IO Unit :=
  IO.println s!"{label}\t{s.iterations}\t{s.median}\t{s.mean}\t{s.stddev}\t{s.min}\t{s.max}"

/-- Run one named benchmark `iterations` times and print one TSV
row with its stats. The action's return value is ignored, we
care only about timing. Setup that must not be timed should be
performed *before* `runBench` and captured into the action's
closure. -/
def runBench {α : Type} (label : String) (iterations : Nat) (act : IO α) :
    IO Unit := do
  let samples ← timeIterations iterations act
  let stats := Stats.ofSamples samples
  printRow label stats

end SizzLeanBench.Runner
