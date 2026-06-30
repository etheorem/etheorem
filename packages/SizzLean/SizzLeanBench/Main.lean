import SizzLeanBench

/-!
# `SizzLeanBench.Main`: `ssz_bench` exe driver

Runs every scenario's `runAll` in declaration order and emits
the TSV header once at the top. Invoked as

```
lake exe ssz_bench > bench/<timestamp>.tsv
```

(`just sizzlean-bench` wraps the redirection and runs the compiled
binary directly.) Stdout is the bench output; stderr is
reserved for any setup-side errors a bench shot can't suppress.

The scenarios run in numbered order: S1–S6 (small tier;
`Validator` + `ValidatorSet16`) emit the quick rows first,
then S7–S12 (large/huge tier; `ValidatorSet256` +
`ValidatorSet4096`) emit the production-shape rows with
longer per-row durations. See `SizzLeanBench.lean`'s module
doc for the full row inventory.
-/

open SizzLeanBench.Runner

def main : IO Unit := do
  printHeader
  -- Small tier (S1–S3): Validator + ValidatorSet16
  SizzLeanBench.Scenarios.ColdRoot.runAll
  SizzLeanBench.Scenarios.BatchedWrites.runAll
  SizzLeanBench.Scenarios.BlockProcessing.runAll
  -- Large tier (S4–S6): ValidatorSet256
  SizzLeanBench.Scenarios.ColdRootLarge.runAll
  SizzLeanBench.Scenarios.BatchedWritesLarge.runAll
  SizzLeanBench.Scenarios.BlockProcessingLarge.runAll
  -- Realistic tier (S7): Fulu BeaconState, mainnet preset
  SizzLeanBench.Scenarios.FuluStateTransition.runAll
