import SizzLeanBench.Profile
import SizzLeanBench.Runner

/-!
# `SizzLeanBench.ProfileMain`: `ssz_profile` exe driver

Standalone driver for the S10 cached-path phase profile.
Invoked as

```
lake exe ssz_profile > packages/SizzLean/bench/profile-<timestamp>.tsv
```

Emits the same TSV shape as `ssz_bench` so the same diff /
inspect tooling works. Kept as a separate exe because profiling
runs are ad-hoc (run once, read the breakdown, act on it) and
shouldn't bloat the regular bench wall-clock.
-/

open SizzLeanBench.Runner

def main : IO Unit := do
  printHeader
  SizzLeanBench.Profile.runAll
