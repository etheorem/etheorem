import SizzLeanBench.MultiState

/-!
# `SizzLeanBench.MultiStateMain`: `ssz_multistate` exe driver

Runs the Stage 17c multi-state heap bench and prints its TSV to
stdout. Invoked as

```
lake exe ssz_multistate > bench/multistate-<timestamp>.tsv
```

(`just sizzlean-bench-multistate` wraps the redirection.) Kept out
of `ssz_bench` so the scenarios TSV, the guard that the default
path is unchanged, keeps its row set.
-/

def main : IO Unit :=
  SizzLeanBench.MultiState.runAll
