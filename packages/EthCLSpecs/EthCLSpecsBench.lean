import EthCLSpecsBench.Profile

/-!
# `EthCLSpecsBench`: the consensus container profile, library root

One tool lives here: the Stage 17d container profile, which answers
"which consensus container types dominate encode, decode, and root
cost on a real state transition?" with measurements.

```
just ethcl-profile              # the Gloas mainnet sanity/blocks case
just ethcl-profile <case-dir>   # any extracted upstream vector directory
just sizzlean-bench-diff before.tsv after.tsv
```

## Why a second bench package

`SizzLeanBench` measures the cache layer against a hand-copied
`ValidatorShape` fixture, because it cannot import `EthCLSpecs`: the
specs package depends on `SizzLean`, so that edge would close a cycle.
The profile here needs the *real* fork containers, so it sits on the
specs side of that boundary. The reverse import is fine and is used:
`EthCLSpecsBench.Profile` imports `SizzLeanBench.Runner` for the
sampling loop and the TSV row shape, so both tools emit the same
columns and one diff tool reads either.

## Layout

* `Profile.lean`: the row set, the per-type value builders, the
  anti-dead-code sinks.
* `ProfileMain.lean`: the `specs_profile` exe driver; takes raw SSZ
  paths, prints the TSV on stdout and the vector's shape on stderr.

The design of record for what the profile is for, and what its numbers
established, is
[`packages/SizzLean/docs/OPTIMISATION.md`](../SizzLean/docs/OPTIMISATION.md),
"Stage 17d".
-/
