# Prysm client-conformance harness

The stage-10 harness (THEOREM_VECTORS_PLAN.md, stage 10). It runs the
function-format theorem vectors against Prysm v7.2.1.

## What it does

The runner walks the generator's function-format tree,
`<outDir>/formats/function/<fork>/<preset>/`, and for every record:

1. Parses the YAML (one self-contained file per vector, §13.3 of the
   theorem-vectors architecture).
2. Maps the record through `coverage.yaml` on (fork, preset,
   pyspecName). A record with no row, or a row whose status is not
   `implemented`, is a tabled skip with the row's reason. A skip never
   fails the run and pays no gate.
3. Deserializes every SSZ input of a record that runs with Prysm's SSZ
   library and checks the input's Merkle root against the file's. Every
   SSZ input pays this gate, including inputs the coverage row marks
   `ignore`.
4. Runs the mapped symbol(s) and compares per the row's `compare` role.
   A mismatch is a failure that names the record, the client's answer,
   and the expected one.
5. Prints one line per record, then the counts and the skip reasons, and
   writes `<outDir>/client-results.json`. The exit code is 1 iff at least
   one record failed. A harness-level problem, a missing tree or an
   unreadable coverage table, exits 2 before any results file is written.
   Each build overwrites `client-results.json`, so keep the output of the
   two runs apart when both matter.

## Caches

Keep the Go caches inside the worktree, the way the verified runs did.
The Prysm module cache alone is large, and `.gitignore` excludes all of
`clients/prysm/.go/`:

```sh
export GOCACHE=$PWD/.go/build
export GOMODCACHE=$PWD/.go/mod
export GOBIN=$PWD/.go/bin
```

## Presets are builds

Prysm compiles one preset per binary: the `minimal` build tag selects the
minimal fixed-vector state protos, the default build is mainnet. Run the
harness once per build:

```sh
go run . --out ../../packages/EthCLSpecs/theorem_vectors
go run -tags minimal . --out ../../packages/EthCLSpecs/theorem_vectors
```

A record of the other preset is a tabled skip: this binary cannot decode
it. A coverage row scoped to one preset is a tabled skip under the other
build too.

The wired path does both runs for you: `just client-prysm` runs the
mainnet build then the minimal build over the current output tree, and
the `client-prysm` CI job runs that recipe against the `theorem-vectors`
job's artifact.

## Self-test

`go test ./...` drives the runner over `testdata/`, a hand-written fixture
whose answer is hand-computed, and over `testdata-corrupted/`, where the
expected answer is flipped. The fixture target is `is_builder_index` with
input `2^40`, the BUILDER_INDEX_FLAG bit; the mapped composition answers
true. A third test feeds the root gate a well-formed Gloas state twice,
once with the state's true root and once with a flipped root. Run the
tests under both builds (`go test ./...` and `go test -tags minimal
./...`) so both presets get the exercise.

## Corpus status

The runs over the real corpus pass at both presets, so a run exits 0.
Every Fulu record runs and passes, including the consolidation requests:
the runner decodes each record's `ConsolidationRequest` operand and
feeds it to the mapped wrapper. The Gloas-state records are tabled
`not-implemented` skips: Prysm's `BeaconStateGloas` merkleization is
progressive (EIP-7495), the vectors are classic, and the root gate
cannot pass at this pin. etheorem/etheorem#128 tracks the Gloas switch
that closes those skips.

## The spectest suite

Prysm runs the upstream pyspec cases through its own `testing/spectest`
runners, and the recipe runs those runners unmodified over a mirrored
corpus. `just client-prysm-pyspec` does the whole run: it ensures the
pinned shallow clone, it emits the corpus with the generator exe's
`prysm-corpus` subcommand, it copies the corpus to the clone's repository
root, and it runs the two consolidation targets.

The clone lives at `clients/prysm/.go/prysm-repo`, a shallow clone of tag
`v7.2.1`. Every run checks the clone's HEAD against the pin
`fea24b41265542905352ab45fe2291d8eea010cc` and fails on a mismatch.

The `prysm-corpus` subcommand mirrors every rendered upstream case layout
under `<out>/tests/<preset>/<fork>/...`, the layout a Prysm checkout runs
its spectests from. It snappy-encodes each `.ssz` part to `.ssz_snappy`
with the generator's all-literals writer (`Snappy.lean`), and it copies
`manifest.yaml` raw. `meta.yaml` is never copied: ours carries
`bls_setting: 2` ("fake backend only"), and the suite's real BLS backend
makes `blsSettingRunnable` drop every case that declares it. Upstream's
consolidation cases carry no `meta.yaml` at the pin, and the mirror follows
them.

The targets are Prysm's `TestMinimal_Fulu_Operations_Consolidation` (with
`-tags minimal`) and `TestMainnet_Fulu_Operations_Consolidation`. Their
pass counts are pinned: 15 minimal, 3 mainnet. A wrong count names one of
two causes: a case the emitter missed, or a fetch-fired run. The clone's
`Runfile` fetches the upstream archive into `third_party/testdata` on a
path miss, and upstream holds 37 minimal consolidation cases at this pin,
so a fetch-fired minimal run counts 37.

The emitter reads the manifest the render pass wrote and never renders, so
a rendered tree is the precondition. Run the generator's `render` first.

## Files

| File | Purpose |
| --- | --- |
| `coverage.yaml` | The coverage table the runner reads. The runner treats it as data. |
| `main.go` | Flags, the summary print, `client-results.json`, the exit code. |
| `run.go` | The walk, the root gate, the table lookup, the comparisons. |
| `mapping.go` | The table-driven mapping from symbol lists to Go closures. |
| `coverage.go` | The coverage-table types and loader. |
| `vector.go` | The function-format YAML types and loader. |
| `preset.go`, `preset_minimal.go` | The build's preset name and its chain-config override. |
| `harness_test.go` | The self-test over the fixture and the corrupted copy. |
