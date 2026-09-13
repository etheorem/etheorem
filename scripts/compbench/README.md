# The SizzLean comparative benchmark

One command builds everything and prints the report:

```bash
just sizzlean-comp-benchmark
```

The driver is [`../comparative_benchmark.py`](../comparative_benchmark.py).
It compiles SizzLean's harness, downloads and compiles the two comparables at
pinned revisions, emits the shared fixture, runs the three harnesses, checks
that they agree on the roots, and writes the markdown to
`packages/SizzLean/bench/comparative-<timestamp>.md`.

That directory is session output and is gitignored. The run kept as the
reference number is copied to
[`packages/SizzLean/docs/COMPARATIVE_BENCHMARK.md`](../../packages/SizzLean/docs/COMPARATIVE_BENCHMARK.md),
verbatim and with nothing added. Move the reference by replacing that file
with a newer report; never edit one in place, because a hand-corrected number
cannot be traced back to a run.

A report says what it was measured on, so a stale or a noisy one gives itself
away. Its header names the SizzLean revision and counts any uncommitted files
under `packages/` and `scripts/`, so a report of a dirty tree cannot pass for
a report of the revision it names. The header also carries the load average at
both ends of the run: contention moves every row without touching any code, so
a busy run compares fairly row against row and not at all against a run taken
on an idle machine.

Nothing has to be installed by hand. The driver needs `lake`, `cargo`, and a
Python 3.11 or later interpreter on `PATH`; it uses `uv` when it is there and
falls back to `python3 -m venv` when it is not.

## What is compared

| Row | Library | Configuration |
|---|---|---|
| SizzLean, Fast | `packages/SizzLean` | `SSZ.FastBox`, the cached path, FFI SHA-256 |
| SizzLean, Pure | `packages/SizzLean` | `SSZ.PureBox`, no cache, FFI SHA-256 |
| libssz | [`lambdaclass/libssz`](https://github.com/lambdaclass/libssz) | `--release`, thin LTO, no Merkle cache |
| ssz-specs | [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs) | CPython, root memo on |

The two SizzLean rows differ in one thing, the constructor. Both call the
same `Box` methods through the same FFI SHA-256, so the pair prices the cache
and nothing else.

## How each side is built

Every row is an optimised native binary, or CPython for the row that is a
Python library.

| Row | Build |
|---|---|
| SizzLean, both | `lake build ssz_compbench`. Lake compiles every module through C with `clang -O3 -DNDEBUG -march=native`; the SizzLean package adds `-march=native` on top of Lake's default. `SizzLeanBench` sets `precompileModules`, so the scenario code is native, not bytecode the interpreter walks. The exe links Lean's runtime statically. |
| libssz | `cargo build --release` with `lto = "thin"` and `codegen-units = 1`, the flags libssz's own README reports its numbers under. |
| ssz-specs | CPython, no build step. The library is pure Python and ships no compiled extension. |

Rust does cross-crate inlining under thin LTO and Lake has no cross-module
equivalent. The effect is small: rebuilding the libssz harness without LTO
moves its first root from 9.5 ms to 9.7 ms, inside the run's noise.

Check the Lean flags for yourself with `lake build ssz_compbench --verbose`,
which prints every `clang` invocation.

## The fixture

A Fulu `BeaconState` at the mainnet preset: 37 fields, 1024 validators, about
2.9 MB on the wire. `SizzLeanBench.CompBench.Fixture` builds it and the
`ssz_compbench emit` subcommand writes the bytes; the Rust and the Python
harnesses decode those very bytes.

Every collection carries distinct values. A zero-filled subtree is the cheap
case: repeated chunks let a memo or a repeated pair-hash do less work than a
real state costs. Filling `block_roots`, `state_roots`, `randao_mixes`, and
`slashings` with distinct values takes that discount away from every
implementation at once.

## The scenarios

Both run five phases over the fixture, and report each phase separately.

| Phase | What it times |
|---|---|
| Deserialize | wire bytes to a plain value |
| Wrap | that value to whatever the library roots |
| First root | merkleization, from cold |
| Writes | the scenario's field writes |
| Second root | merkleization again, after the writes |

Only SizzLean has a wrapping step, the `Box` constructor. The other two root
the decoded value directly and report a zero there, so the deserialize
columns compare like with like.

The report has one table per scenario, and each carries all five phases plus
two totals. **Bytes to first root** sums the three cold phases, which settles
a question the first-root column alone would hide: an implementation is free
to hash while it decodes, and one that did would show a heavy deserialize and
a cheap first root. **Writes + second root** sums the two warm phases, which
is what a slot costs once the value is resident. The two tables repeat the
cold phases, since those are the same work either way; the numbers should
agree to within the run's noise.

`update1` writes one field, `slot`. `update1000` writes 1000 fields, spread
over four shapes: 250 validator records, 250 packed balances, 250
`block_roots` entries, and 250 `randao_mixes` entries. Spreading them
matters. A thousand writes into one list share most of their Merkle path, so
a cache would pay for one subtree and reuse it; four shapes at four depths
make the second root walk four separate paths, as a real slot does.

Each harness runs each scenario 100 times, and the report gives the mean over
those runs. `--reps` changes the count. Every repetition decodes the buffer
again, so no cache survives from one repetition into the next.

## Accounting for a root

A first root of a couple of hundred milliseconds can come from the hashing or
from everything around it, and the two call for opposite fixes. One
subcommand tells them apart:

```bash
packages/SizzLean/.lake/build/bin/ssz_compbench hashers
```

It prices both FFI SHA-256 entry points over the input merkleization feeds
them, two 32-byte children, then counts the calls one uncached root of the
fixture makes and multiplies out. The driver does not run it; it takes no
fixture and answers a question the tables raise rather than one they report.

`SizzLeanBench/CompBench/Hashers.lean` holds it, including the counting
`Hasher` instance. That instance keeps its tally in an `IO.Ref` reached
through `unsafeBaseIO`, which is the unsoundness the `Hasher` seam exists to
keep out of the library. It stays in this bench module; nothing in `SizzLean`
imports it and no proof mentions it.

## The control

All three harnesses print the roots they computed, and the driver refuses to
render a report unless every one of them agrees at every point. The three
container declarations are written by hand in three languages, so the
agreement is what shows they describe the same value.

## Layout

| Path | What it is |
|---|---|
| [`../comparative_benchmark.py`](../comparative_benchmark.py) | the driver: builds, runs, checks, renders |
| [`ssz_specs_harness.py`](ssz_specs_harness.py) | the ssz-specs containers and scenarios |
| [`libssz-harness/`](libssz-harness) | the libssz containers and scenarios, a Cargo crate |
| `packages/SizzLean/SizzLeanBench/CompBench/` | the Lean fixture and scenarios |
| `packages/SizzLean/SizzLeanBench/CompBenchMain.lean` | the `ssz_compbench` exe |

The three harnesses print the same JSON line shape, one line per repetition,
so the driver reads all three the same way:

```json
{"impl": "libssz", "scenario": "update1", "rep": 0, "deser_ns": 401721,
 "wrap_ns": 0, "root1_ns": 9650986, "update_ns": 112, "root2_ns": 8961496,
 "root1": "0x…", "root2": "0x…"}
```

## Bumping a pin

Both comparables are fetched at an exact revision, so two runs a month apart
measure the same code.

* **libssz**: change `rev` in
  [`libssz-harness/Cargo.toml`](libssz-harness/Cargo.toml) *and* `LIBSSZ_REV`
  in the driver. The driver checks that the two agree and refuses to run when
  they drift apart.
* **ssz-specs**: change `SSZ_SPECS_REV` in the driver.

A pin bump can break a harness: either library may rename a type or change a
container. Fix the harness in the same commit, and let the root check confirm
the fix.
