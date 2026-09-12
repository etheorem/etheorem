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

Both run four phases over the fixture, and report each phase separately.

| Phase | What it times |
|---|---|
| Load | wire bytes to a value the library can root |
| First root | merkleization, from cold |
| Writes | the scenario's field writes |
| Second root | merkleization again, after the writes |

`update1` writes one field, `slot`. `update1000` writes 1000 fields, spread
over four shapes: 250 validator records, 250 packed balances, 250
`block_roots` entries, and 250 `randao_mixes` entries. Spreading them
matters. A thousand writes into one list share most of their Merkle path, so
a cache would pay for one subtree and reuse it; four shapes at four depths
make the second root walk four separate paths, as a real slot does.

Every repetition decodes the buffer again, so no cache survives from one
repetition into the next.

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
{"impl": "libssz", "scenario": "update1", "rep": 0, "load_ns": 401721,
 "root1_ns": 9650986, "update_ns": 112, "root2_ns": 8961496,
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
