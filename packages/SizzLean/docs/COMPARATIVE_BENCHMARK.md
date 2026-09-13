# SizzLean comparative benchmark

*Generated 2026-09-12 21:45:44 +07 on 12th Gen Intel(R) Core(TM) i5-12400F, 12 threads, Linux 6.19-amd64. Every number is the mean of 100 repetitions.*

## What ran

| Library | Revision | Role |
|---|---|---|
| `packages/SizzLean` | this checkout | the library under test, in two configurations |
| [`lambdaclass/libssz`](https://github.com/lambdaclass/libssz) | `36802dd1d3e3` | Rust, no Merkle cache |
| [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs) | `2600c0e75a3f` | the Python reference implementation, root memo on |

| Toolchain | Version |
|---|---|
| Lean | `leanprover/lean4:v4.29.1` |
| Rust | `rustc 1.94.0 (4a4ef493e 2026-03-02)` |
| Python | `Python 3.13.11` |

## How each side is built

Every row is an optimised native binary, or CPython for the row that is a Python library. No harness runs through an interpreter that its library would not use in production.

| Row | Build |
|---|---|
| SizzLean, both | `lake build ssz_compbench`. Lake compiles every module through C with `clang -O3 -DNDEBUG -march=native`, and the package adds `-march=native` on top of Lake's default. `SizzLeanBench` sets `precompileModules`, so the scenario code is native rather than bytecode the interpreter walks. The exe links Lean's runtime statically. |
| libssz | `cargo build --release` with `lto = "thin"` and `codegen-units = 1`, the flags libssz's own README reports its numbers under. |
| ssz-specs | CPython, no build step. The library is pure Python and ships no compiled extension. |

One asymmetry is worth naming: Rust does cross-crate inlining under thin LTO, and Lake has no cross-module equivalent. It is small. Rebuilding the libssz harness without LTO moves its first root from 9.5 ms to 9.7 ms, inside the run's noise, so it explains none of the gap between the compiled rows.

## The fixture

A Fulu `BeaconState` at the mainnet preset, 37 fields, 1024 validators, **2,894,641 bytes** on the wire. Every collection carries distinct values, so no implementation gains from a repeated subtree. The Lean harness emits the bytes; the other two decode them.

Each run has five phases:

1. **Deserialize**: wire bytes to a plain value.
2. **Wrap**: that value to whatever the library roots. Only SizzLean has this step; the other two root the decoded value directly.
3. **First root**: merkleize, from cold.
4. **Writes**: the scenario's field writes.
5. **Second root**: merkleize again.

Every repetition decodes the buffer again, so no cache survives from one repetition into the next.

Each harness runs each scenario in a loop, and every number below is the mean over those runs. The two scenarios differ only in the writes. Every other phase is the same work, so the two tables report it twice and the numbers should agree to within the run's noise.

## The control: the roots agree

All four harnesses produced the same root at every point. That is the evidence they rooted the same value, so the timings compare like with like.

| Point | Root |
|---|---|
| The fixture, before any write | `0x3e9c7c068c9837254ef108fd42d54803738e6cc8652dee382e52040a4780dde9` |
| After the one write | `0x1a7317c24af7fb12116552937c6cce1c2d790957db8c51d03b5378392efcf541` |
| After the thousand writes | `0x3707f82ea9a9c77aff893b3a98342141153c732d7567683b39b29ce5287dedcf` |

## Scenario 1: one write

Bump `slot` by one, then root again.

| Implementation | Configuration | Deserialize | Wrap | First root | Bytes to first root | Writes | Second root | Writes + second root | vs SizzLean Fast |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| SizzLean, Fast | cached, FFI SHA-256 | 163.4 ms | 874 ns | 208.0 ms | **371.4 ms** | 2.6 µs | 7.6 ms | **7.6 ms** | 1.00× |
| SizzLean, Pure | no cache, FFI SHA-256 | 164.6 ms | 871 ns | 174.5 ms | **339.1 ms** | 851 ns | 175.5 ms | **175.5 ms** | 23.0× |
| libssz | no cache | 298.3 µs | — | 9.7 ms | **10.0 ms** | 34 ns | 9.6 ms | **9.6 ms** | 1.26× |
| ssz-specs | root memo, CPython | 46.4 ms | — | 79.7 ms | **126.1 ms** | 26.4 µs | 246.5 µs | **273.0 µs** | 0.04× |

## Scenario 2: a thousand writes

Write 1000 fields, then root again. The writes are spread over four shapes: 250 validator records, 250 packed balances, 250 `block_roots` entries, and 250 `randao_mixes` entries. Spreading them matters, because a thousand writes into one list would share most of their Merkle path.

| Implementation | Configuration | Deserialize | Wrap | First root | Bytes to first root | Writes | Second root | Writes + second root | vs SizzLean Fast |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| SizzLean, Fast | cached, FFI SHA-256 | 164.0 ms | 840 ns | 207.4 ms | **371.4 ms** | 106.3 ms | 13.7 ms | **120.0 ms** | 1.00× |
| SizzLean, Pure | no cache, FFI SHA-256 | 164.2 ms | 772 ns | 172.1 ms | **336.3 ms** | 181.0 µs | 174.5 ms | **174.7 ms** | 1.46× |
| libssz | no cache | 284.9 µs | — | 9.7 ms | **10.0 ms** | 2.4 µs | 9.7 ms | **9.7 ms** | 0.08× |
| ssz-specs | root memo, CPython | 46.2 ms | — | 79.3 ms | **125.5 ms** | 2.7 ms | 57.2 ms | **59.9 ms** | 0.50× |

Splitting the decode out answers a question the first-root column alone would hide. An implementation is free to hash while it decodes, and one that did would show a heavy **Deserialize** and a cheap **First root**. **Bytes to first root** prices the whole path, so it holds wherever each library chooses to do the work.

**Second root** is where a Merkle cache shows up. A library that keeps no tree pays the first root's price again; one that keeps a tree rehashes only the paths the writes changed. Read it with **Writes** beside it: a cache that makes the second root cheap has to earn back whatever its writes cost.

## Reading the numbers

Two totals carry the report. **Bytes to first root** is what a cold start costs, from a buffer on disk to a root. **Writes + second root** is what a slot costs once the value is resident, which is the number a consensus client reads most often. The phase columns say where each total comes from.

The SizzLean pair isolates the cache and nothing else. Both rows run the same code through the same FFI SHA-256; only the constructor differs, `SSZ.FastBox` against `SSZ.PureBox`.

libssz has no Merkle cache, so its second root costs what its first one did. That is its design, and the number should be read as the price of recomputation rather than as a shortfall.

ssz-specs is the specification, written to say what the format is. It does carry a root memo, so an unchanged subtree is not rehashed.

Reproduce with `just sizzlean-comp-benchmark`. `scripts/compbench/README.md` states the method in full.
