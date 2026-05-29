# LeanPoseidon

A pure-Lean 4 reference implementation of the **Poseidon2** algebraic hash
permutation ([eprint 2023/323](https://eprint.iacr.org/2023/323.pdf)) over
the scalar fields of **BN254** and **BLS12-381** at width `t = 3`: the
field-arithmetic permutation, the 2-to-1 `compress` (the binary-Merkle-tree
node primitive), and a `hash` sponge over arbitrary-length input.

The shipped path is **pure Lean** — the whole permutation reduces in the
Lean kernel and under `native_decide`, with no FFI. A Rust [`zkhash`](https://crates.io/crates/zkhash)
*oracle* is used only for differential conformance testing; it is never on
the shipped path or inside a proof. Its fast linear layers are also
**formally proven** equal to the textbook dense reference (`permute =
permuteRef`).

> **Poseidon v1** is out of scope — this is **Poseidon2**. Nethermind's
> [`Poseidon.lean`](https://github.com/NethermindEth/Poseidon.lean) covers v1.

The field is a `ZMod`-style bounded-`Nat` parameterised by the modulus
(`Fp (p : Nat)`), so a new field is new data, not new code; `Bn254Fr := Fp
bn254FrModulus`. The Poseidon2 construction is namespaced under
`LeanPoseidon.Poseidon2` so a future Poseidon variant can sit beside it.

## Setup

Toolchain is pinned in the repo's [`lean-toolchain`](../../lean-toolchain)
(`leanprover/lean4:v4.29.1`); [`elan`](https://github.com/leanprover/elan)
picks it up automatically. Build the core:

```bash
lake build LeanPoseidon      # pure Lean — no mathlib, no Rust
```

To depend on it from another Lake project, add to your `lakefile.toml`
(the package is a subdirectory of the monorepo, with **no Lean
dependencies** of its own):

```toml
[[require]]
name = "LeanPoseidon"
git = "https://github.com/etheorem/etheorem"
subDir = "packages/LeanPoseidon"
rev = "<commit-or-tag>"      # pin a rev; don't track a branch
```

Two optional toolchains, each confined to one task (see **Tests**):
`cargo` (Rust) for the differential test, and `mathlib` (fetched
automatically as a prebuilt olean cache) for the equivalence proof. Neither
is needed to build or use the core.

## Usage

```lean
import LeanPoseidon
open LeanPoseidon              -- the fields: Bn254Fr, Bls12Fr, the byte codec
open LeanPoseidon.Poseidon2    -- permute, compress, hash, bn254Params, bls12Params

-- 2-to-1 compression matches the HorizenLabs zkhash BN254 t=3 reference:
example : compress (Bn254Fr.ofNat 1) (Bn254Fr.ofNat 2)
    = Bn254Fr.ofNat 0x2afac3bdc3663b71eefeecdf21b147d0ba7dd7a169a7757c05ed6bfb065bffd2 := by
  native_decide

-- the width-3 permutation on a state of field elements:
#eval (permute bn254Params #v[Bn254Fr.ofNat 0, Bn254Fr.ofNat 1, Bn254Fr.ofNat 2]).toList.map (·.val)

-- the sponge over arbitrary-length input → one field element:
#eval (hash #[Bn254Fr.ofNat 1, Bn254Fr.ofNat 2, Bn254Fr.ofNat 3]).map (·.val)

-- canonical 32-byte big-endian codec (the one home for endianness):
#eval (Bn254Fr.ofBytes? (Bn254Fr.toBytes (Bn254Fr.ofNat 42))).map (·.val)   -- some 42
```

`compress` and `hash` are over the default field `Bn254Fr`; `permute` is
generic over the coefficient type, so it runs over `Bls12Fr` too
(`permute bls12Params …`).

> Note on `hash`: the 2-to-1 `compress` is the externally-pinned,
> KAT-validated primitive (use it for Merkle / consensus-relevant work). The
> sponge `hash` uses a documented convention (no upstream Poseidon2 sponge
> exists to pin it against yet); see `Poseidon2/Sponge.lean`.

## API

All names live under `LeanPoseidon` (`open LeanPoseidon`) or its
`Poseidon2` sub-namespace (`open LeanPoseidon.Poseidon2`).

### Fields — `LeanPoseidon.Field`

| Name | Signature | Notes |
| --- | --- | --- |
| `Fp` | `structure Fp (p : Nat)` (`val : Nat`, `isLt : val < p`) | the prime-field abstraction; `Nat`/GMP-backed |
| `Bn254Fr` / `Bls12Fr` | `abbrev … := Fp bn254FrModulus` / `Fp blsFrModulus` | the two shipped scalar fields |
| arithmetic | `+ * - ^`, `0`, `1` (`Add`/`Mul`/`Sub`/`Neg`/`Zero`/`One`/`Pow`), `DecidableEq` | each `mod p` by construction |
| `Bn254Fr.ofNat` | `Nat → Bn254Fr` | reduce a literal into the field |
| `Bn254Fr.toBytes` | `Bn254Fr → ByteArray` | 32-byte **big-endian** encoding |
| `Bn254Fr.ofBytes?` | `ByteArray → Option Bn254Fr` | parse 32-byte BE; `none` if `≥ p` (never reduces) |

(`Bls12Fr.{ofNat,toBytes,ofBytes?}` are the BLS12-381 counterparts.)

### Poseidon2 — `LeanPoseidon.Poseidon2`

| Name | Signature | Notes |
| --- | --- | --- |
| `Params` | `structure Params (R : Type)` | instance data: `t`, full/partial rounds, `sboxDegree`, `roundConstants`, `intDiag` |
| `bn254Params` / `bls12Params` | `Params Bn254Fr` / `Params Bls12Fr` | the pinned `t=3` instances (generated from `zkhash`) |
| `permute` | `(par : Params R) → Vector R 3 → Vector R 3` | the shipped (fast-layer) permutation |
| `permuteRef` | `(par : Params R) → Vector R 3 → Vector R 3` | dense-matrix reference (`= permute`, proved) |
| `compress` | `Bn254Fr → Bn254Fr → Bn254Fr` | 2-to-1: `permute [a, b, 0] |>.get 0` |
| `hash` | `Array Bn254Fr → Array Bn254Fr` | sponge, rate `t−1` / capacity 1 |

### Proofs — `LeanPoseidonProofs` (sibling package, mathlib)

| Name | Statement |
| --- | --- |
| `Fp.instCommRing` | `instance [NeZero p] : CommRing (Fp p)` (transported from `ZMod p`) |
| `mulExternalFast_eq_ref` / `mulInternalFast_eq_ref` | the fast layer = the dense layer, over any `[CommRing R]` |
| `permute_eq_permuteRef` | `permute par st = permuteRef par st`, over any `[CommRing R]` |
| `permute_eq_permuteRef_bn254` / `…_bls12` | the above specialised to each field |

## Verification

The library's central optimisation is **machine-checked**: the cheap *fast*
linear layers it ships (the `O(t)` sum-plus-scaled-diagonal forms) are proven
*equal* to the textbook *dense* `t×t` matrix products, so `permute =
permuteRef`. The proof is generic over any `[CommRing R]` — covering **both**
fields at once — and lives in the sibling `LeanPoseidonProofs` package (its
only dependency, mathlib); the concrete fields plug in through a
`CommRing (Fp p)` instance transported from `ZMod p`. (`LeanPoseidonProofs`
also exports the specialisations `permute_eq_permuteRef_bn254` / `…_bls12`.)

Its axiom footprint is **clean**: `#print axioms permute_eq_permuteRef` is
exactly `[propext, Classical.choice, Quot.sound]` — mathlib's standard
axioms, with **no** FFI axiom and **no** `Lean.ofReduceBool` (the
`native_decide` compiler-trust axiom).

**Scope — what it does and does not cover.** `permute` and `permuteRef`
share the *same* S-box (`x⁵`), round-constant (ARK) additions, and round
schedule; those cancel in the equality and are **not** cross-validated by
the theorem — it would hold unchanged even if the S-box exponent or the
schedule were wrong. They are pinned instead by the conformance gates (the
[Tests](#tests) below), which carry compiler (`ofReduceBool`) / empirical
(`zkhash`) trust. So the trust splits cleanly: the linear-layer
**optimisation** is proved with no compiler trust here; the
**spec-faithfulness** of the S-box, schedule, and constants is empirical.
Together they make the shipped `permute` faithful Poseidon2.

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §9 for the theorem
statements.

## Trust boundary

| Component | Trust |
| --- | --- |
| Shipped API (`permute`, `compress`, `hash`, `Fp` arithmetic, codec) | **Kernel-reducible pure Lean.** No FFI, no extra axioms; reduces under `decide` / `native_decide`. |
| Anchor + committed KATs (`Permutation.lean`, `Kat.lean`) | `native_decide` → one `Lean.ofReduceBool` axiom each (trusts the compiler's evaluation). Pin the S-box, schedule, and round constants to the reference. |
| Rust `zkhash` oracle (`@[extern]`, `rust-oracle/`) | **Test-only.** Trusted to implement Poseidon2; validated by the differential test agreeing over 100 000 random inputs. Never on the shipped path or in a proof term. |
| Equivalence proof (`LeanPoseidonProofs`) | **Clean** (`[propext, Classical.choice, Quot.sound]` — no FFI, no `ofReduceBool`); covers the linear-layer optimisation only — see [Verification](#verification). |

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §10 for the full diagram.

## Tests

| Command | What it runs | Needs |
| --- | --- | --- |
| `lake build LeanPoseidon` | the inline anchor KATs (`permute [0,1,2]` for both fields) fire as `native_decide` gates | — |
| `just test-poseidon-vectors` | the committed `zkhash` KAT batch (`LeanPoseidonTests`) | — |
| `just fuzz-poseidon` *(`lake exe poseidon_fuzz [N]`)* | differential test: pure-Lean `permute` vs the Rust oracle over `N` seeded-random inputs per field (default 10 000; CI runs 100 000+, all agreeing) | `cargo` |
| `just test-poseidon-proofs` | the `permute = permuteRef` equivalence proof | `mathlib` (prebuilt olean cache fetched automatically) |

The core builds and the KAT/committed-KAT gates fire with **no Rust and no
mathlib**; the latter two are isolated to their respective commands.

## License

`LGPL-3.0-only`. The [`LICENSE`](../../LICENSE) at the monorepo root is the
source of truth (`licenseFiles = ["../../LICENSE"]`).

## Documentation

- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — the design (field, layers,
  permutation, FFI oracle, trust boundary, the equivalence proof).
- [`docs/PLAN.md`](docs/PLAN.md) — the staged roadmap and live status table.
