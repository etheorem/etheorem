# LeanPoseidon

A pure-Lean 4 reference implementation of the **Poseidon2** algebraic hash
permutation ([eprint 2023/323](https://eprint.iacr.org/2023/323.pdf)) over
the scalar fields of **BN254** and **BLS12-381** at width `t = 3`: the
field-arithmetic permutation, the 2-to-1 `compress` (the binary-Merkle-tree
node primitive), and a `hash` sponge over arbitrary-length input.

The shipped path is **pure Lean**, the whole permutation reduces in the
Lean kernel and under `native_decide`, with no FFI. A Rust [`zkhash`](https://crates.io/crates/zkhash)
*oracle* is used only for differential conformance testing; it is never on
the shipped path or inside a proof. The shipped primitive is also
**machine-checked** in a sibling `mathlib` package: the permutation is a genuine
**bijection**, its fast linear layers compute the textbook dense reference
(`permute = permuteRef`), the sponge padding is injective, and the deployed
round numbers meet the paper's security floor. See [Verification](#verification).

> **Poseidon v1** is out of scope. This is **Poseidon2**. For other Lean 4
> implementations of both, see [Related work](#related-work).

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
automatically as a prebuilt olean cache) for the proofs. Neither is needed to
build or use the core.

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

### Fields: `LeanPoseidon.Field`

| Name | Signature | Notes |
| --- | --- | --- |
| `Fp` | `structure Fp (p : Nat)` (`val : Nat`, `isLt : val < p`) | the prime-field abstraction; `Nat`/GMP-backed |
| `Bn254Fr` / `Bls12Fr` | `abbrev … := Fp bn254FrModulus` / `Fp blsFrModulus` | the two shipped scalar fields |
| arithmetic | `+ * - ^`, `0`, `1` (`Add`/`Mul`/`Sub`/`Neg`/`Zero`/`One`/`Pow`), `DecidableEq` | each `mod p` by construction |
| `Bn254Fr.ofNat` | `Nat → Bn254Fr` | reduce a literal into the field |
| `Bn254Fr.toBytes` | `Bn254Fr → ByteArray` | 32-byte **big-endian** encoding |
| `Bn254Fr.ofBytes?` | `ByteArray → Option Bn254Fr` | parse 32-byte BE; `none` if `≥ p` (never reduces) |

(`Bls12Fr.{ofNat,toBytes,ofBytes?}` are the BLS12-381 counterparts.)

### Poseidon2: `LeanPoseidon.Poseidon2`

| Name | Signature | Notes |
| --- | --- | --- |
| `Params` | `structure Params (R : Type)` | instance data: `t`, full/partial rounds, `sboxDegree`, `roundConstants`, `intDiag` |
| `bn254Params` / `bls12Params` | `Params Bn254Fr` / `Params Bls12Fr` | the pinned `t=3` instances (generated from `zkhash`) |
| `permute` | `(par : Params R) → Vector R 3 → Vector R 3` | the shipped (fast-layer) permutation |
| `permuteRef` | `(par : Params R) → Vector R 3 → Vector R 3` | dense-matrix reference (`= permute`, proved) |
| `compress` | `Bn254Fr → Bn254Fr → Bn254Fr` | 2-to-1: `permute [a, b, 0] |>.get 0` |
| `hash` | `Array Bn254Fr → Array Bn254Fr` | sponge, rate `t−1` / capacity 1 |

### Proofs: `LeanPoseidonProofs` (sibling package, mathlib)

| Name | Statement |
| --- | --- |
| `Fp.instCommRing` | `instance [NeZero p] : CommRing (Fp p)` (transported from `ZMod p`) |
| `Fp.instField` | `instance [Fact (Nat.Prime p)] : Field (Fp p)` (reuses the `CommRing` parent, no diamond) |
| `mulExternalFast_eq_ref` / `mulInternalFast_eq_ref` | the fast layer = the dense layer, over any `[CommRing R]` |
| `permute_eq_permuteRef` (+ `…_bn254` / `…_bls12`) | `permute par st = permuteRef par st`, over any `[CommRing R]`, then each field |
| `permute_bijective_bn254` / `…_bls12` | `Function.Bijective (permute …)`, the shipped permutation is a genuine bijection |
| `compress_not_injective` | `¬ Function.Injective (fun (a, b) ↦ compress a b)`, the 2-to-1 node has collisions (pigeonhole) |
| `pad_injective` | `Function.Injective pad`, the sponge padding is injective |
| `meetsFloor` (`#guard`s) | the deployed `R_F = 8`, `R_P = 56` meet the reference script's minimum-round bounds (`RoundCount.lean`) |

The two standardised moduli are assumed prime via cited axioms
(`bn254FrModulus_prime` / `blsFrModulus_prime`, `Primality.lean`). See the
[Trust boundary](#trust-boundary).

## Verification

Beyond the conformance gates ([Tests](#tests)), the shipped primitive is
**machine-checked**. The proofs establish that:

- **`permute` is a genuine bijection**, it really is a *permutation*
  (`permute_bijective_bn254` / `permute_bijective_bls12`);
- **the fast linear layers compute the textbook dense matrices**, so
  `permute = permuteRef` (the paper's central optimisation);
- **the sponge padding is injective** (`pad_injective`);
- **`compress` is not collision-resistant on its own**. The 2-to-1 node has
  collisions, so a Merkle tree's security must come from pre-hashing its leaves,
  not from `compress` alone (`compress_not_injective`);
- **the deployed round numbers meet the paper's minimum-round bounds**
  (`RoundCount.lean`).

Run them all with:

```bash
just poseidon-proofs
```

**Where the proofs live.** They are *not* part of the `LeanPoseidon` package,
they sit beside it in the monorepo
[`etheorem/etheorem`](https://github.com/etheorem/etheorem), under
`packages/LeanPoseidonProofs`. They are isolated there because they are the
monorepo's only `mathlib` dependency (a heavy one), so the core library and
everything else stay `mathlib`-free and fast. **If you depend on `LeanPoseidon`
as a standalone / mirrored package, the proofs are not bundled with it**. Clone
the monorepo to build them. (Rationale: [§11 of `ARCHITECTURE.md`](docs/ARCHITECTURE.md).)

For these proofs' axiom footprint and the precise boundary of what they do,
and do not, establish, see [Trust boundary](#trust-boundary).

## Trust boundary

| Component | Trust |
| --- | --- |
| Shipped API (`permute`, `compress`, `hash`, `Fp` arithmetic, codec) | **Kernel-reducible pure Lean.** No FFI, no extra axioms; reduces under `decide` / `native_decide`. |
| Anchor + committed KATs (`Permutation.lean`, `Kat.lean`) | `native_decide` → one `Lean.ofReduceBool` axiom each (trusts the compiler's evaluation). Pin the S-box, schedule, and round constants to the reference. |
| Rust `zkhash` oracle (`@[extern]`, `rust-oracle/`) | **Test-only.** Trusted to implement Poseidon2; validated by the differential test agreeing over 100 000 random inputs. Never on the shipped path or in a proof term. |
| Proofs (`LeanPoseidonProofs`) | mathlib-only, **no FFI, no `ofReduceBool`**. `permute = permuteRef`, the generic lemmas, and `pad_injective` are `[propext, Classical.choice, Quot.sound]`; the concrete `permute_bijective_…` / `compress_not_injective` add one **cited, dischargeable** primality axiom (`…Modulus_prime`), swappable for a kernel-checked Pratt/Lucas certificate. |

**What the proofs do *not* establish** (pinned elsewhere, by design):

- **That the shipped constants and schedule are the canonical Poseidon2 ones.**
  The proofs are *structure-level*. They hold for any coprime S-box exponent
  and any round constants, so they do not match `permute` against an external
  reference. That faithfulness is pinned **empirically**, by the anchor /
  committed KATs and the `zkhash` differential test (the rows above). The two
  together, structurally-verified primitive plus empirically-pinned constants,
  are what make the shipped `permute` faithful Poseidon2.
- **Collision / preimage resistance.** As for any keyless hash, this is a
  cryptographic *assumption* (assessed empirically, e.g. by the EF Poseidon
  Cryptanalysis Initiative), **not** a theorem; nothing here claims it.
  `compress_not_injective` is the opposite, a *proof* that the bare 2-to-1
  compression has collisions.

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) §10 for the full diagram.

## Related work

The contribution here is the **mechanisation**. Bijectivity of
the bare Poseidon2 permutation is a paper exercise: the S-box `x⁵` is
bijective on prime fields where `gcd(5, p − 1) = 1`, the linear layers are
invertible by determinant, and composition preserves bijectivity. What
LeanPoseidon adds is a kernel-checked Lean 4 artefact that pins down *which*
permutation, *which* field instances, and what depends on what. The
round-constants / schedule gap is delineated honestly by differential testing
rather than hidden.

Neighbouring Lean 4 implementations:

- [`NethermindEth/Poseidon.lean`](https://github.com/NethermindEth/Poseidon.lean):
  Poseidon (v1) and Poseidon2; the Poseidon2 instances target **BabyBear**
  at widths 16 and 24, test-validated.
- [`manuelpuebla/amo-lean`](https://github.com/manuelpuebla/amo-lean):
  Poseidon2 over BN254 at `t = 3`; its Poseidon2 proofs carry 12 `sorry`s
  (as self-reported in its README).

## Tests

| Command | What it runs | Needs |
| --- | --- | --- |
| `lake build LeanPoseidon` | the inline anchor KATs (`permute [0,1,2]` for both fields) fire as `native_decide` gates | — |
| `just poseidon-vectors` | the committed `zkhash` KAT batch (`LeanPoseidonTests`) | — |
| `just poseidon-fuzz` *(`lake exe poseidon_fuzz [N]`)* | differential test: pure-Lean `permute` vs the Rust oracle over `N` seeded-random inputs per field (default 10 000; CI runs 100 000+, all agreeing) | `cargo` |
| `just poseidon-proofs` | all `LeanPoseidonProofs` proofs: `permute = permuteRef`, `permute` is a bijection, `pad` injective, `compress` non-injective, and the round-count `#guard`s | `mathlib` (prebuilt olean cache fetched automatically) |

The core builds and the KAT/committed-KAT gates fire with **no Rust and no
mathlib**; the latter two are isolated to their respective commands.

## License

`LGPL-3.0-only`. The [`LICENSE`](../../LICENSE) at the monorepo root is the
source of truth (`licenseFiles = ["../../LICENSE"]`).

## Documentation

- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md): the design (field, layers,
  permutation, FFI oracle, trust boundary, the equivalence and
  structural-correctness proofs).
- [`docs/PLAN.md`](docs/PLAN.md): the staged plan and live status table.
