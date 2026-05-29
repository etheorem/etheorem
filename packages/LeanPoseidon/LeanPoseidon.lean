import LeanPoseidon.Field
import LeanPoseidon.Poseidon2.Params
import LeanPoseidon.Poseidon2.LinearLayers
import LeanPoseidon.Poseidon2.Permutation
import LeanPoseidon.Poseidon2.Compress
import LeanPoseidon.Poseidon2.Sponge

/-!
# `LeanPoseidon` — pure-Lean algebraic-hash references (library root)

A *kernel-reducible* implementation of the **Poseidon2** algebraic hash
permutation ([eprint 2023/323](https://eprint.iacr.org/2023/323.pdf)) over
the BN254 scalar field at width `t = 3`: the field-arithmetic permutation,
the 2-to-1 compression function used by binary Merkle trees, and a sponge
over arbitrary-length input. No FFI on the shipped path — the entire
permutation reduces in the Lean kernel and under `native_decide`. A Rust
`zkhash` *oracle* is used only for differential conformance testing (see
`LeanPoseidonTests`); it never sits on the shipped code path or inside a
proof term.

This is the algebraic-hash counterpart to the monorepo's pure-Lean SHA-256
reference (`LeanSha256`): a faithful, formally-checked Poseidon2 anyone can
depend on directly. It is a **standalone island** — it depends on nothing
in the monorepo and (for now) nothing depends on it. See
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the design and
[`docs/PLAN.md`](docs/PLAN.md) for the roadmap.

## Layout: shared field, per-construction namespace

The shared coefficient field lives at the top level; the Poseidon2
construction lives under a `Poseidon2` namespace, so its generically-named
pieces (`permute`, `compress`, `hash`, …) are qualified as
`Poseidon2.permute` etc. and a future Poseidon variant (or other algebraic
hash over the same field) can be added as a sibling namespace without
clashing.

* `LeanPoseidon.Field` — `Bn254Fr`, the BN254 scalar field over `Nat`,
  with the canonical 32-byte big-endian byte codec. *Field-level, shared.*
* `LeanPoseidon.Poseidon2.Params` — `Params` and the generated BN254
  `t = 3` instance `bn254Params`.
* `LeanPoseidon.Poseidon2.LinearLayers` — the fast (shipped) and dense
  (reference) external / internal linear layers.
* `LeanPoseidon.Poseidon2.Permutation` — `permute` / `permuteRef` and the
  anchor-KAT `native_decide` gate.
* `LeanPoseidon.Poseidon2.Compress` — `compress`, the 2-to-1 primitive.
* `LeanPoseidon.Poseidon2.Sponge` — `hash`, the sponge over arbitrary input.

Poseidon **v1** is *not* reimplemented here — Nethermind's
[`Poseidon.lean`](https://github.com/NethermindEth/Poseidon.lean)
covers it and stays an external reference only.
-/
