# LeanRlp

A Recursive-Length Prefix (RLP) codec for the Ethereum execution
layer, in Lean 4. A total encoder, a total and strict decoder, a
`deriving RlpRepr` handler for record codecs, and theorems that say
the two directions agree: round trip, canonical form, injectivity,
and size.

This package takes the role `SizzLean` has for the consensus layer:
one standalone package, a verified core, no execution-layer types in
the codec.

## Status

The package holds the item codec: `Item`, the two-arm tree; a total
encoder; a total, strict decoder on a fuel argument with a depth
bound; the canonical-form `DecodeError`; the known-answer gates
of `LeanRlpTests.Known`; and the decoder's fuel and header theorems
in `Proofs.Fuel`, gated in `Proofs.Axioms`. The nine codec theorems
of ARCHITECTURE.md §5, the schema layer, and the user surface follow
in later stages of the plan. Read
[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for the binding design
and [docs/PLAN.md](docs/PLAN.md) for the staging and the status.

## Build

From the monorepo root:

```sh
lake build LeanRlp         # the library
just rlp-build             # the library and the axiom gate
lake build LeanRlpTests    # the gates (separate lean_lib)
just rlp-test              # the same, via Just
```

Or standalone, from this directory: `lake build`.

## Usage

Once Stage 5 lands, a consumer derives a record codec:

```lean
import LeanRlp

structure Withdrawal where
  index          : UInt64
  validatorIndex : UInt64
  address        : Address
  amount         : U256
  deriving RlpRepr
```

and gets `Rlp.encode` and `Rlp.decode`, with the round trip proved.
Until Stage 5, the item layer is the surface: `Spec.encode` and
`Spec.decode` over `Item`.

## Scope

In: RLP as `ethereum-rlp` defines it, the `RlpType` schema universe,
`deriving RlpRepr`, and the codec theorems. Out: Keccak (its own
Hazmat package, `LeanHazmatKeccak`), the `Hasher` class (planned
for `EthCommon`), the hash entry point, the EIP-2718 typed
envelope, the MPT, and the hash memo.

## License

LGPL-3.0-only. The `LICENSE` file is a pinned copy of the
monorepo's, so the package stays self-contained when subtree-split
out to its own repository.
