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

Scaffold (PLAN.md Stage 0b). The module layout and the design docs
are in place; the codec code lands stage by stage. Read
[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) for the binding design
and [docs/PLAN.md](docs/PLAN.md) for the staging.

## Build

From the monorepo root:

```sh
lake build LeanRlp         # the library
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
Until then the module stubs state what each file will hold.

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
