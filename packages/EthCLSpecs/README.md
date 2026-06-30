# EthCLSpecs

> **Status: experimental, single-developer; personal project, not an EF
> release. Validated against the pyspec test vectors for two
> forks (Fulu, Gloas); machine-checked proofs are future work.**

A Lean 4 implementation of the Ethereum consensus specification for the Fulu
and Gloas forks. It is executable. The SSZ container types, the full
beacon-chain state transition, the fork upgrade, and fork choice all run, and
they are checked against Ethereum's pyspec
[`consensus-spec-tests`](https://github.com/ethereum/consensus-spec-tests)
vectors.

EthCLSpecs is one half of a two-package design. The fork-agnostic framework
lives in the sibling [`EthCLLib`](../EthCLLib), which supplies the authoring
DSL, the effect monad, the SSZ container front-end over `SizzLean`, and the
pyspec driver. EthCLSpecs writes only the consensus logic on top. The
dependency chain runs from `SizzLean` (SSZ) and the `LeanHazmat` crypto
packages, through `EthCLLib`, to `EthCLSpecs`.

## What it covers

Two forks are in scope:

- **Fulu** is the base, authored whole. It carries the accumulated
  beacon-chain spec from Phase 0 through Electra, plus Fulu's PeerDAS
  data-availability additions (EIP-7594).
- **Gloas** is a diff over Fulu. It adds enshrined proposer-builder separation
  (EIP-7732): a builder registry, execution payload bids, the
  payload-timeliness committee, and a reordered block pipeline.

For each fork the library implements the SSZ containers, the state transition
(slots, blocks, epochs, and every operation), the fork upgrade, and a second
state machine for fork choice. Its containers are checked against the upstream
`ssz_static` vectors. Genesis is not yet implemented; the pinned vector set
carries no genesis cases to drive it. Validator duties, p2p networking, and the
BLS and KZG vector formats sit out of scope; those exercise primitives the
crypto packages own. The fork-agnostic `ssz_generic` wire-format vectors run in
`SizzLean`.

## Advantages

**One source, fast to run and ready to prove.** The spec body is generic over
its hasher, its boxing, and its monad. The runner picks a fast configuration:
native FFI SHA-256, a warm Merkle cache. That same source also elaborates at a
pure, kernel-reducible configuration, which keeps the door open for
machine-checked proofs in a later package. The author names neither one.

**It reads like the spec.** Conformance is behavioral, measured against
vectors. That gives the Lean rendering freedom to follow whatever reads most
naturally. Each pyspec function keeps its name in the docstring, and each
pyspec construct maps to one framework primitive. A reviewer who knows the spec
can audit the Lean line by line.

```lean
/-- `process_block` (Gloas ordering, EIP-7732). -/
forkdef processBlock (block : BeaconBlock) : StateTransition Unit := do
  processParentExecutionPayload block
  processBlockHeader block
  processWithdrawals
  processExecutionPayloadBid block.body.signedExecutionPayloadBid
  processRandao block.body
  processEth1Data block.body
  processOperations block.body
  processSyncAggregate block.body.syncAggregate
```

**A later fork is a diff over its parent.** Gloas reuses every declaration
EIP-7732 leaves untouched with a one-line `inherit`, and restates only what
changed. The mechanism replays the parent's body inside the child namespace, so
an inherited caller dispatches to the child's overrides. Late binding is
correct by construction: the child's version binds at every call site in the
inherited body.

```lean
fork Gloas from Fulu      -- declare the lineage once

inherit Validator         -- a container EIP-7732 leaves unchanged
inherit processRandao     -- a transition step it leaves unchanged
```

**Validated against the real vectors.** The full in-scope suite passes at both
the `minimal` and `mainnet` presets, for both forks, pinned to release
`v1.7.0-alpha.10`. The verdict model is honest. An out-of-range read or a crash
is a hard failure, and an unimplemented branch is a visible `xfail`. Every
passing vector reflects a real match or a faithful rejection.

## Build and test

```bash
lake build EthCLLib EthCLSpecs       # build the framework and the fork bodies
just ethcl-test                       # build everything plus the Lean self-tests

# Pyspec against upstream vectors (downloads and caches the archive):
just ethcl-pyspec-smoke          # dev subset, both forks
just ethcl-pyspec "--subset=0 --fork=gloas"   # one fork, full in-scope suite
just ethcl-pyspec-full                # the full sweep: both presets, both forks
```

CI runs the dev-subset smoke gate. The full multi-preset sweep runs on demand.

## Documentation

The design is written down under [`docs/`](docs/):

- [`SPECS_ARCHITECTURE.md`](docs/SPECS_ARCHITECTURE.md), how the fork bodies are
  organized.
- [`FRAMEWORK_ARCHITECTURE.md`](docs/FRAMEWORK_ARCHITECTURE.md), what `EthCLLib`
  provides from below.
- [`SPEC_AUTHORING_MODEL.md`](docs/SPEC_AUTHORING_MODEL.md), the author/framework
  boundary and the authoring forms.
- [`PLAN.md`](docs/PLAN.md), [`IMPLEMENTATION_NOTES.md`](docs/IMPLEMENTATION_NOTES.md),
  [`DISCREPANCIES.md`](docs/DISCREPANCIES.md), and
  [`FUTURE_WORK.md`](docs/FUTURE_WORK.md).

## Requiring this package

TODO: publication URL.
