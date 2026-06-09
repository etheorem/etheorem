# LeanEthCS

Ethereum Consensus Spec containers expressed against the SSZ type
system from `SizzLean`. Covers every fork from Phase 0 through
Gloas plus the preset-struct macro that stamps out minimal /
mainnet variants.

## Status

Pre-alpha. Container coverage is complete through Fulu and partial
through Gloas (full `BeaconState` and the `BlockAccessList`-bearing
`ExecutionPayload` are still deferred per the `LeanEthCS/Forks/Gloas/`
file docstrings).

## Dependencies

* `SizzLean`: the SSZ library (also pulls in `LeanSha256` and
  the FFI hasher transitively).

## Module overview

* `Primitives.lean`: named SSZ primitives shared across forks
  (`Slot`, `Epoch`, `Bytes32`, `BLSPubkey`, …).
* `Preset.lean` + `PresetStruct.lean`: preset constants (minimal /
  mainnet) and the `ssz_struct_for_presets` macro.
* `Forks/{Phase0,Altair,Bellatrix,Capella,Deneb,Electra,Fulu,Gloas}/`:
  per-fork container declarations.
* `Conformance/`: Eth-driven property tests + the `ssz_static`
  CLI runner (`Cli/Main.lean` → the `eth_ssz_vector_runner` exe; drives both
  `ssz_static` and `ssz_generic` against
  `ethereum/consensus-spec-tests`).

## Build / test

```bash
lake build LeanEthCS
# (No in-Lean property tests of its own; the build itself
# validates every `deriving SSZRepr` line in every container.)

# Conformance-test runner library (just builds the CLI machinery):
lake build LeanEthCS

# Per-test-case CLI driver (consumed by scripts/run_conformance.py
# from the repo root — drives ssz_static and ssz_generic against
# ethereum/consensus-spec-tests):
lake build eth_ssz_vector_runner
lake exe eth_ssz_vector_runner root <fork>:<type> <input.ssz>
```

## Requiring this package

TODO: publication URL.
