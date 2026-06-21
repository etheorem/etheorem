import EthCLSpecs.Tests.WalkingSkeleton

/-!
# `EthCLSpecs.Tests`: Lean-internal spec self-tests

`#guard` / `native_decide` checks over hand-built inputs, confirming spec
behavior independently of the `pytest-xdist` conformance harness. The sources
live under `EthCLSpecs/Tests/` (namespace `EthCLSpecs.Tests.*`), built as their
own `lean_lib` and excluded from the shipped library (`SPECS_ARCHITECTURE.md`
§3.6).
-/
