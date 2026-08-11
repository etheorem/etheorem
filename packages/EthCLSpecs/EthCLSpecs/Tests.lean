import EthCLSpecs.Tests.FuluForkChoicePins
import EthCLSpecs.Tests.GloasForkChoicePins
import EthCLSpecs.Tests.HezeCommitteesPins
import EthCLSpecs.Tests.HezeForkChoicePins
import EthCLSpecs.Tests.WalkingSkeleton

/-!
# `EthCLSpecs.Tests`: Lean-internal spec self-tests

`#guard` / `native_decide` checks over hand-built inputs, confirming spec
behavior independently of the `pytest-xdist` pyspec harness. The sources
live under `EthCLSpecs/Tests/` (namespace `EthCLSpecs.Tests.*`), built as their
own `lean_lib` and excluded from the shipped library (`SPECS_ARCHITECTURE.md`
§3.6).

The `*Pins` modules are the vectorless build gates: reject branches and helper
values no conformance vector reaches, one module per fork body they pin. They
were written beside the declarations they pin and moved here, since a
`native_decide` compiled into a fork body is evaluation every consumer of that
body carries, for a check only the build gate reads.
-/
