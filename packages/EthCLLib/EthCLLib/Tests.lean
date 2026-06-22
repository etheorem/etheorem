import EthCLLib.Tests.InheritanceReplay
import EthCLLib.Tests.ReplayChild
import EthCLLib.Tests.CryptoBackendSpike
import EthCLLib.Tests.ContainerForm
import EthCLLib.Tests.FrameworkUtils
import EthCLLib.Tests.PreambleSection

/-!
# `EthCLLib.Tests`: framework self-tests

Lean-internal unit tests for what the framework owns, written as `#guard` /
`native_decide` / `example` so they are checked at build (`lake build
EthCLLibTests`). Distinct from the `pytest-xdist` conformance harness, which runs
the upstream vectors. See `FRAMEWORK_ARCHITECTURE.md` §14.

The tests live under `EthCLLib/Tests/` (namespace `EthCLLib.Tests.*`), built as
their own `lean_lib` and excluded from the shipped `EthCLLib` library, which
globs only its own root (`SPECS_ARCHITECTURE.md` §3.6).
-/
