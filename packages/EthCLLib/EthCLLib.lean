import EthCLLib.Internal.Capture
import EthCLLib.Spec
import EthCLLib.PySpecTests.Interface
import EthCLLib.PySpecTests.Driver

/-!
# `EthCLLib`: the consensus-spec framework and DSL

Library root and public surface. `EthCLLib` is the framework half of the
EthCLSpecs design: the capturing declaration forms, the header macros, the
effect monad, the error and tier systems, the container front-end over
SizzLean, the crypto and finite-map seams, the fork-interface typeclass, and
the generic `PySpecTests` driver. It names no fork; a separate package
(`EthCLSpecs`) implements forks against it.

The author-facing surface is gathered under `EthCLLib.Spec`, so a spec file
opens exactly one namespace (`open EthCLLib.Spec`). Internals live under
`EthCLLib.Internal`; the generic conformance driver under `EthCLLib.PySpecTests`.

See `packages/EthCLSpecs/docs/` for the three design documents this implements
and `IMPLEMENTATION_NOTES.md` there for deviations found while building.
-/
