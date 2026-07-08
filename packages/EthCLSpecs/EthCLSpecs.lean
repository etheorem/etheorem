import EthCLSpecs.Forms
import EthCLSpecs.Fulu
import EthCLSpecs.Gloas
import EthCLSpecs.Proofs

/-!
# `EthCLSpecs`: the Ethereum consensus-spec fork bodies

Library root. `EthCLSpecs` is the spec half of the EthCLSpecs design: the
`EthCLSpecs.Fulu` body (and, later, `EthCLSpecs.Gloas` as a diff), each
implementing the framework's `ForkInterface`, plus the `pyspec_server` runner
exe that instantiates the generic `PySpecTests` driver at a fork. Built on
`EthCLLib`; see `docs/` for the design and `docs/IMPLEMENTATION_NOTES.md` for
deviations.

`EthCLSpecs.Proofs` holds the mathlib-free theorems about the fork bodies
above, the `SizzLean.Proofs` colocation pattern (see that module's docstring).
-/
