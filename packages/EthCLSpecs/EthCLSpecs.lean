import EthCLSpecs.Forms
import EthCLSpecs.Fulu
import EthCLSpecs.Gloas
import EthCLSpecs.Heze

/-!
# `EthCLSpecs`: the Ethereum consensus-spec fork bodies

Library root. `EthCLSpecs` is the spec half of the EthCLSpecs design: the
`EthCLSpecs.Fulu` body (and, later, `EthCLSpecs.Gloas` as a diff), each
implementing the framework's `ForkInterface`, plus the `pyspec_server` runner
exe that instantiates the generic `PySpecTests` driver at a fork. Built on
`EthCLLib`; see `docs/` for the design and `docs/IMPLEMENTATION_NOTES.md` for
deviations.

Spike note (task 2.1): the `EthCLSpecs.Proofs` import is cut on this branch so
the runner can build before the proofs are repaired; Stage 3 task 3.1 restores
it. The mathlib-free theorems about the fork bodies otherwise live in
`EthCLSpecs.Proofs`, the `SizzLean.Proofs` colocation pattern (see that
module's docstring).
-/
