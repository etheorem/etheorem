import EthCLLib.TheoremVectors.Tests.Attribute
import EthCLLib.TheoremVectors.Tests.Command

/-!
# `EthCLLib.TheoremVectors.Tests`: the generator's framework-half tests

Build-gate tests for the theorem-vector generator's framework half, over a
toy fork binding. Distinct from the spec-half pins
(`EthCLSpecs.Tests.TheoremVectorsPins`), which run over real theorems.
Built as the second root of the `EthCLLibTheoremVectors` library, so
`lake build EthCLLibTheoremVectors` runs them.
-/
