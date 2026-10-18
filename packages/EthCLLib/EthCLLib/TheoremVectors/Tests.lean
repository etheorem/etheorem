import EthCLLib.TheoremVectors.Tests.Attribute
import EthCLLib.TheoremVectors.Tests.Command
import EthCLLib.TheoremVectors.Tests.Probe
import EthCLLib.TheoremVectors.Tests.ToyRun
import EthCLLib.TheoremVectors.Tests.BitVec
import EthCLLib.TheoremVectors.Tests.Random
import EthCLLib.TheoremVectors.Tests.Hint
import EthCLLib.TheoremVectors.Tests.Built
import EthCLLib.TheoremVectors.Tests.BuiltDrive
import EthCLLib.TheoremVectors.Tests.Pyspec
import EthCLLib.TheoremVectors.Tests.Function
import EthCLLib.TheoremVectors.Tests.Manual
import EthCLLib.TheoremVectors.Tests.Reuse
import EthCLLib.TheoremVectors.Tests.ReuseFork
import EthCLLib.TheoremVectors.Tests.Support
import EthCLLib.TheoremVectors.Tests.ClientResults

/-!
# `EthCLLib.TheoremVectors.Tests`: the generator's framework-half tests

Build-gate tests for the theorem-vector generator's framework half, over a
toy fork binding. Distinct from the spec-half pins
(`EthCLSpecs.Tests.TheoremVectorsPins`), which run over real theorems.
Built as the second root of the `EthCLLibTheoremVectors` library, so
`lake build EthCLLibTheoremVectors` runs them.
-/

set_option autoImplicit false
