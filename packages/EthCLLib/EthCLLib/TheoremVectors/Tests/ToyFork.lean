import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.PySpecTests.Interface

/-!
# `EthCLLib.TheoremVectors.Tests.ToyFork`: the command tests' toy binding

The `ForkBinding` the command tests run over, in its own module: the test
module imports `EthCLLib.TheoremVectors.Command`, and Lean reserves the
command syntax's atoms at import time, so a module below the import cannot
spell the binding's `presets` field. Declaring the binding here, where the
command module is not imported, keeps the field speakable.
-/

set_option autoImplicit false

namespace EthCLLib.TheoremVectors.Tests.ToyFork

/-- A toy binding over the registered toy fork
`EthCLLib.Tests.InheritanceReplay.Base` (`EthCLLib.Tests.InheritanceReplay`). -/
def toyBinding : EthCLLib.TheoremVectors.ForkBinding where
  fork := `EthCLLib.Tests.InheritanceReplay.Base
  tag := "toybase"
  presets := #[]
  hasherTag := `EthCLLib.Spec.fastHasherTag
  crypto := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType := `Nat
  blockTypes := #[]
  opens := #[]
  builders := #[]
  handlerOf := fun _ => none
  interface := fun _ => none

/-- The scratch output root the test drives share, under this package's
gitignored build tree. -/
def scratchOutDir : System.FilePath := ".lake/build/test-theorem-vectors"

end EthCLLib.TheoremVectors.Tests.ToyFork
