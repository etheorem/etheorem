import EthCLLib.TheoremVectors.ForkBinding

/-!
# `EthCLLib.TheoremVectors.Tests.ReuseFork`: the reuse tests' toy binding

The two-preset `ForkBinding` the witness-reuse tests run over
(`THEOREM_VECTORS_ARCHITECTURE.md` §10), in its own module: the test module
imports `EthCLLib.TheoremVectors.Command`, and Lean reserves the command
syntax's atoms at import time, so a module below the import cannot spell
the binding's `presets` field. Declaring the binding here, where the
command module is not imported, keeps the field speakable
(`Tests/ToyFork.lean` carries the same note for its own binding).

The toy preset seam is the class `ReuseFork.Preset`, whose one field is the
preset constant the toy hypotheses read. The two preset constants are plain
`def`s: the binding names them, and nothing synthesizes instances.
-/

set_option autoImplicit false

namespace EthCLLib.TheoremVectors.Tests.ReuseFork

/-- The toy preset seam. The class name's last component is exactly
`Preset`, which is what the reader's `instanceKindOf` matches a binder's
class on (`Statement.lean`), so a theorem binding `[ReuseFork.Preset]`
reads as a preset seam the generator fixes per preset. -/
class Preset where
  /-- The preset constant the toy hypotheses read. -/
  bound : UInt64

/-- The minimal preset constant: `bound` is 8. The binding names the
constant, so nothing synthesizes instances; the `reducible` mark only
keeps core's class-type-definition warning quiet. -/
@[reducible] def minimalPreset : Preset := ⟨8⟩

/-- The mainnet preset constant: `bound` is 32. -/
@[reducible] def mainnetPreset : Preset := ⟨32⟩

/-- The toy two-preset binding the reuse tests run over. The `config` slot
names the same constant as `preset` because no toy theorem binds a
`[Config]` binder, so the slot is never read. -/
def reuseBinding : EthCLLib.TheoremVectors.ForkBinding where
  fork       := `EthCLLib.TheoremVectors.Tests.ReuseFork
  tag        := "toypresets"
  presets    := #[(.minimal, ⟨`EthCLLib.TheoremVectors.Tests.ReuseFork.minimalPreset,
                              `EthCLLib.TheoremVectors.Tests.ReuseFork.minimalPreset⟩),
                  (.mainnet,  ⟨`EthCLLib.TheoremVectors.Tests.ReuseFork.mainnetPreset,
                              `EthCLLib.TheoremVectors.Tests.ReuseFork.mainnetPreset⟩)]
  hasherTag  := `EthCLLib.Spec.fastHasherTag
  crypto     := `EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := `Nat
  blockTypes := #[]
  opens      := #[]
  builders   := #[]
  handlerOf  := fun _ => none
  -- §6: no reuse test pins a pyspec spelling, so the table stays empty.
  pyspecNames := #[]
  interface  := fun _ => none

/-- The scratch output root the reuse tests' command drive writes into,
under this package's gitignored build tree. -/
def scratchOutDir : System.FilePath := ".lake/build/test-theorem-vectors-reuse"

end EthCLLib.TheoremVectors.Tests.ReuseFork
