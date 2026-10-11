import EthCLLib.TheoremVectors.ForkBinding
import EthCLSpecs.TheoremVectors.Bindings.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Gloas
import EthCLSpecs.TheoremVectors.Bindings.Heze

/-!
# `EthCLSpecs.TheoremVectors.Bindings`: the fork-binding table

The table the exe reads (`THEOREM_VECTORS_ARCHITECTURE.md` §4.2): fork tag to binding. The
pyspec format's check and the harness's per-fork selection go through
`ofTag`; a generator file names its fork's binding constant directly.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Bindings

/-- Every fork binding, in fork order. -/
def all : Array ForkBinding :=
  #[Fulu.fulu, Gloas.gloas, Heze.heze]

/-- The binding whose `tag` is `tag`. -/
def ofTag (tag : String) : Option ForkBinding :=
  all.find? fun b => b.tag == tag

end EthCLSpecs.TheoremVectors.Bindings
