import EthCLLib.Internal.ProofLedger
import EthCLLib.Tests.InheritanceReplay

/-!
# `EthCLLib.TheoremVectors.Tests.Attribute`: the `theorem_vectors` tag's gates

Build-gate checks for the `@[theorem_vectors]` attribute (`THEOREM_VECTORS_ARCHITECTURE.md`
§14.1): the tag rejects a declaration that is not a theorem, and a theorem
outside a registered fork's proof namespace. The positive control tags a
theorem under the toy fork `EthCLLib.Tests.InheritanceReplay.Base`, whose
proof namespace by the repository layout is `EthCLLib.Proofs.Base`.

`#guard_msgs` pins each rejection's message, so a wording change is a
reviewed diff.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs.Base

/-- The positive control: a theorem under a registered fork's proof
namespace carries the tag without a word from the elaborator. -/
@[theorem_vectors] theorem taggedInFork : 1 = 1 := rfl

end EthCLLib.Proofs.Base

namespace EthCLLib.TheoremVectors.Tests.Attribute

-- The tag on a `def` is rejected.
/-- error: `theorem_vectors` marks a theorem; `EthCLLib.TheoremVectors.Tests.Attribute.notAThm` is not one. -/
#guard_msgs (error) in
@[theorem_vectors] def notAThm : Nat := 0

-- The tag on a theorem outside every registered fork's proof namespace
-- is rejected.
/-- error: `theorem_vectors` must sit under a registered fork's proof namespace (`EthCLSpecs.Proofs.<Fork>`), and `EthCLLib.TheoremVectors.Tests.Attribute.outsideFork` sits under none. Move the theorem into its fork's proof directory, or drop the tag. -/
#guard_msgs (error) in
@[theorem_vectors] theorem outsideFork : 1 = 1 := rfl

end EthCLLib.TheoremVectors.Tests.Attribute
