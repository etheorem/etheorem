import EthCLSpecs.Gloas.Operations
import Std.Tactic.BVDecide

/-!
# `EthCLSpecs.Proofs.BuilderIndex`: the builder-index flag round-trip

`EthCLSpecs.Gloas.convertBuilderIndexToValidatorIndex` sets the
`BUILDER_INDEX_FLAG` bit and `EthCLSpecs.Gloas.toBuilderIndex` clears it; the
two are meant to be inverses on the builder side of the flag, the round trip
`toBuilderIndex (convertBuilderIndexToValidatorIndex bi) = bi` should hold for
every `bi : BuilderIndex`. `isBuilderIndex` should agree with the same bit
test. All three are single bitwise operations on `UInt64` (`&&&` / `|||` /
`~~~`), so the expected proof technique is the same one
`SizzLean.Proofs.UInt` uses for its LE bit-packing identities: reduce to a
fixed-width `BitVec` goal and close with `bv_decide`, no mathlib needed.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "New Gloas functionality".

TODO: state and prove the round-trip theorem.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

end EthCLSpecs.Proofs
