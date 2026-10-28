import EthCLSpecs.Heze.Inherited

/-!
# `EthCLSpecs.Heze.Containers.InclusionList`: the FOCIL inclusion list (EIP-7805, new)

The two containers EIP-7805 adds: an `InclusionList` (a committee member's
committed transactions for a slot) and its signed wrapper. At v1.7.0-beta.4
`transactions` is the Gloas `Transactions`, a `ProgressiveList` of `Transaction`s
(`ProgressiveByteList`), and the list names its committee by `dependent_root`, the block
whose state fixes the slot's inclusion-list committee (alpha.12 carried the committee's own
root). The container itself stays a classic container.

The two DSL forms: `forkcontainer` declares an SSZ container in the fork namespace and
captures it for a later fork's `inherit`. Field order is declaration order, and that order
fixes both the SSZ serialization and the hash-tree-root. `signedwrapper SignedX wraps X`
expands to the two-field `forkcontainer { message : X, signature : BLSSignature }`, in that
order (`EthCLLib.Spec.Forms` documents `forkcontainer`; `EthCLSpecs.Forms` documents
`signedwrapper`).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

/-- An inclusion list (EIP-7805, `heze/beacon-chain.md:103-108`): the transactions an
inclusion-list-committee member commits to for a slot, and the shuffling dependent root its
committee was drawn under. -/
forkcontainer InclusionList where
  slot           : Slot
  validatorIndex : ValidatorIndex
  dependentRoot  : Root
  transactions   : ProgressiveList Transaction

/-- A signed inclusion list. -/
signedwrapper SignedInclusionList wraps InclusionList

end EthCLSpecs.Heze
