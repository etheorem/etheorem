import EthCLSpecs.Heze.Inherited

/-!
# `EthCLSpecs.Heze.Containers.InclusionList`: the FOCIL inclusion list (EIP-7805, new)

The two containers EIP-7805 adds at alpha.11: an `InclusionList` (a committee member's
committed transactions for a slot) and its signed wrapper. `Transaction` and
`MAX_TRANSACTIONS_PER_PAYLOAD` are the existing Fulu/Gloas types. These are the *only*
new Heze containers; the bid is unchanged at alpha.11.

The two DSL forms: `forkcontainer` declares an SSZ container in the fork namespace and
captures it for a later fork's `inherit`. Field order is declaration order, and that order
fixes both the SSZ serialization and the hash-tree-root. `signedwrapper SignedX wraps X`
expands to the two-field `forkcontainer { message : X, signature : BLSSignature }`, in that
order (`EthCLLib.Spec.Forms` documents `forkcontainer`; `EthCLSpecs.Forms` documents
`signedwrapper`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

/-- An inclusion list (EIP-7805): the transactions an inclusion-list-committee member
commits to for a slot. -/
forkcontainer InclusionList where
  slot                       : Slot
  validatorIndex             : ValidatorIndex
  inclusionListCommitteeRoot : Root
  transactions               : SSZList Transaction Const.maxTransactionsPerPayload

/-- A signed inclusion list. -/
signedwrapper SignedInclusionList wraps InclusionList

end EthCLSpecs.Heze
