import EthCLSpecs.Heze.Inherited

/-!
# `EthCLSpecs.Heze.Containers.InclusionList`: the FOCIL inclusion list (EIP-7805, new)

The two containers EIP-7805 adds at alpha.11: an `InclusionList` (a committee member's
committed transactions for a slot) and its signed wrapper. `Transaction` and
`MAX_TRANSACTIONS_PER_PAYLOAD` are the existing Fulu/Gloas types. These are the *only*
new Heze containers; the bid is unchanged at alpha.11.
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
