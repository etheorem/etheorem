import EthCLSpecs.Gloas.Constants

/-!
# `EthCLSpecs.Heze.Constants`: the Heze fork declaration + version values

Heze is a diff over Gloas, adding EIP-7805 (FOCIL). At alpha.11 it modifies no Gloas
container (PR #5371 reverted the bid change), so the only Heze-specific constants here
are the two `HEZE_FORK_VERSION` values. `fork Heze from Gloas` records the lineage so
`inherit` replays Gloas (and through Gloas, Fulu) declarations in the Heze namespace.
The FOCIL `DOMAIN_INCLUSION_LIST_COMMITTEE` tag lives with every other BLS domain in
`Fulu.Const` (`Const.domainInclusionListCommittee`); the FOCIL
`is_valid_inclusion_list_signature` predicate (`Heze/Focil.lean`) verifies signatures under it.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

fork Heze from Gloas

/-- `HEZE_FORK_VERSION` at the `minimal` config (`0x08000001`). -/
def hezeForkVersionMinimal : Version := ⟨#[0x08, 0x00, 0x00, 0x01], by decide⟩
/-- `HEZE_FORK_VERSION` at the `mainnet` config (`0x08000000`). -/
def hezeForkVersionMainnet : Version := ⟨#[0x08, 0x00, 0x00, 0x00], by decide⟩

end EthCLSpecs.Heze
