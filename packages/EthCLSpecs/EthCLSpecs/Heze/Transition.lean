import EthCLSpecs.Heze.Withdrawals
import EthCLSpecs.Gloas.Transition

/-!
# `EthCLSpecs.Heze.Transition`: the inherited state-transition spine (Gloas over Heze)

EIP-7805 (FOCIL) leaves the EIP-7732 block spine unchanged. `process_slot` /
`process_epoch` / `process_slots` / `process_operations` / `process_block` /
`state_transition` (and the unchanged `process_randao` / `process_eth1_data` /
`verify_block_signature`) are all `inherit`ed over Heze state; their sub-calls late-bind
to the Heze copies from the earlier spine files.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

state_section

inherit processRandao
inherit processEth1Data
inherit verifyBlockSignature
inherit processSlot
inherit processEpoch
inherit processSlots
inherit processOperations
inherit processBlock
inherit stateTransition

end

end EthCLSpecs.Heze
