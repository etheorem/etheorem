import EthCLSpecs.Heze.Transition
import EthCLSpecs.Gloas.ForkChoice
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLSpecs.Heze.ForkChoice`: the inherited ePBS node-based fork choice (Gloas over Heze)

EIP-7805 adds no fork-choice step type at v1.7.0-alpha.11 (no `on_inclusion_list`, no IL
store), so Heze's tested fork choice is Gloas's. The `ForkChoiceNode` / `LatestMessage` /
`Store` `forkstruct`s and every handler are `inherit`ed over Heze state. The three node
smart constructors and the `deriving` lines are plain declarations in Gloas (not captured),
so they are restated here.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

inherit ForkChoiceNode
deriving instance BEq, Inhabited for ForkChoiceNode

inherit LatestMessage
deriving instance Inhabited for LatestMessage

inherit Store

fork_choice_section map

/-- A PENDING node at `root`: the undecided block, before either payload realisation is
committed. -/
def ForkChoiceNode.pending (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusPending }

/-- An EMPTY node at `root`: the realisation in which the block's payload is absent. -/
def ForkChoiceNode.empty (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusEmpty }

/-- A FULL node at `root`: the realisation in which the block's payload is present. -/
def ForkChoiceNode.full (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusFull }

inherit fcZeroRoot
inherit getSlotsSinceGenesis
inherit getCurrentSlot
inherit getCurrentStoreEpoch
inherit timeIntoSlotMs
inherit bpsDeadlineMs
inherit getParentPayloadStatus
inherit isParentNodeFull
inherit getAncestor
inherit isAncestor
inherit getCheckpointBlock
inherit getSupportedNode
inherit getDependentRoot
inherit isPayloadVerified
inherit voteCount
inherit payloadTimeliness
inherit payloadDataAvailability
inherit isPreviousSlotPayloadDecision
inherit shouldExtendPayload
inherit getPayloadStatusTiebreaker
inherit committeeWeight
inherit calculateCommitteeFraction
inherit getProposerScore
inherit getAttestationScore
inherit isHeadWeak
inherit isParentStrong
inherit shouldApplyProposerBoost
inherit getWeight
inherit getVotingSource
inherit filterBlockTree
inherit getFilteredBlockTree
inherit getNodeChildren
inherit getHead
inherit updateCheckpoints
inherit updateUnrealizedCheckpoints
inherit computePulledUpTip
inherit onTickPerSlot
inherit advanceStoreTime
inherit onTick
inherit recordBlockTimeliness
inherit updateProposerBoostRoot
inherit recordPtcVotes
inherit notifyPtcMessages
inherit onBlock
inherit computeTimeAtSlot
inherit verifyExecutionPayloadEnvelopeSignature
inherit verifyExecutionPayloadEnvelope
inherit onExecutionPayloadEnvelope
inherit onPayloadAttestationMessage
inherit storeTargetCheckpointState
inherit validateOnAttestation
inherit updateLatestMessages
inherit onAttestation
inherit onAttesterSlashing
inherit getForkchoiceStore

end

end EthCLSpecs.Heze
