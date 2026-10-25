import EthCLSpecs.Proofs.Heze.Accountable
import EthCLSpecs.Proofs.Heze.AttestationScore
import EthCLSpecs.Proofs.Heze.AttesterSlashing
import EthCLSpecs.Proofs.Heze.BalanceMoves
import EthCLSpecs.Proofs.Heze.BlockChain
import EthCLSpecs.Proofs.Heze.BlockRoot
import EthCLSpecs.Proofs.Heze.BlockRootsRun
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.ChainAgree
import EthCLSpecs.Proofs.Heze.CheckpointFrame
import EthCLSpecs.Proofs.Heze.CheckpointInvariants
import EthCLSpecs.Proofs.Heze.CheckpointOrd
import EthCLSpecs.Proofs.Heze.Churn
import EthCLSpecs.Proofs.Heze.ClockedTrace
import EthCLSpecs.Proofs.Heze.CommitteeFrame
import EthCLSpecs.Proofs.Heze.Committees
import EthCLSpecs.Proofs.Heze.DriftAttest
import EthCLSpecs.Proofs.Heze.DriftBlock
import EthCLSpecs.Proofs.Heze.DriftBlockStep
import EthCLSpecs.Proofs.Heze.DriftBound
import EthCLSpecs.Proofs.Heze.DriftChurn
import EthCLSpecs.Proofs.Heze.DriftCons
import EthCLSpecs.Proofs.Heze.DriftDefs
import EthCLSpecs.Proofs.Heze.DriftDeposits
import EthCLSpecs.Proofs.Heze.DriftEpoch
import EthCLSpecs.Proofs.Heze.DriftEpochStep
import EthCLSpecs.Proofs.Heze.DriftExit
import EthCLSpecs.Proofs.Heze.DriftInv
import EthCLSpecs.Proofs.Heze.DriftMath
import EthCLSpecs.Proofs.Heze.DriftOps
import EthCLSpecs.Proofs.Heze.DriftParent
import EthCLSpecs.Proofs.Heze.DriftRequests
import EthCLSpecs.Proofs.Heze.DriftRewards
import EthCLSpecs.Proofs.Heze.DriftRun
import EthCLSpecs.Proofs.Heze.DriftSlash
import EthCLSpecs.Proofs.Heze.DriftSync
import EthCLSpecs.Proofs.Heze.DriftTotal
import EthCLSpecs.Proofs.Heze.DriftWithdraw
import EthCLSpecs.Proofs.Heze.EbUpdates
import EthCLSpecs.Proofs.Heze.EconFrame
import EthCLSpecs.Proofs.Heze.EmptyTarget
import EthCLSpecs.Proofs.Heze.Equivocators
import EthCLSpecs.Proofs.Heze.FFGRefines
import EthCLSpecs.Proofs.Heze.FinalityCheck
import EthCLSpecs.Proofs.Heze.FinalityLock
import EthCLSpecs.Proofs.Heze.FinalizationLiveness
import EthCLSpecs.Proofs.Heze.FinalizationProgress
import EthCLSpecs.Proofs.Heze.ForkPoint
import EthCLSpecs.Proofs.Heze.FullSupport
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLSpecs.Proofs.Heze.HandlerFrames
import EthCLSpecs.Proofs.Heze.HeaderFrame
import EthCLSpecs.Proofs.Heze.HeadAvoidsFull
import EthCLSpecs.Proofs.Heze.HeadBelowJustified
import EthCLSpecs.Proofs.Heze.HonestDuties
import EthCLSpecs.Proofs.Heze.HonestHead
import EthCLSpecs.Proofs.Heze.HonestVoter
import EthCLSpecs.Proofs.Heze.HonestVoteSide
import EthCLSpecs.Proofs.Heze.ILStoreOrder
import EthCLSpecs.Proofs.Heze.InclusionDichotomy
import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLSpecs.Proofs.Heze.JustificationAndFinalization
import EthCLSpecs.Proofs.Heze.JustificationBits
import EthCLSpecs.Proofs.Heze.KeepsUncached
import EthCLSpecs.Proofs.Heze.KeyFrame
import EthCLSpecs.Proofs.Heze.KeepsUncached.Block
import EthCLSpecs.Proofs.Heze.KeepsUncached.Epoch
import EthCLSpecs.Proofs.Heze.KeepsUncached.Payload
import EthCLSpecs.Proofs.Heze.KeepsUncached.Slots
import EthCLSpecs.Proofs.Heze.KeepsUncached.Withdrawals
import EthCLSpecs.Proofs.Heze.ListLengths
import EthCLSpecs.Proofs.Heze.StorePure
import EthCLSpecs.Proofs.Heze.LatestMessages
import EthCLSpecs.Proofs.Heze.NodeTrace
import EthCLSpecs.Proofs.Heze.NodeViews
import EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope
import EthCLSpecs.Proofs.Heze.OnInclusionList
import EthCLSpecs.Proofs.Heze.OnTickPerSlot
import EthCLSpecs.Proofs.Heze.ParentPayloadEmpty
import EthCLSpecs.Proofs.Heze.Participation
import EthCLSpecs.Proofs.Heze.ParticipationFrame
import EthCLSpecs.Proofs.Heze.ParticipationKeep
import EthCLSpecs.Proofs.Heze.ParticipationRotate
import EthCLSpecs.Proofs.Heze.PayloadRace
import EthCLSpecs.Proofs.Heze.PayloadRaceBounds
import EthCLSpecs.Proofs.Heze.PayloadRaceCount
import EthCLSpecs.Proofs.Heze.PayloadRaceDecision
import EthCLSpecs.Proofs.Heze.PayloadRaceExec
import EthCLSpecs.Proofs.Heze.PayloadRaceRefines
import EthCLSpecs.Proofs.Heze.PayloadRaceWalk
import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.PaymentCarried
import EthCLSpecs.Proofs.Heze.PaymentFrame
import EthCLSpecs.Proofs.Heze.PaymentWriters
import EthCLSpecs.Proofs.Heze.ProposerScore
import EthCLSpecs.Proofs.Heze.RaceCheck
import EthCLSpecs.Proofs.Heze.RaceLong
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.Heze.RefDrift
import EthCLSpecs.Proofs.Heze.RootFrames
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Proofs.Heze.RunVotes
import EthCLSpecs.Proofs.Heze.RunWeighs
import EthCLSpecs.Proofs.Heze.ShouldExtendPayload
import EthCLSpecs.Proofs.Heze.Shuffle
import EthCLSpecs.Proofs.Heze.SlotsIncrease
import EthCLSpecs.Proofs.Heze.StakeDrift
import EthCLSpecs.Proofs.Heze.StoreChainState
import EthCLSpecs.Proofs.Heze.StoreClock
import EthCLSpecs.Proofs.Heze.StoreFinality
import EthCLSpecs.Proofs.Heze.SyncFrame
import EthCLSpecs.Proofs.Heze.TargetStake
import EthCLSpecs.Proofs.Heze.Time
import EthCLSpecs.Proofs.Heze.TraceFacts
import EthCLSpecs.Proofs.Heze.TraceRun
import EthCLSpecs.Proofs.Heze.VoteValid

/-!
# `EthCLSpecs.Proofs.Heze`: the Heze fork's theorems (index)

Every theorem about an `EthCLSpecs.Heze` declaration, one module per subject.
The directory mirrors `EthCLSpecs/Heze/`, for the reason `Proofs/Gloas.lean`
states: a fork elaborates its own constant for every declaration, inherited ones
included, so a theorem here is about the Heze constant and about no other fork's.
`shouldExtendPayload` is the case that shows it. Gloas declares it and Heze
overrides it with the FOCIL gate, so the Gloas theorems say nothing about the
Heze constant.

`PayloadRace` and `PayloadRaceBounds` are the exception. They state an abstract model of
the weight race at one block and no theorem about a Heze declaration.
`PayloadRaceRefines` ties the model to `getAttestationScore`, and `PayloadRaceWalk` ties it
to the `getHead` walk. `PayloadRaceExec` states the result on the executable spec, and
`PayloadRaceDecision` joins it to tier T1.

Every declaration here sits in the `EthCLSpecs.Proofs.Heze` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Heze.Accountable`: accountable safety for two honest nodes
  (`honestNodes_accountable`). The justified checkpoint of one node conflicts with the
  finalized checkpoint of another, under `getCheckpointBlock`. Then a root collision exists, or
  there is `SlashingEvidence`. The evidence is pairs of indexed attestations that pass the
  slashing test, with one attestation valid on a state of each chain. The common validators of
  the pairs hold a third of the stake of the fork point, less `5/3` of the measured drift.
  `SlashingEvidence.accepted` states that `processAttesterSlashing` accepts such a pair.
* `EthCLSpecs.Proofs.Heze.AttestationScore`: the Heze `getAttestationScore` is the `Nat` sum
  of the effective balances of the counted active indices (`getAttestationScore_run_ok`).
* `EthCLSpecs.Proofs.Heze.AttesterSlashing`: the slashing test of two attestation data is a
  double vote or a surround vote (`isSlashableAttestationData_iff`). Two different data with
  one target epoch are a double vote, or their roots collide
  (`isSlashableAttestationData_of_ne`). When the data are slashable, both indexed
  attestations are valid, and a validator of both lists is slashable, `processAttesterSlashing`
  does not reject with an assert (`processAttesterSlashing_run_not_assert`, under
  `QsortMem`). Each of the first three asserts rejects when its condition fails.
* `EthCLSpecs.Proofs.Heze.BlockChain`: the invariant `CkptInv` along a node trace from the
  anchor store (`NodeTrace.ckptInv`), or a root collision. Each stored state ends a chain
  run from the anchor state over the blocks on the parent links of its root
  (`AncestorPath`), and the run ends at the block of the state (`EndsAtBlock`). Each of the
  four store checkpoints is the anchor checkpoint, or comes from such a state or its pull-up
  (`CheckpointSource`). In both pairs, the finalized epoch
  is at most the justified epoch. A successful `onBlock` run passed its two acceptance
  asserts (`onBlock_run_ok_asserts`). a block root is the root of its header
  (`htr_eq_htr_headerOf`), under the hypothesis that every `combine` returns 32 bytes.
  The root of a 32-byte vector is its bytes (`hashTreeRoot_bytes32`).
* `EthCLSpecs.Proofs.Heze.BlockRootsRun`: along a chain run of validated blocks, `blockRoots`
  holds the root of the last block at or before each slot that it covers, or the root that
  the anchor state records (`rootAtSlot`, `ChainRun.rootsInv`). `get_block_root_at_slot`
  reads that root on a state of the run, and on the state after the next `processSlot`
  (`RootsInv.read`, `RootsInv.read_slotWrite`).
* `EthCLSpecs.Proofs.Heze.BuilderPendingPayments`: the Heze port of the epoch
  substep for builder payments (`processBuilderPendingPayments_run`), and the
  per-entry quorum condition (`mem_qualifyingPaymentIndices_iff`), proved with
  `HezeRun`. When the payment of a bid is carried to the substep
  (`BidPaymentCarried`), the substep appends the entry of the bid if and only if the
  entry reaches the quorum (`processBuilderPendingPayments_run_bid`).
* `EthCLSpecs.Proofs.Heze.CensorshipCost`: three facts about a block with a recorded
  `false` inclusion-list answer (`unsatisfiedPayload_cost`). The `getHead` loop
  continues from EMPTY at the block. A child on EMPTY, with the empty parent requests,
  does not settle the bid. At the epoch substep, the entry of the bid is appended if and
  only if it reaches the quorum. `unsatisfiedPayload_cost_of_run` states the three facts
  with the third one over the chain from the block to the substep.
* `EthCLSpecs.Proofs.Heze.ChainAgree`: take two runs whose blocks lie on ancestor paths. Their
  chains agree below a shared root, or a root collision exists (`ffgChain_agree`). The walk of
  `getCheckpointBlock` along an ancestor path returns the root after the path blocks at or
  before the epoch start (`AncestorPath.checkpointBlock`). So a checkpoint that conflicts with a
  justified checkpoint of a chain is not on that chain (`conflicting_not_onChain`).
* `EthCLSpecs.Proofs.Heze.CheckpointFrame`: every function of a slot step and a block
  step, other than `processJustificationAndFinalization`, keeps the three state checkpoints,
  the justification bits, and the slot (`processBlock_frame_ord`,
  `processEpochAfterJF_frame_ord`).
* `EthCLSpecs.Proofs.Heze.CheckpointInvariants`: a chain run keeps the checkpoint order of
  a state (`StateCkptOrd`, `ChainRun.stateCkptOrd`), when no slot increment wraps. On an
  ordered state, `processJustificationAndFinalization` writes a finalized epoch at most
  the current justified epoch (`processJustificationAndFinalization_run_fin_le`). A handler
  event, and a trace, raise no epoch of the four store checkpoints
  (`HandlerEvent.run_ckptGrows`, `NodeTrace.ckptGrows`).
* `EthCLSpecs.Proofs.Heze.CheckpointOrd`: the derived order on `Checkpoint` is transitive
  and returns `.eq` only on equal checkpoints (`instTransOrdCheckpoint`,
  `instLawfulEqOrdCheckpoint`), so `treeMap` meets the map laws at `Checkpoint`.
* `EthCLSpecs.Proofs.Heze.Churn`: the inherited `reserveChurn`, which takes the Gloas proof
  terms, and run theorems for the two inherited churn callers.
* `EthCLSpecs.Proofs.Heze.ClockedTrace`: a node trace on the wall clock
  (`ClockedTrace`). It states the current slot and the time into the slot in terms of the
  wall time (`slotStartMs_le_of_getCurrentSlot`, `slot_window_of_getCurrentSlot`,
  `timeIntoSlotMs_lt_of_window`). A state at a root comes from an `onBlock` event that
  passed its clock check
  (`NodeTrace.blockStates_origin`, `onBlock_run_ok_currentSlot`).
* `EthCLSpecs.Proofs.Heze.Committees`: the inherited committee functions
  partition the active set per epoch (`getBeaconCommittee_partition`).
* `EthCLSpecs.Proofs.Heze.CommitteeFrame`: two states with one activity and one seed mix at
  an epoch have one set of attesting indices there (`getAttestingIndices_eq_of_comView`). A
  block keeps both up to and inside its attestation loop. So it sets the target flag of each
  attesting index of its attestations, as its start state computes them
  (`processBlock_sets_flag`).
* The stake-drift modules, which `StakeDrift` assembles. `DriftMath` and `DriftDefs` hold
  the arithmetic and the reads (`absDiff`, `EbTrack`, `moveN`). `DriftBound` bounds the drift
  by facts at the end of a run (`drift_le_of_endFacts`). `DriftInv` states the invariant
  `RunInv` of a run and gives those facts (`RunInv.endFacts`). `DriftTotal` names the reads
  of the total active balance (`AcKeep`), and `EconFrame` the functions that write no read
  of the invariant. The writers each keep `RunInv` at a stated cost: `BalanceMoves` for one
  balance write, `DriftExit`, `DriftSlash` and `DriftOps` for exits and slashings,
  `DriftChurn` for the churn arithmetic, `DriftCons`, `DriftRequests` and `DriftParent` for
  the execution requests, `DriftAttest` and `DriftSync` for the rewards of a block,
  `DriftWithdraw` for the withdrawals, `DriftBlock` and `DriftBlockStep` for a block,
  `DriftEpoch`, `DriftRewards`, `DriftDeposits` and `EbUpdates` for the epoch writers, and
  `DriftEpochStep` and `DriftRun` for an epoch, a slot step, and the run (`runAcc_run`).
* `EthCLSpecs.Proofs.Heze.Equivocators`: only `onAttesterSlashing` adds to
  `equivocatingIndices`, and only an index that both attestations carry and whose
  slashing passes its checks (`onAttesterSlashing_run_ok`, `onAttesterSlashing_new_member`).
  Along a trace from the anchor, an index that no slashing of the trace marks is never in
  the set (`honest_not_equivocating`).
* `EthCLSpecs.Proofs.Heze.EmptyTarget`: two nodes above one node lie on one chain
  (`NodeBelow.comparable`). Under `SlotsIncrease`, the block of a node is no later than the
  block of a node below it (`NodeBelow.slot_le`). The checkpoint block of a head below
  `empty r` is a stored block (`checkpointBlock_block`). When that block is later than `rb`,
  it is on the EMPTY side of `r` (`checkpointBlock_emptySide`).
* `EthCLSpecs.Proofs.Heze.FFGRefines`: a chain run refines Casper FFG (`chain_refines`). The
  abstract chain of the run (`ffgChain`) has the placed votes of the run, the checkpoint roots
  of the run, and the stake and the total of each weigh state (`ChainMatches`). At an epoch
  with no weigh state, the end state of the run gives the stake and the total. The two
  justified checkpoints at the end are justified in the chain. The finalized checkpoint is
  finalized there, or it is a base checkpoint. The same holds for the pull-up of the end state
  (`chain_refines_pullup`).
* `EthCLSpecs.Proofs.Heze.FinalityCheck`: the premises of `FinalitySetting` and
  `SlashingEvidence` as computations. The store runs of a store of chain blocks follow the chain
  (`ChainStore.state_mem`). So checks over the states and the votes of the chain give
  `StoreTotals`, the stake bound, and the honest votes. A check over the epochs up to the one
  after the head block gives `early` (`early_of_check`). `HonestChain.of_check` and
  `SlashingEvidence.of_check` check the chain premises.
* `EthCLSpecs.Proofs.Heze.FinalityLock`: under `SlotsIncrease`, the two sides of a block `r`
  are disjoint (`below_emptySide_not_full`). A checkpoint block on the EMPTY side puts the
  start of its walk on the EMPTY side (`emptySide_of_checkpointBlock`). Take an honest node
  whose finalized block is on the EMPTY side of `r`. Each later head is not below `full r`,
  or a root collision exists, or the later justified checkpoint conflicts with that
  finalized checkpoint (`honestNode_finality_lock`).
* `EthCLSpecs.Proofs.Heze.FinalizationLiveness`: the censored payload stays off the honest
  heads (`censored_payload_final`). The window runs from `N + 1` to the first slot of
  `E₁ + 4` (`FinalitySetting`). A justified block no later than `rb` gives the race step. A
  justified block past `rb` is on the EMPTY side (`FinalitySetting.justified_empty`). So every
  honest head of the window avoids `full r` (`heads_avoid_full_window`). At the end of the
  window, every honest store has finalized `E₁` or later, on the EMPTY side
  (`honestNodes_finalize_empty`). A later head avoids `full r`, or there is slashing
  evidence, or two blocks, headers, or attestation data share a root.
* `EthCLSpecs.Proofs.Heze.FinalizationProgress`: a chain that includes the honest votes of
  three epochs finalizes the first one (`HonestChain.finalizes`). Each honest validator that
  the target test can count has a placed vote (`PlacedVote`), and these validators hold two
  thirds of the total active balance. Then each weigh step passes its previous-epoch test
  (`HonestChain.weigh`). When the justified block is on the EMPTY side of `r`, no head is below
  `full r` (`heads_stay_of_justified_empty`).
* `EthCLSpecs.Proofs.Heze.ForkPoint`: two runs from one state split at their fork point `st₀`
  (`ForkAt`, `ChainRun.forkAt`). The fork point ends the longest common prefix of their block
  messages.
  Before the slot of `st₀`, the runs have one root at each slot and one weigh state at each
  epoch. So their chains share the base when the fork comes late enough (`ForkAt.commonBase`).
  Two runs that reach a slot `T` and keep the same blocks below it fork at or after `T`
  (`ForkAt.slot_ge`). `regVals` holds every registry index.
* `EthCLSpecs.Proofs.Heze.FrameInvert`: the `frame_invert` tactic. From a run between two
  plain states, it proves that the run keeps a view, one action at a time. It closes a
  call of a spec function by a `@[frame]` lemma of that function, and a loop by an invariant.
* `EthCLSpecs.Proofs.Heze.FullSupport`: `getAncestor` returns an ancestor of its start
  node (`getAncestor_run_above`). So the store puts an index on `full` only when the
  supported node of its latest message lies below `full r` (`storeSide_full_below`). That
  message is from a slot after the slot of `r` (`fullSupport_slot_gt`).
* `EthCLSpecs.Proofs.Heze.GetInclusionListTransactions`: collector run
  equations for `getInclusionListCommittee` and
  `getInclusionListTransactions`
  (`getInclusionListCommittee_run_eq`, `getInclusionListTransactions_run_eq`),
  plus the missing-timeliness predicate on the `FcMap.fold` entries array. Under
  `LawfulFcMap`, a successful collection holds exactly the transactions of the stored,
  timely lists from validators that are not equivocators
  (`collectInclusionListTransactions_ok_mem_iff`, `getInclusionListTransactions_ok_mem_iff`).
  So it keeps each transaction of an honest list
  (`collectInclusionListTransactions_ok_mem`, `mem_getInclusionListTransactions`).
* `EthCLSpecs.Proofs.Heze.HandlerFrames`: the six handlers other than `onInclusionList`
  keep the IL store (`onBlock_keeps_ilStore` and the rest), with the `keeps_solve`
  tactic that walks a handler body.
* `EthCLSpecs.Proofs.Heze.HeaderFrame`: every function of a slot step and a block step, other
  than `processSlot` and `processBlockHeader`, keeps the latest block header and `blockRoots`
  (`processEpoch_frame_hdr`, `processBlockTail_frame_hdr`).
* `EthCLSpecs.Proofs.Heze.HeadAvoidsFull`: the node tree (`NodeEdge`, `NodeBelow`).
  Take a block from the previous slot with an unverified payload or a recorded `false`
  answer. The head that `getHead` returns is not the FULL node of the block and not
  below it (`getHead_run_avoids_full`). For a missing transaction under
  `DichotomyHypotheses`, the same holds at every `LaterStore`
  (`inclusionList_missing_tx_head_avoids_full`). Without the block at `r`, the walk never
  reaches the pending node of `r` (`getHead_run_avoids_full_of_no_block`).
* `EthCLSpecs.Proofs.Heze.HeadBelowJustified`: the head that `getHead` returns lies below
  the pending node of the justified root (`getHead_run_below_justified`).
* `EthCLSpecs.Proofs.Heze.HonestDuties`: the duties of slot `n + 1` on a head that avoids
  the FULL node of `r`. `shouldBuildOnFull` rejects a pending head and answers `false` at
  an EMPTY head. No honest vote is `(r, 1)` (`honestAttestation_ne_full`). An honest block
  (`HonestProposal`) has a parent root other than `r`. Or its head is the EMPTY node of `r`,
  and `processParentExecutionPayload` leaves the state unchanged, so the block settles no
  builder payment (`honestProposal_avoids_full`). `HonestProposal` covers a proposer that
  builds on the `getHead` head, without a proposer re-org. `honestNodes_duties_avoid_full`
  states the three facts for every honest node of a network.
* `EthCLSpecs.Proofs.Heze.HonestHead`: the head of an honest node in slot `n + 1` avoids
  the FULL node of `r` and every node below it, or a root collision exists
  (`honestNode_head_avoids_full`). The current slot comes from the wall clock
  (`getCurrentSlot_run_eq_of_window`, `ClockedTrace`).
* `EthCLSpecs.Proofs.Heze.HonestVoter`: take a checkpoint that the chain of a run justifies
  past its base. The adversary holds less than two thirds of the stake that weighs the link.
  Then an honest validator voted for the checkpoint (`justified_honest_voter`). A margin at
  the anchor and a drift bound give that premise on every run (`allChains_of_drift`).
* `EthCLSpecs.Proofs.Heze.HonestVoteSide`: an honest vote on a head below `empty r` puts
  its validator on `empty` in `storeSide` (`honest_supported_below_empty`,
  `storeSide_empty_of_below`). The `getAncestor` walk from a node below `empty r` returns
  `empty r`, and its fuel is enough because the chain roots are distinct keys
  (`getAncestor_run_below_empty`). The chain moves to a second store that holds the same
  blocks (`NodeBelow.transfer`).
* `EthCLSpecs.Proofs.Heze.ILStoreOrder`: the IL store after an arrival list in closed
  form (`ilStoreOfArrivals_describes`). The collected transactions depend only on the
  timeliness of the first arrival of each list
  (`getInclusionListTransactions_order_independent`), so the recorded answer does too
  (`recordPayloadInclusionListSatisfaction_order_independent`,
  `NodeTrace.answer_order_independent`).
* `EthCLSpecs.Proofs.Heze.InclusionDichotomy`: for one honest inclusion-list
  transaction, the envelope handler records one of two answers
  (`inclusionList_dichotomy`). With `true`, the payload includes the transaction or the
  EL omits it under `LawfulInclusionList`. With `false`, `UnsatisfiedPayload` holds at
  a later store (`LaterStore`). That store holds the block and the answer at its root.
  Its current slot is the slot after the block, and its slot increment does not overflow.
  `inclusionList_missing_tx` states the direction for one missing transaction, and
  `inclusionList_missing_tx_cost` takes it to the three facts of `unsatisfiedPayload_cost`.
* `EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied`: the complete
  `.run` equation of `isPayloadInclusionListSatisfied`
  (`isPayloadInclusionListSatisfied_run`), and the four read corollaries
  for a missing record, an unverified recorded value, a recorded `false`,
  and a recorded `true` with a verified payload.
* `EthCLSpecs.Proofs.Heze.JustificationAndFinalization`: what the weigh step of
  `processJustificationAndFinalization` writes on a plain value. The previous justified
  checkpoint takes the old current one. The current one takes the checkpoint of a justified
  epoch. The bits shift and get the bit of each justified epoch. The finalized checkpoint
  follows `finalizeRules` (`weighJustificationAndFinalization_run_ok`). Every
  other field keeps its value (`weighJustificationAndFinalization_run_keeps`). A failed run
  fails in a `getBlockRoot` read or in an overflow
  (`weighJustificationAndFinalization_run_error`).
  `processJustificationAndFinalization_run_eq` reduces the outer step to its five reads and
  the weigh step (`processJustificationAndFinalization_run_ok`).
* `EthCLSpecs.Proofs.Heze.JustificationBits`: the weigh step shifts the justification bits and
  sets bits 0 and 1 from its two target tests (`weighBits_get`).
* `EthCLSpecs.Proofs.Heze.KeepsUncached`: a run of each Heze operation handler, and of
  `processOperations`, that starts on an uncached box ends on an uncached box
  (`keepsUncached_processOperations` and the handler lemmas). `increaseBalance` and
  `decreaseBalance` also return an uncached box (`returnsUncached_increaseBalance`).
* `EthCLSpecs.Proofs.Heze.KeepsUncached.Block`, `….Payload`, `….Withdrawals`,
  `….Epoch`, `….Slots`: the same fact for every substep of `processBlock` and
  `processEpoch`, and for `processSlots` and `stateTransition`
  (`keepsUncached_stateTransition`). A run of the state transition that starts on an
  uncached box ends on an uncached box.
* `EthCLSpecs.Proofs.Heze.KeyFrame`: each function that a block step runs before the
  attestation loop, and each one inside it, keeps `keyView`. `keyView` holds the public keys
  of the registry, the fork, and the genesis validators root. A write of one validator keeps its
  public key (`keyView_modValidator`). The module also holds the plain-state forms of a write
  (`modValidator_pureState`).
* `EthCLSpecs.Proofs.Heze.LatestMessages`: only `onAttestation` writes the latest messages
  (`onAttestation_run_ok`). An entry at the end of a trace comes from an attestation event of
  the trace. That event checked the block and the slot of the vote (`NodeTrace.latest_source`,
  `AttWrite`). The slot of an entry never decreases (`NodeTrace.latest_mono`). Under
  `QsortMem`, an event delivers the vote of each attesting index that is not an equivocator
  (`onAttestation_delivers`). An attesting index is in a committee of the vote slot that the
  committee bits name, and `getBeaconCommittee` returns that committee as `.ok`
  (`getAttestingIndices_mem`).
* `EthCLSpecs.Proofs.Heze.ListLengths`: along a chain run, the balances, the two
  participation lists, and the inactivity scores keep the length of `validators` when they
  have it at the start (`ChainRun.listLengths`). Each spec function on the way has a lemma
  for the lengths.
* `EthCLSpecs.Proofs.Heze.NodeTrace`: the successful handler runs of one node
  (`NodeTrace`). From a seed with the empty IL store, such as the anchor store of
  `getForkchoiceStore`, the IL store is `ilStoreOfArrivals` of the arrivals of the trace
  (`NodeTrace.ilStore`).
* `EthCLSpecs.Proofs.Heze.NodeViews`: every honest node that handles an envelope for the
  root `r`, on a payload that omits a transaction of the honest list, records `false`
  (`honestNode_records_false`, `honestNodes_record_false`). The answer at `r` then never
  holds `true` (`honestNode_answer_ne_true`).
* `EthCLSpecs.Proofs.Heze.OnExecutionPayloadEnvelope`: the complete
  compositional `.run` equation of `onExecutionPayloadEnvelope`
  (`onExecutionPayloadEnvelope_run`), tagged
  `@[characterizes EthCLSpecs.Heze.onExecutionPayloadEnvelope]`, plus
  the four direct error corollaries and the successful-path corollary
  `onExecutionPayloadEnvelope_run_eq_of_successful_checks`, proved with
  `ForkChoiceStoreRun`. Under `LawfulFcMap`, the envelope and its
  inclusion-list answer are at the same root
  (`onExecutionPayloadEnvelope_run_pairing`).
* `EthCLSpecs.Proofs.Heze.OnInclusionList`: the run of `onInclusionList`
  (`onInclusionList_run_eq`), the three branches of `processInclusionList`
  (`processInclusionList_cases`), and the arrival model. An honest list stays in the
  IL store with the timeliness of its first arrival (`honestStored_of_arrivals`).
* `EthCLSpecs.Proofs.Heze.OnTickPerSlot`: a per-slot tick keeps the `blocks` and
  `payloadInclusionListSatisfaction` maps (`onTickPerSlot_run_keeps`).
* `EthCLSpecs.Proofs.Heze.ParentPayloadEmpty`: `processParentExecutionPayload` on
  the EMPTY edge, with the empty parent requests, does not change the state
  (`processParentExecutionPayload_run_of_empty_parent`). Fork choice calls an edge
  EMPTY exactly when the two block hashes differ
  (`getParentPayloadStatus_run_eq_empty_iff`).
* `EthCLSpecs.Proofs.Heze.Participation`: a target bit that `processAttestation` sets belongs
  to an attesting index with a matching source and target root
  (`processAttestation_explained`). With a matching source and target root, the run sets the
  target bit of each attesting index (`processAttestation_sets_target`). Along a chain run,
  each target flag of an epoch after the current epoch of the start state comes from an
  attestation that a block of the run includes (`ChainRun.flag_explained`).
* `EthCLSpecs.Proofs.Heze.ParticipationFrame`: every function of a slot step and a block step
  keeps one target bit and the slot (`partView`), except `processAttestation`, the flag
  rotation, and the deposits. The callers of `addValidatorToRegistry` keep a target bit of
  `false`. An epoch step clears the current bit, and a previous bit after it was a current
  bit before it (`processEpoch_part`).
* `EthCLSpecs.Proofs.Heze.ParticipationKeep`: a set target flag stays set inside one epoch
  (`ChainRun.targetFlag_keep`). `processAttestation` only adds flags, and every other function
  of a block step or of a slot step inside the epoch keeps them.
* `EthCLSpecs.Proofs.Heze.ParticipationRotate`: the epoch step moves the set current flag of a
  registry index to the previous list (`processEpoch_moves`, `SlotStep.targetFlag_moves`). The
  deposits write past every registry index, so they keep that flag.
* `EthCLSpecs.Proofs.Heze.PayloadRace`: the race between the EMPTY and the FULL node of a
  block from slot `N + 2` on. The model has validators, latest messages, and views
  (`sideWeight`, `ViewOk`). While the honest balance that has voted is more than the
  adversarial balance plus the boost, every allowed view puts EMPTY strictly ahead
  (`race_empty_persists`).
* `EthCLSpecs.Proofs.Heze.PayloadRaceBounds`: the counting inequality of
  `race_empty_persists` from uniform committees (`race_empty_persists_of_fraction`) and
  from honest proposers (`race_empty_persists_honest_proposers`). With the boost of
  `PROPOSER_SCORE_BOOST = 40`, one committee needs more than 70 % honest balance
  (`seventy_percent`).
* `EthCLSpecs.Proofs.Heze.PayloadRaceCount`: the counting inequality of
  `race_empty_persists_exec` from the committees of the window (`RaceCommittees.count`).
  Each validator votes in at most one slot. The first committee beats the proposer score,
  and each later committee has at least as much honest as adversarial balance. For a window
  inside one epoch, the committee partition gives the first condition
  (`EpochCommittees.oneVoteIn`, `RaceCommittees.of_epoch`). More than
  70 % honest balance in the first committee gives the second condition
  (`raceCommittees_first_of_fraction`).
* `EthCLSpecs.Proofs.Heze.PayloadRaceDecision`: tier T2 with the decision slot and the count
  discharged (`race_empty_persists_composed`). `DecisionSetting` holds the premises of tier
  T1. Under it, the honest heads of slot `N + 1` avoid `full r`, or a root collision exists
  (`RaceSetting.Core.first_of_decision`).
* `EthCLSpecs.Proofs.Heze.PayloadRaceExec`: tier T2 on the executable spec
  (`race_empty_persists_exec`). `RaceSetting.Core` puts every honest head of the window
  strictly below `pending r`, and `RaceSetting` adds the first slot. Under it and the
  counting inequality, each of these heads lies below `empty r` and not below `full r`, or
  a root collision exists. `race_empty_persists_long` states the race with one justified
  state per slot (`RaceSetting.Long`), for a window of several epochs.
* `EthCLSpecs.Proofs.Heze.PayloadRaceRefines`: the score of `full r` and of `empty r` is
  `sideWeight` of that side, over the active unslashed validators and the side the store
  gives each one (`score_full_refines`, `score_empty_refines`). One supported node is never
  under both children (`supportsVal_full_empty_exclusive`).
* `EthCLSpecs.Proofs.Heze.PayloadRaceWalk`: off the decision slot, weight decides the walk at
  `pending r`. When EMPTY is strictly ahead (`WeightAhead`), the loop body steps to
  `empty r` (`headLoopBody_run_pending_of_ahead`). The scores and a bound on the proposer
  score give `WeightAhead` (`weightAhead_of_scores`). The head avoids `full r`, and a head
  strictly below `pending r` is below `empty r` (`getHead_run_below_empty`).
* `EthCLSpecs.Proofs.Heze.PayloadTiebreak`: the payload tiebreak at a block from
  the previous slot, the zero weights, `betterOf`, and the `getHead` loop body
  `headLoopBody` to EMPTY (`getHeadStep_run_eq_empty_of_recorded_unsatisfied`), proved
  with `ForkChoiceStoreRun`. `getHead_eq_fuelLoop_headLoopBody` ties the body to
  `getHead` by `rfl`, and `getHead_walk_pending_to_empty` takes the walk from the
  pending node to the EMPTY node. The step lemmas hold at any runner state
  (`getCurrentSlot_run_state`).
* `EthCLSpecs.Proofs.Heze.PaymentCarried`: `stateTransition` as slot steps and a block
  step (`ChainRun`, `stateTransition_chainRun`). Along such a run, the entry of a bid keeps
  its withdrawal until the epoch substep that judges it (`bidPaymentCarried_of_run`),
  when the first child takes the EMPTY edge and no block slashes the bid's proposer at the
  bid's slot. The states of a run are plain values, and each step runs on their uncached
  boxes. `runChain` computes a run.
* `EthCLSpecs.Proofs.Heze.PaymentFrame`: the spec functions between a bid and its epoch
  substep keep the slot, the header slot, the cached bid, and the payment window
  (`windowView`), or the first three (`spineView`). Each frame lemma states the view of a
  run between plain states, and `frame_invert` (`FrameInvert`) proves it by run inversion.
* `EthCLSpecs.Proofs.Heze.PaymentWriters`: the writers of the payment window at one index
  (`processExecutionPayloadBid_run_payment`, `processAttestation_run_withdrawal`,
  `processProposerSlashing_run_withdrawal`, `processParentExecutionPayload_run_withdrawal`),
  and the index facts (`builderPaymentIndex_inj`).
* `EthCLSpecs.Proofs.Heze.ProposerScore`: a successful `getProposerScore` run returns
  `proposerScoreOf` of the justified checkpoint state (`getProposerScore_run_eq`). So the
  proposer score is one value per justified state.
* `EthCLSpecs.Proofs.Heze.RaceCheck`: the premises of `race_empty_persists_composed` as
  computations. When every vote finds its target in the store before it, the checkpoint
  states stay those of the seed (`NodeTrace.checkpointStates_eq`). `deliver_of_check`,
  `HeadRun.Ok.of_check`, and `honestSigner_of_check` give premises from checks.
* `EthCLSpecs.Proofs.Heze.RaceLong`: the counting inequality of `race_empty_persists_long`
  after a full epoch of the window (`count_of_epoch`). Every validator that is active at the
  epoch has voted, so a margin of the honest total over the adversarial total gives the
  count. `hcount_of_parts` joins it to `RaceCommittees.count` for the first part.
* `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: the
  complete run of `recordPayloadInclusionListSatisfaction`
  (`recordPayloadInclusionListSatisfaction_run`), proved with
  `ForkChoiceStoreRun`.
* `EthCLSpecs.Proofs.Heze.RefDrift`: the drift of a state from the fork point `st₀`
  (`refDrift`). It adds the distances of the link stakes of the state from the current-epoch
  stake of `st₀`, and the shortfall of its total. `runDrift` takes the largest drift over the
  run after `st₀`. From the epoch of `st₀` on, the chain of the run stays within `runDrift`
  (`ForkAt.stakeClose`). `refDrift_le_drift` bounds the drift by the stake drift `drift` plus
  the stake that exits at the epoch of `st₀`.
* `EthCLSpecs.Proofs.Heze.RootFrames`: each handler keeps the block, the envelope, and
  the answer at a root `r`, unless it writes another value there
  (`HandlerEvent.run_keeps_rootView`). A trace after the envelope handler, with no second
  envelope for `r`, gives `LaterStore` (`NodeTrace.laterStore`). Traces split and join
  (`NodeTrace.split`, `NodeTrace.append`). `inclusionList_missing_tx_trace` states the
  missing-transaction result over such a trace.
* `EthCLSpecs.Proofs.Heze.Run`: `HezeRun`, the runner for Heze state transitions.
* `EthCLSpecs.Proofs.Heze.RunVotes`: each target flag of an epoch after the anchor epoch comes
  from a vote that a block of the run includes. `processAttestation` accepted it on a state
  with the checkpoints, the slot, and the block roots of the run state before the block, and
  with its public keys, fork, and genesis validators root (`RunVote`, `ChainRun.flag_located`).
* `EthCLSpecs.Proofs.Heze.RunWeighs`: a chain run is a function of its start state and its
  steps (`ChainRun.det`). The slot and the epoch do not decrease, and the steps of one epoch
  keep the checkpoints (`ChainRun.ckView_of_epoch`). An epoch has at most one weigh state
  (`WeighAt.unique`). The slot step after it runs the weigh step on the balances of that
  state (`SlotStep.weigh`).
* `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: the complete `.run`
  equation of `shouldExtendPayload` (`shouldExtendPayload_run`), the
  existing recorded-unsatisfied FOCIL rejection
  (`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`), and the
  named prefix, FOCIL, vote, and inherited-Gloas-tail corollaries.
* `EthCLSpecs.Proofs.Heze.Shuffle`: the inherited `computeShuffledPermutation`
  returns a permutation of `[0, n)` whenever it does not raise
  (`computeShuffledPermutation_perm`).
* `EthCLSpecs.Proofs.Heze.SlotsIncrease`: block slots increase along parent links at the
  end of a trace from the anchor store, or two distinct headers or blocks share a root
  (`NodeTrace.slotInv`). The argument uses the header check of `processBlockHeader` and
  the block-root lemma, and needs no frame over the state transition.
  `inclusionList_missing_tx_anchored` states the missing-transaction result on such a
  trace, with the justified-root hypothesis reduced to a slot comparison.
* `EthCLSpecs.Proofs.Heze.StakeDrift`: the stake drift along a chain run
  (`chainRun_drift_le`). The run ends at the epoch `E` of its end state, within half a
  slashings vector of `st₀`, and each state of the run meets `StatePre`. Then the distances of
  the link stakes, plus the shortfall of the total active balance, are at most
  `driftBound`. The bound reads `st₀`, the churn bounds, and the bounds of the total active
  balance, of the effective balances, and of the inactivity scores along the run.
* `EthCLSpecs.Proofs.Heze.StoreChainState`: a store traces to the anchor of a chain run and
  receives a block of the run. Then the store holds the state of the run after that block,
  unless two blocks share a root (`onBlock_stores_chainState`). Each block of a validated run names the last block
  before it as its parent (`ChainRun.linked`). Two runs from one state with one list of blocks
  and one end slot end in one state (`ChainRun.det_blocks`).
* `EthCLSpecs.Proofs.Heze.StoreClock`: the blocks of a head-run store are no later than its
  slot (`HeadRun.Base.block_slot_le`). A placed vote is from a slot before its block, and
  its target epoch is the epoch of its slot (`RunVote.slot_lt_block`). Each checkpoint
  epoch of a traced store is at most the anchor epoch or the epoch of a block event of the
  trace (`NodeTrace.ckptWit`). Each checkpoint is the anchor checkpoint or is from a later
  epoch (`NodeTrace.ckptAbove`).
* `EthCLSpecs.Proofs.Heze.StoreFinality`: an honest store finalizes `E₁` from the first slot
  of `E₁ + 4` (`honestStore_finalizes`). It receives the block of the last slot of `E₁ + 3`
  before that slot. The pull-up of that block finalizes `E₁` or later
  (`HonestChain.pullup_finalizes`). The tick that reaches the first slot of an epoch realizes
  the unrealized finalized checkpoint (`onTick_realizes`).
* `EthCLSpecs.Proofs.Heze.StorePure`: every state that the store holds is the uncached box
  of a plain value, at the end of a trace from the anchor store of `getForkchoiceStore`
  over an uncached anchor (`StorePure.anchor`, `NodeTrace.storePure`). The `blockStates`
  half needs only the law of the root map (`NodeTrace.blockStatesPure`). The run
  inversions of `onBlock` and the envelope handler return the stored states as plain
  values (`onBlock_run_ok`, `onExecutionPayloadEnvelope_run_ok`). The predicates are in
  `….StorePure.Basic`.
* `EthCLSpecs.Proofs.Heze.SyncFrame`: the `sync_frame` tactic, the frame fact of a
  `processSyncAggregate` run for a view. It names the join point after the key choice, so
  `frame_invert` inverts it once.
* `EthCLSpecs.Proofs.Heze.TargetStake`: under `RunTotals`, a passed target test bounds the sum
  of `linkStake` over a list that holds every counted index (`link_weight`).
* `EthCLSpecs.Proofs.Heze.Time`: the inherited `computeEpochAtSlot`,
  `computeStartSlotAtEpoch`, and `computeActivationExitEpoch` at Heze. The `Downgrade`
  bridge reaches one fork up, so each theorem takes the Gloas proof term.
* `EthCLSpecs.Proofs.Heze.TraceFacts`: a key of the block map stays a key along a trace
  (`NodeTrace.blocks_persist`). An attestation event of a clocked trace ran at a current
  slot no greater than the current slot of a later query (`ClockedTrace.attestation_slot_le`).
  An honest signer of a trace is an honest signer of each prefix (`HonestSigner.prefix`).
* `EthCLSpecs.Proofs.Heze.TraceRun`: a node trace as a function. `runTrace` runs the
  handlers of a trace, and a trace exists exactly when it succeeds
  (`NodeTrace.iff_runTrace`), so a trace is a function of its events (`NodeTrace.det`).
  `traceAll` checks the stores of a trace in one pass. `ClockedTrace.of_check`,
  `RootFacts.of_check`, and `HonestList.of_check` derive the hypotheses of the network
  results from `Bool` checks that `native_decide` closes.
* `EthCLSpecs.Proofs.Heze.VoteValid`: a placed vote is an indexed attestation that
  `processAttestation` validated. It is valid on the run state before its block
  (`RunVote.indexed`, under `QsortMem`). `isValidIndexedAttestation` reads only `keyView`
  (`isValidIndexedAttestation_of_keyView`).
-/
