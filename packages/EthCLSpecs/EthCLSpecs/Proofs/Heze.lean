import EthCLSpecs.Proofs.Heze.AttestationScore
import EthCLSpecs.Proofs.Heze.BlockRoot
import EthCLSpecs.Proofs.Heze.BuilderPendingPayments
import EthCLSpecs.Proofs.Heze.CensorshipCost
import EthCLSpecs.Proofs.Heze.CheckpointOrd
import EthCLSpecs.Proofs.Heze.Churn
import EthCLSpecs.Proofs.Heze.ClockedTrace
import EthCLSpecs.Proofs.Heze.Committees
import EthCLSpecs.Proofs.Heze.Equivocators
import EthCLSpecs.Proofs.Heze.FullSupport
import EthCLSpecs.Proofs.Heze.GetInclusionListTransactions
import EthCLSpecs.Proofs.Heze.HandlerFrames
import EthCLSpecs.Proofs.Heze.HeadAvoidsFull
import EthCLSpecs.Proofs.Heze.HonestDuties
import EthCLSpecs.Proofs.Heze.HonestHead
import EthCLSpecs.Proofs.Heze.HonestVoteSide
import EthCLSpecs.Proofs.Heze.ILStoreOrder
import EthCLSpecs.Proofs.Heze.InclusionDichotomy
import EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied
import EthCLSpecs.Proofs.Heze.KeepsUncached
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
import EthCLSpecs.Proofs.Heze.PayloadRace
import EthCLSpecs.Proofs.Heze.PayloadRaceBounds
import EthCLSpecs.Proofs.Heze.PayloadRaceExec
import EthCLSpecs.Proofs.Heze.PayloadRaceRefines
import EthCLSpecs.Proofs.Heze.PayloadRaceWalk
import EthCLSpecs.Proofs.Heze.PayloadTiebreak
import EthCLSpecs.Proofs.Heze.PaymentCarried
import EthCLSpecs.Proofs.Heze.PaymentFrame
import EthCLSpecs.Proofs.Heze.PaymentWriters
import EthCLSpecs.Proofs.Heze.ProposerScore
import EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction
import EthCLSpecs.Proofs.Heze.RootFrames
import EthCLSpecs.Proofs.Heze.Run
import EthCLSpecs.Proofs.Heze.ShouldExtendPayload
import EthCLSpecs.Proofs.Heze.Shuffle
import EthCLSpecs.Proofs.Heze.SlotsIncrease
import EthCLSpecs.Proofs.Heze.SyncFrame
import EthCLSpecs.Proofs.Heze.Time
import EthCLSpecs.Proofs.Heze.TraceFacts
import EthCLSpecs.Proofs.Heze.TraceRun

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
to the `getHead` walk. `PayloadRaceExec` states the result on the executable spec.

Every declaration here sits in the `EthCLSpecs.Proofs.Heze` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Heze.AttestationScore`: the Heze `getAttestationScore` is the `Nat` sum
  of the effective balances of the counted active indices (`getAttestationScore_run_ok`).
* `EthCLSpecs.Proofs.Heze.BlockRoot`: a block root is the root of its header
  (`htr_eq_htr_headerOf`), under the hypothesis that every `combine` returns 32 bytes.
  The root of a 32-byte vector is its bytes (`hashTreeRoot_bytes32`).
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
* `EthCLSpecs.Proofs.Heze.CheckpointOrd`: the derived order on `Checkpoint` is transitive
  and returns `.eq` only on equal checkpoints (`instTransOrdCheckpoint`,
  `instLawfulEqOrdCheckpoint`), so `treeMap` meets the map laws at `Checkpoint`.
* `EthCLSpecs.Proofs.Heze.Churn`: the inherited `reserveChurn`, which takes the Gloas proof
  terms, and run theorems for the two inherited churn callers.
* `EthCLSpecs.Proofs.Heze.ClockedTrace`: a node trace on the wall clock
  (`ClockedTrace`). The current slot and the time into the slot in terms of the wall time
  (`slotStartMs_le_of_getCurrentSlot`, `timeIntoSlotMs_lt_of_window`). A state at a root
  comes from an `onBlock` event that passed its clock check
  (`NodeTrace.blockStates_origin`, `onBlock_run_ok_currentSlot`).
* `EthCLSpecs.Proofs.Heze.Committees`: the inherited committee functions
  partition the active set per epoch (`getBeaconCommittee_partition`).
* `EthCLSpecs.Proofs.Heze.Equivocators`: only `onAttesterSlashing` adds to
  `equivocatingIndices`, and only an index that both attestations carry and whose
  slashing passes its checks (`onAttesterSlashing_run_ok`, `onAttesterSlashing_new_member`).
  Along a trace from the anchor, an index that no slashing of the trace marks is never in
  the set (`honest_not_equivocating`).
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
* `EthCLSpecs.Proofs.Heze.HeadAvoidsFull`: the node tree (`NodeEdge`, `NodeBelow`).
  Take a block from the previous slot with an unverified payload or a recorded `false`
  answer. The head that `getHead` returns is not the FULL node of the block and not
  below it (`getHead_run_avoids_full`). For a missing transaction under
  `DichotomyHypotheses`, the same holds at every `LaterStore`
  (`inclusionList_missing_tx_head_avoids_full`). Without the block at `r`, the walk never
  reaches the pending node of `r` (`getHead_run_avoids_full_of_no_block`).
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
* `EthCLSpecs.Proofs.Heze.KeepsUncached`: a run of each Heze operation handler, and of
  `processOperations`, that starts on an uncached box ends on an uncached box
  (`keepsUncached_processOperations` and the handler lemmas). `increaseBalance` and
  `decreaseBalance` also return an uncached box (`returnsUncached_increaseBalance`).
* `EthCLSpecs.Proofs.Heze.KeepsUncached.Block`, `….Payload`, `….Withdrawals`,
  `….Epoch`, `….Slots`: the same fact for every substep of `processBlock` and
  `processEpoch`, and for `processSlots` and `stateTransition`
  (`keepsUncached_stateTransition`). A run of the state transition that starts on an
  uncached box ends on an uncached box.
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
* `EthCLSpecs.Proofs.Heze.PayloadRaceExec`: tier T2 on the executable spec
  (`race_empty_persists_exec`). `RaceSetting` puts every honest head of the window strictly
  below `pending r`. Under it and the counting inequality, each of these heads lies below
  `empty r` and not below `full r`, or a root collision exists.
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
* `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: the
  complete run of `recordPayloadInclusionListSatisfaction`
  (`recordPayloadInclusionListSatisfaction_run`), proved with
  `ForkChoiceStoreRun`.
* `EthCLSpecs.Proofs.Heze.RootFrames`: each handler keeps the block, the envelope, and
  the answer at a root `r`, unless it writes another value there
  (`HandlerEvent.run_keeps_rootView`). A trace after the envelope handler, with no second
  envelope for `r`, gives `LaterStore` (`NodeTrace.laterStore`). Traces split and join
  (`NodeTrace.split`, `NodeTrace.append`). `inclusionList_missing_tx_trace` states the
  missing-transaction result over such a trace.
* `EthCLSpecs.Proofs.Heze.Run`: `HezeRun`, the runner for Heze state transitions.
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
-/
