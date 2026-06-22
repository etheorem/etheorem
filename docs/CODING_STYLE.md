# Coding style

Worked, example-driven conventions for the Etheorem monorepo. This sits under
[`CLAUDE.md`](../CLAUDE.md), which is binding on style and form across all
subpackages and states the principles tersely. This document is the elaboration:
the same principles applied to real code, with before/after pairs. Where the two
overlap, CLAUDE.md wins. This file shows; it does not legislate.

The first section covers function bodies, the prose inside a definition. More
sections can follow as other patterns earn a worked write-up.

Examples are drawn from across the monorepo. EthCLSpecs supplies most of them
because it holds the densest procedural code. The techniques apply equally to
SizzLean, LeanSha256, and LeanPoseidon, and several examples come from those
packages to show the reach.

---

## Function body

This is about the body, the part between the signature and the `return`. It is not
about the `/-- … -/` docstring above it. The docstring carries the "why" of a
definition. This section is about making the steps inside it easy to follow, the
literate-by-default principle from CLAUDE.md applied below the docstring line.

The techniques in §1 through §4 are general Lean and imperative style. §5
(splitting) adds one rule that follows from this repo's nature as a set of ports.
§6 returns to general style for loops that thread an accumulator. §7 is the
counterweight: when to do none of it.

The guidance is independent of the DSL a definition is written in. It applies to a
plain `def`, a `forkdef`, an `inherit`ed body, or a `mutual` block alike. It is
about the `let`-chain and control-flow prose inside.

### 1. Paragraph the phases

The clearest win. A function that does several things in sequence should show
several groups, separated by a blank line. The reader's eye then finds the seams
without parsing every statement.

`permuteWith` (`packages/LeanPoseidon/LeanPoseidon/Poseidon2/Permutation.lean:permuteWith`)
is the model. Its four schedule phases each sit on their own `let st := …` line
under a one-line header naming the phase:

```lean
  -- (1) initial external linear layer
  let st := extLayer st0
  -- (2) beginning full rounds r = 0 .. half−1; constants at flat[3r + i]
  let st := Nat.fold half (fun r _ st => fullRound extLayer (fun i => rc[3 * r + i.val]!) st) st
  -- (3) partial rounds j = 0 .. np−1; constant at flat[3·half + j]
  let st := Nat.fold np (fun j _ st => partialRound intLayer (rc[3 * half + j]!) st) st
  -- (4) end full rounds k = 0 .. half−1; constants at flat[3·half + np + 3k + i]
  let st := Nat.fold half (fun k _ st => fullRound extLayer (fun i => rc[3 * half + np + 3 * k + i.val]!) st) st
```

Each header maps to a step of the zkhash schedule, so the comments teach the
reference and mark the phases at once.

The long, unbroken bodies are what diverge from this. The densest is
`process_attestation` in Gloas (`packages/EthCLSpecs/EthCLSpecs/Gloas/Operations.lean:processAttestation`),
57 lines with one internal comment, running six distinct phases together:

```lean
-- before (abbreviated)
forkdef processAttestation (att : Attestation) : StateTransition Unit := do
  let state ← get
  let data := att.data
  assert (data.target.epoch == previousEpochOf state || data.target.epoch == currentEpochOf state)
  assert (data.target.epoch == computeEpochAtSlot data.slot)
  assert (data.slot + Const.minAttestationInclusionDelay ≤ sszGet state slot)
  assert (data.index < 2)
  let count := getCommitteeCountPerSlot state data.target.epoch
  let (ok, offset) := (getCommitteeIndices att.committeeBits).foldl …
  assert ok
  assert (att.aggregationBits.size == offset)
  let flagIndices ← match getAttestationParticipationFlagIndices state data … with
    | some f => pure f
    | none   => throw (StateTransitionError.assert "attestation participation flags")
  let indexedAttestation : IndexedAttestation := …
  assert (isValidIndexedAttestation state indexedAttestation)
  let currentTarget := data.target.epoch == currentEpochOf state
  …
  for vi in (← liftErr (getAttestingIndices state att)) do
    …
  stateAcc := sszUpdate stateAcc with builderPendingPayments[paymentIdx]! := …
  let proposerDenom := …
  stateAcc := increaseBalance stateAcc (getBeaconProposerIndex stateAcc) …
  set stateAcc
```

The same body with phase breaks and four short headers:

```lean
-- after
forkdef processAttestation (att : Attestation) : StateTransition Unit := do
  let state ← get
  let data := att.data

  -- Reject on shape: target epoch, slot timing, and the payload-presence bit.
  assert (data.target.epoch == previousEpochOf state || data.target.epoch == currentEpochOf state)
  assert (data.target.epoch == computeEpochAtSlot data.slot)
  assert (data.slot + Const.minAttestationInclusionDelay ≤ sszGet state slot)
  assert (data.index < 2)

  -- Every committee index is valid and non-empty; the bitfield covers them all.
  let count := getCommitteeCountPerSlot state data.target.epoch
  let (ok, offset) := (getCommitteeIndices att.committeeBits).foldl …
  assert ok
  assert (att.aggregationBits.size == offset)

  -- Resolve the participation flags, then validate the aggregate signature.
  let flagIndices ← match getAttestationParticipationFlagIndices state data … with
    | some f => pure f
    | none   => throw (StateTransitionError.assert "attestation participation flags")
  let indexedAttestation : IndexedAttestation := …
  assert (isValidIndexedAttestation state indexedAttestation)

  -- Apply participation flags and accumulate the builder-payment weight.
  let currentTarget := data.target.epoch == currentEpochOf state
  …
  for vi in (← liftErr (getAttestingIndices state att)) do
    …

  -- Write back the payment weight and pay the proposer.
  stateAcc := sszUpdate stateAcc with builderPendingPayments[paymentIdx]! := …
  let proposerDenom := …
  stateAcc := increaseBalance stateAcc (getBeaconProposerIndex stateAcc) …
  set stateAcc
```

Same logic, same line count of code. The four headers carry the spec's own phase
structure, so they tell the reader where they are.

Those headers are not mandatory. The blank line is the rule; the header above it is
optional. Add one only when the phase's purpose is not obvious from the lines it
groups, the spec step it implements, or a reason that is not on the page. Many
paragraphs earn the blank line and nothing more. A header that just restates its
block in English is the obvious comment §3 says to delete, and the same holds for any
line comment inside the body: if the code already says it, the comment is noise.

Other good candidates: `getExpectedWithdrawals`
(`EthCLSpecs/Fulu/Withdrawals.lean:getExpectedWithdrawals`, blank lines between setup, the partial
loop, and the sweep loop), `onBlock` (`EthCLSpecs/Gloas/ForkChoice.lean:onBlock`), and
`verifyExecutionPayloadEnvelope` (`EthCLSpecs/Gloas/ForkChoice.lean:verifyExecutionPayloadEnvelope`, the assert
wall reads better split into signature / block-root / bid-consistency groups).

#### Inside a branch, too

The rule does not stop at the top level. A `match` arm or an `if` / `else` branch
is already fenced off from its siblings by the control flow, so the branch split
itself is one seam. But when a single branch runs several sub-phases of its own,
paragraph *those* as well. The reader's eye needs the seams inside the branch for
the same reason it needs them in a flat body.

The leaf case of `filterBlockTree.go` (`EthCLSpecs/Gloas/ForkChoice.lean:filterBlockTree.go`)
decides a branch's viability from two independent criteria, the voting-source
check and the finalized-checkpoint check. They run in sequence and are combined
once at the end, so the one branch holds two phases:

```lean
-- before
    if children.isEmpty then
      let currentEpoch := getCurrentStoreEpoch store
      let votingSource := getVotingSource store blockRoot
      let correctJustified :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
          || votingSource.epoch + 2 ≥ currentEpoch
      let finalizedBlock := getCheckpointBlock store blockRoot store.finalizedCheckpoint.epoch
      let correctFinalized :=
        store.finalizedCheckpoint.epoch == Const.genesisEpoch
          || store.finalizedCheckpoint.root == finalizedBlock
      if correctJustified && correctFinalized then (acc.push blockRoot, true) else (acc, false)
    else
      …
```

```lean
-- after
    if children.isEmpty then
      -- A leaf branch is viable when its voting source stays close to the justified
      -- checkpoint (genesis, the same epoch, or within two epochs of the current one).
      let currentEpoch := getCurrentStoreEpoch store
      let votingSource := getVotingSource store blockRoot
      let correctJustified :=
        store.justifiedCheckpoint.epoch == Const.genesisEpoch
          || votingSource.epoch == store.justifiedCheckpoint.epoch
          || votingSource.epoch + 2 ≥ currentEpoch

      -- The finalized checkpoint must also lie on this branch.
      let finalizedBlock := getCheckpointBlock store blockRoot store.finalizedCheckpoint.epoch
      let correctFinalized :=
        store.finalizedCheckpoint.epoch == Const.genesisEpoch
          || store.finalizedCheckpoint.root == finalizedBlock
      if correctJustified && correctFinalized then (acc.push blockRoot, true) else (acc, false)
    else
      …
```

A header earns its place on each group here, since the criterion a predicate
encodes is not obvious from its name alone (§3). The §7 limits still bind inside a
branch: do not blank-line between the two `let`s that build one predicate
(`correctJustified` spans three lines and is one paragraph), and do not paragraph a
branch that does a single thing. And the seam between the arms is the `if` / `else`
itself, never a blank line between `match` arms.

#### Break the setup off from the action

The most common seam, and the one easiest to miss, is the boundary between a body's
binding preamble and its imperative work. A handler typically opens with a run of
`let` reads and derived values, then turns to the action: a loop, a `modifyState`, a
chain of `assert`s. Those are two phases even when the function does one job, so a
blank line between them lets the eye find where setup ends and work begins.
`processPendingDeposits` (`EthCLSpecs/Fulu/EpochProcessing.lean:processPendingDeposits`) gathers its five
inputs, then a blank line, then runs the scan and writes the result back:

```lean
forkdef processPendingDeposits : StateTransition Unit := do
  let state ← get
  let nextEpoch := currentEpochOf state + 1
  let avail := (sszGet state depositBalanceToConsume) + getActivationExitChurnLimit state
  let finalizedSlot := computeStartSlotAtEpoch (sszGet state finalizedCheckpoint).epoch
  let deposits := (sszGet state pendingDeposits).toArray

  let scan ← ppdLoop deposits finalizedSlot avail nextEpoch
  modifyState fun state => sszUpdate state with
    pendingDeposits := sszOfArray (deposits.extract scan.ndi deposits.size ++ scan.postpone),
    depositBalanceToConsume := if scan.churnReached then avail - scan.processed else 0
```

No header is needed here: the binding names say what the setup gathers, and the call
says what runs. Add a header on either side only when the purpose is not obvious from
reading it (§3). The blank line is the whole point; a comment over each paragraph that
just renames it is the noise §3 warns against.

### 2. Name intermediates for what they hold

A two-letter local hides its meaning. `getHead.better`
(`EthCLSpecs/Gloas/ForkChoice.lean:getHead.better`) compares two fork-choice nodes:

```lean
-- before
  better (store : Store map) (a b : ForkChoiceNode) : Bool :=
    let wa := getWeight store a
    let wb := getWeight store b
    if wa > wb then true
    else if wa < wb then false
    else match compare a.root b.root with …
```

```lean
-- after
  better (store : Store map) (a b : ForkChoiceNode) : Bool :=
    let weightA := getWeight store a
    let weightB := getWeight store b
    if weightA > weightB then true
    else if weightA < weightB then false
    else match compare a.root b.root with …
```

The sharper case is a function whose whole return is a tuple of terse locals.
`getExpectedWithdrawals` in Gloas (`EthCLSpecs/Gloas/Withdrawals.lean:getExpectedWithdrawals`) threads
four phases through `wi0…wi3`, `bw/pw/sw/vw`, and `bc/pc/sc`. The docstring has to
spell out that the trailing `Nat × Nat × Nat` is "(builder, partial,
builders-sweep) processed counts" because the names alone do not say it:

```lean
-- before
  let wi0 := sszGet (← get) nextWithdrawalIndex
  let (bw, wi1, bc) ← getBuilderWithdrawals wi0 #[]
  let (pw, wi2, pc) ← getPendingPartialWithdrawals wi1 bw
  let prior2 := bw ++ pw
  let (sw, wi3, sc) ← getBuildersSweepWithdrawals wi2 prior2
  let prior3 := prior2 ++ sw
  let (vw, _, _) ← getValidatorsSweepWithdrawals wi3 prior3
  return (prior3 ++ vw, bc, pc, sc)
```

```lean
-- after
  let firstIndex := sszGet (← get) nextWithdrawalIndex
  let (builderWs, idxAfterBuilder, builderCount) ← getBuilderWithdrawals firstIndex #[]
  let (partialWs, idxAfterPartial, partialCount) ← getPendingPartialWithdrawals idxAfterBuilder builderWs
  let priorAfterPartial := builderWs ++ partialWs
  let (sweepWs, idxAfterSweep, sweepCount) ← getBuildersSweepWithdrawals idxAfterPartial priorAfterPartial
  let priorAfterSweep := priorAfterPartial ++ sweepWs
  let (validatorWs, _, _) ← getValidatorsSweepWithdrawals idxAfterSweep priorAfterSweep
  return (priorAfterSweep ++ validatorWs, builderCount, partialCount, sweepCount)
```

Now the `return` line reads as a sentence, and `prior3` no longer makes the reader
count back to see which phases it sums.

#### When a short name earns its keep

Two cases where expansion adds noise:

- **Reference-mirroring parameters.** `updateCheckpoints (store) (j f : Checkpoint)`
  (`EthCLSpecs/Gloas/ForkChoice.lean:updateCheckpoints`) takes `j` and `f` because the upstream
  `update_checkpoints(store, justified, finalized)` is right there. Expanding the
  body's uses helps; expanding the parameter names is a small, optional gain. The
  same goes for `rc` / `half` / `np` in `permuteWith`, which track the zkhash
  variable names.
- **Established local idioms.** `let hb ← assertH (…)` binds a bound proof used
  once as `…'hb.down`. The name is a fixed pattern across every operation handler.
  Renaming it per call site would break a pattern the reader has already learned.

The rule: expand a name when it is an internal invention whose meaning lives only
in the author's head, such as `wa`, `bc`, or `prior3`. Keep it short when it
mirrors a reference parameter the reader can look up, or it is an established
idiom.

### 3. Comment the section, never the line

Section comments earn their place when they name a phase that spans several
statements, the reference step a block implements, or a non-obvious reason a line
exists. Good instances are everywhere: the `-- update_next_withdrawal_index` tags
in `process_withdrawals` (`EthCLSpecs/Gloas/Withdrawals.lean:processWithdrawals`) pin each block to
its spec function, the `(1) … (4)` headers in `permuteWith` pin each block to the
zkhash schedule, and the `sszGetIdx` rationale in `processAttestation`
(`EthCLSpecs/Gloas/Operations.lean:processAttestation`) explains why a read takes the fallible
path.

Four habits, three to keep and one to drop:

- **Tag the reference step.** When a block implements a named procedure from the
  spec or paper (`update_*`, an EIP step, a schedule round), name it. The reader
  cross-references the source by that name.
- **Name the phase.** The `-- Pending partial withdrawals (EIP-7251).` /
  `-- Validator sweep (Capella).` pair in `getExpectedWithdrawals`
  (`EthCLSpecs/Fulu/Withdrawals.lean:getExpectedWithdrawals`) is the model. Two comments, two
  phases.
- **Explain a load-bearing inference.** The `sszGetIdx` comments say why an index
  read must reject instead of masking. The cache-root comment in `Node.ofSubtrees`
  (`SizzLean/Cache/MerkleTree/Build.lean:Node.ofSubtrees`) says why the root is computed inline.
  Neither fact is recoverable from the surface code. CLAUDE.md asks for exactly
  this on non-obvious inferences.
- **Do not restate the code.** A `-- get the state` above `let state ← get` is
  noise. CLAUDE.md already bans it. Hold the line as headers get added: a comment
  that repeats its line in English is worse than no comment.

Any comment added follows the CLAUDE.md "Writing Style & Structural Constraints"
section, which governs code comments too. No em-dashes for subphrases, no
"not X, but Y" framing, plain words. The headers above are written to that
standard.

### 4. Lift complex expressions into named steps

A nested expression that spans a line and a half does two jobs: it computes a
value and it hides what the value is. Splitting it names the value and often
removes a duplicated subexpression.

`advanceStoreTime` (`EthCLSpecs/Gloas/ForkChoice.lean:advanceStoreTime`) buries the target slot
in the fuel argument, then recomputes the identical formula inside the loop:

```lean
-- before
forkdef advanceStoreTime (store : Store map) (time : UInt64) : Store map :=
  fuelIterate (((((time - store.genesisTime) * 1000) / Const.slotDurationMs) - getCurrentSlot store).toNat + 1) store fun store =>
    let tickSlot := ((time - store.genesisTime) * 1000) / Const.slotDurationMs
    if getCurrentSlot store < tickSlot then
      let previousTime := store.genesisTime + (getCurrentSlot store + 1) * Const.slotDurationMs / 1000
      .next (onTickPerSlot store previousTime)
    else .done (onTickPerSlot store time)
```

```lean
-- after
forkdef advanceStoreTime (store : Store map) (time : UInt64) : Store map :=
  -- The slot `time` lands in. It is loop-invariant (only `time` and the fixed
  -- `genesisTime` feed it, and `onTickPerSlot` touches neither), so it doubles as
  -- the fuel bound and is read unchanged inside the sweep.
  let targetSlot := ((time - store.genesisTime) * 1000) / Const.slotDurationMs
  let fuel := (targetSlot - getCurrentSlot store).toNat + 1
  fuelIterate fuel store fun store =>
    if getCurrentSlot store < targetSlot then
      let nextSlotTime := store.genesisTime + (getCurrentSlot store + 1) * Const.slotDurationMs / 1000
      .next (onTickPerSlot store nextSlotTime)
    else .done (onTickPerSlot store time)
```

The giant fuel argument becomes a named `fuel`, the duplicated `tickSlot` formula
collapses to one `targetSlot`, and the comment records the invariant that makes the
dedup safe. That invariant is the kind of load-bearing inference CLAUDE.md asks to
be spelled out, since a reader cannot tell from the old code that the inner
recompute was redundant.

The Gloas `process_withdrawals` cursor update
(`EthCLSpecs/Gloas/Withdrawals.lean:processWithdrawals`) has a duplicated shape worth collapsing:
two `sszUpdate` arms, each wrapping the same `if nvals == 0 then 0 else … % nvals`
guard.

```lean
-- after
  -- update_next_withdrawal_validator_index: a full payload resumes one past the
  -- last validator drained; a short one jumps a whole sweep window ahead. Both
  -- wrap modulo the registry size (0 when empty).
  modifyState fun state =>
    let nvals := (sszGet state validators).size
    let sweptFullPayload := expected.size == Const.maxWithdrawalsPerPayload
    let nextCursor :=
      if sweptFullPayload then (expected[expected.size - 1]!).validatorIndex.toNat + 1
      else (sszGet state nextWithdrawalValidatorIndex).toNat + Const.maxValidatorsPerWithdrawalsSweep
    let wrapped := if nvals == 0 then 0 else nextCursor % nvals
    sszUpdate state with nextWithdrawalValidatorIndex := UInt64.ofNat wrapped
```

The branch now decides one value (`nextCursor`); the wrap and the write happen once
each. The two cases stand side by side instead of being buried in parallel
`sszUpdate` boilerplate.

#### When the duplication is structural, realign to the reference

Sometimes the repeated thing is not a subexpression but a whole decision: the same
check sits in two arms of a `match` because the port grew a control-flow shape the
reference does not have. Lifting a `let` does not fix that. Restoring the
reference's shape does, and it writes the check once.

`ppdLoop` (`EthCLSpecs/Fulu/EpochProcessing.lean:ppdLoop`), the `process_pending_deposits`
scan, matched `validatorIndexByPubkey?` first and then ran the churn-limit check in
*both* the `some` and the `none` arm:

```lean
-- before
        match validatorIndexByPubkey? state deposit.pubkey with
        | some vi =>
          let validator := sszGet state validators[vi]!
          if validator.withdrawableEpoch < nextEpoch then
            applyPendingDeposit deposit; return cont processed postpone
          else if validator.exitEpoch < Const.farFutureEpoch then
            return cont processed (postpone.push deposit)
          else if processed + deposit.amount > avail then
            return .done (true, processed, ndi, postpone)
          else applyPendingDeposit deposit; return cont (processed + deposit.amount) postpone
        | none =>
          if processed + deposit.amount > avail then return .done (true, processed, ndi, postpone)
          else applyPendingDeposit deposit; return cont (processed + deposit.amount) postpone
```

The spec writes this with two precomputed flags and one ladder:
`is_validator_withdrawn` and `is_validator_exited` default to false, are set only
when the pubkey is known, and a single branch then decides the action. Mirroring
that shape reads the validator once and writes the churn check once:

```lean
-- after
        -- Read the deposit's validator once, if its pubkey is known, and derive the two
        -- flags the spec branches on. An unknown pubkey leaves both false, so it falls
        -- through to the churn check.
        let (isWithdrawn, isExited) := match validatorIndexByPubkey? state deposit.pubkey with
          | some vi =>
            let v := sszGet state validators[vi]!
            (decide (v.withdrawableEpoch < nextEpoch), decide (v.exitEpoch < Const.farFutureEpoch))
          | none => (false, false)

        if isWithdrawn then applyPendingDeposit deposit; return cont processed postpone
        else if isExited then return cont processed (postpone.push deposit)
        else if processed + deposit.amount > avail then return .done (true, processed, ndi, postpone)
        else applyPendingDeposit deposit; return cont (processed + deposit.amount) postpone
```

The churn check lives in one place, and the ladder now reads as the reference does,
which is the §5 goal. The test for this case: a check appears in more than one arm,
and the reference computes the value the arms differ on (here, the two flags)
*before* it branches. When both hold, hoist that value out and write the shared
logic once. The flags are `decide (… < …)` because a `Prop`-valued comparison
cannot be stored and then matched in an `if`; `decide` is the same `Bool` the
inline `if … < … then` was producing implicitly.

### 5. Split by concern, preserving the reference's boundaries

The instinct from most codebases, a long function wants breaking up, holds here,
with one rule on top. Every package in this repo ports an external reference.
SizzLean and its cache implement the SSZ spec, LeanSha256 implements FIPS 180-4,
LeanPoseidon mirrors the Poseidon2 paper and the HorizenLabs zkhash crate, and
EthCLSpecs ports the consensus spec. When code ports a reference, preserve the
reference's function boundaries. A definition that maps 1:1 to a named reference
procedure stays auditable against it line by line. Carving it into private helpers
with no counterpart makes that audit harder.

So the trigger for splitting is the number of independent concerns, the nesting
depth, and reuse. Line count alone does not decide it. Paragraphing (§1) handles
"long but linear"; splitting handles "doing genuinely separate jobs."

#### When the split is free: the reference already decomposed

When the reference itself calls named sub-procedures, mirror that decomposition
with the same names. Readability and reference correspondence improve together.
Three instances across the repo:

- `permuteWith` (`LeanPoseidon/.../Permutation.lean:permuteWith`) factors out `sbox` (`:sbox`),
  `fullRound` (`:fullRound`), and `partialRound` (`:partialRound`), the same named operations zkhash
  uses (`sbox_p`, full rounds, partial rounds).
- `Node.ofShape` (`SizzLean/Cache/MerkleTree/Build.lean:Node.ofShape`) "mirrors
  `Spec.SSZType.hashTreeRoot` arm-for-arm", with `Node.subtreesForFields` (`:Node.subtreesForFields`)
  and `Node.subtreesForListComposite` (`:Node.subtreesForListComposite`) matching the spec's
  `hashTreeRootFields` / `hashTreeRootListComposite`.
- Gloas `getExpectedWithdrawals` (`EthCLSpecs/Gloas/Withdrawals.lean:getExpectedWithdrawals`) is
  composed from `getBuilderWithdrawals`, `getPendingPartialWithdrawals`,
  `getBuildersSweepWithdrawals`, and `getValidatorsSweepWithdrawals`, the same way
  the spec's `get_expected_withdrawals` is.

The mirror image is a warning. Do not import a *different* reference version's
decomposition. Fulu's `get_expected_withdrawals`
(`EthCLSpecs/Fulu/Withdrawals.lean:getExpectedWithdrawals`) is the Electra inline two-phase form, not
the Gloas four-helper form. Splitting it to match Gloas would read cleaner and
diverge from the Fulu spec. Paragraph it (§1) and keep the structure matching the
version being ported.

#### When the split earns itself: pure core out of the effectful shell

A high-value split the reference does not prescribe: separate a pure computation
from its monadic wrapper. `processJustificationAndFinalization`
(`EthCLSpecs/Fulu/EpochProcessing.lean:processJustificationAndFinalization`) reads the participating indices and
total balances, then hands the three balances to `weighJustificationAndFinalization`
(`:weighJustificationAndFinalization`), which does the bit and checkpoint logic. The spec inlines all of it. The
split isolates the part worth reading on its own from the plumbing that fetches its
inputs, and it makes the pure part testable in isolation. When a body holds a
cohesive sub-computation with a clean signature, values in and value out, ideally
with no `get` / `set`, that boundary is the seam.

#### When the language forces it

Some splits exist because Lean demands them, with no style motive. The
fuel-bounded loops `ppdLoop` (`EthCLSpecs/Fulu/EpochProcessing.lean:ppdLoop`), `pcLoop`
(`:pcLoop`), and `cbwsAux` (`EthCLSpecs/Fulu/Committees.lean:cbwsAux`) are extracted for
structural recursion. The `Node.ofShape` mutual block
(`SizzLean/Cache/MerkleTree/Build.lean`) is split into mutual helpers because Lean
4.29.1 rejects passing `Node.ofShape` itself as a higher-order argument, as its
"Why structural mutual recursion" note records. These helpers are tolerated
even when they take many parameters (`cbwsAux` threads eight). That parameter count
is itself a smell, and it is the price of the termination proof. Do not copy the
wide-parameter shape into splits that the language does not force.

What the language forces is the extraction and its parameter list, not a pass on
the body. A forced helper's body still follows §1 through §4 like any other; do not
read "Lean demanded this split" as "leave the body alone." `ppdLoop`'s realignment
to the spec's flag-then-branch shape (§4) happened inside exactly such a helper.

#### The cheapest split: a `where` clause

For a one-off helper used by exactly one function, prefer a `where` clause over a
top-level `def`. The helper stays invisible at namespace scope and reads as
subordinate to its parent, so the top level still presents as one reference
function. The codebase leans on this: `getHead.better`
(`EthCLSpecs/Gloas/ForkChoice.lean:getHead.better`), `filterBlockTree.go` (`:filterBlockTree.go`),
`addBuilderToRegistry.addressOfCred` (`EthCLSpecs/Gloas/Operations.lean:addBuilderToRegistry.addressOfCred`),
`onTickPerSlot.computeSlotsSinceEpochStart` (`:onTickPerSlot.computeSlotsSinceEpochStart`).

Promote a helper to namespace scope only when it is reused, mirrors a named
reference helper, or must be recursive. A good promotion-for-reuse candidate: the
`empty : BuilderPendingPayment` literal is written three times
(`EthCLSpecs/Gloas/Operations.lean:processProposerSlashing` and `:settleBuilderPayment`, `Gloas/EpochProcessing.lean:processBuilderPendingPayments`). One
`def emptyBuilderPendingPayment` would retire all three. Some duplication is forced
and should be left alone: `addressOf` is defined in both
`EthCLSpecs/Fulu/Withdrawals.lean:addressOf` and `Gloas/Withdrawals.lean:addressOf`, because the
two bodies bind to different per-fork `Validator` types, and the docstrings say so.

#### The EthCLSpecs instance: `forkdef` and `inherit`

EthCLSpecs is where the "preserve the reference's boundaries" rule bites hardest,
because two more mechanisms depend on the 1:1 mapping. The `inherit` mechanism
replays a fork's bodies into the next fork, so each helper promoted to namespace
scope joins the inherit surface the next fork has to manage (Gloas `EpochProcessing`
inherits roughly fifty Fulu defs). The conformance harness dispatches on handler
names that map 1:1 to the spec functions (the `OpKind` / `EpochStep` tags). A
`where` helper costs the next fork nothing and stays off the dispatch surface; a
promoted one does not. So in EthCLSpecs the bias toward keeping a spec function
whole, and toward `where` over promotion, is stronger than elsewhere.

#### Applied to the long ones

`processAttestation` (`EthCLSpecs/Gloas/Operations.lean:processAttestation`) is the case where both
tools apply. The committee-coverage check (the `(ok, offset)` fold) is a
self-contained validity computation with a clean boundary; lift it to a `where
verifyCommitteeCoverage` helper. The participation-flag loop that follows mutates
three accumulators together (`stateAcc`, `proposerNum`, `weight`), so extracting it
cleanly means returning a triple, which buys little. Leave that inline and
paragraph it (§1). The judgment is per-block: extract the parts with clean
signatures, keep the tangled-accumulator core in place.

### 6. Shape the state a loop threads

The rules so far target flat handlers. A loop that threads an accumulator (a
`fuelLoop`, a `fold`, a recursive scan) carries a second source of noise: the
plumbing of the state itself. `ppdLoop` (`EthCLSpecs/Fulu/EpochProcessing.lean:ppdLoop`),
the `process_pending_deposits` scan, threaded two near-identical positional 4-tuples
(one for the accumulator, one for the result), two counters, and a guard ladder
nested three `else` deep. The logic underneath is four early stops and a four-way
classify; the plumbing buried it. Three behavior-preserving moves clear it:

```lean
-- before
  fuelLoop (deposits.size + 1)
      ((0, (0 : Gwei), 0, (#[] : Array PendingDeposit)) :
        Nat × Gwei × Nat × Array PendingDeposit)
      ((false, (0 : Gwei), 0, (#[] : Array PendingDeposit)) :
        Bool × Gwei × Nat × Array PendingDeposit)
      fun (di, processed, ndi, postpone) => do
    if di ≥ deposits.size then return .done (false, processed, ndi, postpone)
    else
      let state ← get
      let deposit := deposits[di]!
      if (eth1-bridge gap) then return .done (false, processed, ndi, postpone)
      else if deposit.slot > finalizedSlot then return .done (false, processed, ndi, postpone)
      else if ndi ≥ Const.maxPendingDepositsPerEpoch then return .done (false, processed, ndi, postpone)
      else
        let cont (processed' : Gwei) (postpone' : Array PendingDeposit) := …
        …
```

```lean
-- after
forkstruct DepositScan where
  ndi          : Nat := 0
  processed    : Gwei := 0
  postpone     : Array PendingDeposit := #[]
  churnReached : Bool := false

  fuelLoop (deposits.size + 1) ({} : DepositScan) ({} : DepositScan) fun s => do
    if s.ndi ≥ deposits.size then return .done s
    let state ← get
    let deposit := deposits[s.ndi]!

    if (eth1-bridge gap) then return .done s
    if deposit.slot > finalizedSlot then return .done s
    if s.ndi ≥ Const.maxPendingDepositsPerEpoch then return .done s

    let advance (processed : Gwei) (postpone : Array PendingDeposit) : Step DepositScan DepositScan :=
      .next { s with ndi := s.ndi + 1, processed, postpone }
    …
```

#### Name threaded state with a record, not a positional tuple

A `(Bool × Gwei × Nat × Array …)` accumulator turns every `.done (false, processed,
ndi, postpone)` into a position-counting exercise, and two tuples of the same shape
(here the accumulator led with `Nat`, the result with `Bool`) are a trap: the reader
has to notice they differ. A record with named fields ends both. `fuelLoop`'s
accumulator and result types may be the *same* type, so one `DepositScan` serves both,
and `{}` (all field defaults) replaces the two giant inline `(… : Nat × Gwei × Nat ×
Array …)` annotations. Past two components, a tuple is an unnamed record; name it.
This is §2 applied to composite state.

Inside a fork spec the record is a `forkstruct`, not a plain `structure`, so it carries
the uniform `[Preset]` binder every container has and is captured for replay. A sibling
fork that overrides the loop (Gloas has its own `ppdLoop`) adds `inherit DepositScan`
rather than restating the fields, the same way it inherits any other declaration. Apply
the record one place and both forks read in field names.

#### Thread the minimum: drop state that moves in lockstep

`ppdLoop` threaded `di` (the cursor) and `ndi` (`next_deposit_index`) separately, yet
every step advanced both by one or stopped on neither, so they were always equal. Two
names for one value cost the reader a question with no answer, "when do these differ?".
They never do, so collapse them to one. Before adding a field to an accumulator, check
it is not a copy of one already there. This is §4 for state: the repeated thing is the
variable itself, not an expression.

#### Let guard clauses stand flat

In a `do` block, `if c then return …` short-circuits, so a precondition need not wrap
the rest of the body in its `else`. The three early stops sat nested three `else` deep;
as flat `if … then return .done s` lines they read as a checklist, and the real work
un-indents. Keep the two-armed `if … else` (and §1's "inside a branch" paragraphing)
for branches where both arms do real work; a guard that only exits is cleaner flat.

The payoff is in the caller too: `let scan ← ppdLoop …` then `scan.ndi` /
`scan.churnReached` reads as English, where the old `let (churnReached, processed,
ndi, postpone) ← …` made the call site re-declare the tuple shape.

### 7. Leave the small ones alone

Over-application is its own smell. Most files are full of short pure helpers that
are already at their best. These need no blank lines, no internal comments, no
extra locals:

```lean
forkdef getCurrentSlot (store : Store map) : Slot := Const.genesisSlot + getSlotsSinceGenesis store

forkdef isBuilderIndex (vi : ValidatorIndex) : Bool := (vi &&& Const.builderIndexFlag) != 0

def sbox (x : R) : R := let x2 := x * x; x2 * x2 * x

forkdef calculateCommitteeFraction (state : State) (committeePercent : UInt64) : Gwei :=
  let committeeWeight := (getTotalActiveBalance state) / UInt64.ofNat Const.slotsPerEpoch
  committeeWeight * committeePercent / 100
```

The signature plus docstring already says everything. A single expression, or a
two-line `let` that reads straight through, is one paragraph by definition.

Heuristics for restraint:

- **Under ~8 lines of body, one logical step:** no internal structure. One
  paragraph, no headers.
- **Blank lines mark phases, not statements.** A blank line between every line
  reads as visual stutter. Group, then break between groups.
- **A comment per three to six lines, at most.** If a function wants a comment on
  every other line, it is too dense and wants splitting into helpers (§5, the
  `where`-clause pattern in `getHead` and `filterBlockTree`).
- **Stop expanding names when the short form mirrors the reference.** See §2.

### Where the payoff is largest

The packages outside EthCLSpecs are largely already at the bar: `permuteWith` and
`Node.ofShape` are positive models, not work items. The densest backlog is in
EthCLSpecs, ranked by density and call-site importance:

1. `processAttestation` (Gloas `Gloas/Operations.lean:processAttestation`, Fulu
   `Fulu/Operations.lean:processAttestation`) — paragraphing + phase headers (§1), and lift the
   committee-coverage fold to a `where` helper (§5).
2. `getExpectedWithdrawals` (Gloas `Gloas/Withdrawals.lean:getExpectedWithdrawals`) — tuple-thread
   naming (§2); (Fulu `Fulu/Withdrawals.lean:getExpectedWithdrawals`) — blank-line phases (§1).
3. `advanceStoreTime` (`Gloas/ForkChoice.lean:advanceStoreTime`) — lift + dedup the slot formula
   (§4).
4. `process_withdrawals` cursor update (`Gloas/Withdrawals.lean:processWithdrawals`) — collapse the
   duplicated guard (§4).
5. `processConsolidationRequest` (`Fulu/Operations.lean:processConsolidationRequest`) and
   `processWithdrawalRequest` (`Fulu/Operations.lean:processWithdrawalRequest`) — long `else if` ladders
   that would read better with a one-line header naming the validity gate they
   walk.
6. `getHead.better` (`Gloas/ForkChoice.lean:getHead.better`) — the `wa` / `wb` rename (§2),
   small, and it is the exact pattern to standardize on.

The big `forkdef` epoch substeps (`weighJustificationAndFinalization`,
`processSlashings`, `processEffectiveBalanceUpdates`) are already close: each is one
phase with a clear `Id.run do` accumulator. They mostly want the §2 name
expansions.

### Checklist for a body

When writing or revising a function body:

- More than one phase? Separate phases with a blank line.
- A block implements a named reference step or a phase? One header comment naming
  it.
- A local invented for this function? Name it for what it holds, not its type.
- A local that mirrors a reference parameter, or a fixed idiom (`hb`)? Leave it
  short.
- An expression spanning more than a line, or repeated? Lift it to a named `let`.
- Several independent concerns, deep nesting, or a block reused elsewhere? Split by
  concern, a `where` clause for one-offs, keeping each piece mapped to a reference
  function or helper.
- A comment that restates its line, or just labels an obvious paragraph? Delete it.
  The blank line carries the paragraph; the header is only for the non-obvious.
- Threading an accumulator? Name it with a record, not a positional tuple past two
  fields; check no two components move in lockstep; let exit-only guards stand flat.
- Under ~8 lines, one step? Leave it as one paragraph.

The bar is the one CLAUDE.md sets for the rest of the project: a reader who knows
one side of the intersection but not the other should be able to follow the body
top to bottom on first read.
