# Formal-verification proof targets

A menu of proof targets across Etheorem, the SSZ layer, the consensus containers,
and the fork framework. Every target points at code already in the tree and says
whether one of the two prior beacon-chain efforts left a template for it, or whether
it's new ground. They're grouped into four tiers by area and tagged by how novel and
how hard I think each one is.

This is a working doc. I'll reshuffle targets as work lands.

## Prior art

Two earlier efforts verified chunks of the beacon chain, both outside Lean 4. What
they closed tells us what's tractable. What they punted on is where the interesting
work is.

### ConsenSys eth2.0-dafny (Dafny, Phase 0, archived)

- SSZ round-trip proved for the non-composite shapes: `seDesInvolutive`
  (`deserialise(serialise s) = s`), `serialiseIsInjective`, and the per-type SeDes
  lemmas, bitlist and bitvector included. Both central lemmas carry
  `requires !(s.Container? || s.List? || s.Vector?)`, so containers, lists, and
  vectors sit outside them. Composite round-trip is open ground for everyone.
- Merkleization: only the chunk-count and length bookkeeping proved. Root-equals-spec
  stays differential-tested. `hash()` is uninterpreted.
- State transition proved as refinement. Every `process_*` method carries
  `ensures s' == update*(s)`, with slot monotonicity and validator/balance length
  sync.
- Overflow bounds assumed, not proved: balance sum `< 2^64`, deposit index
  `+1 < 2^64`, registry `<= VALIDATOR_REGISTRY_LIMIT` all ride on `{:axiom}`
  `Assume*Overflow` lemmas ("This proof is assumed", per their docstrings). The
  transition proofs hold modulo those assumptions; discharging them is open.
- Committee-size bounds (`ActiveValidatorBounds`).
- Fork-choice store invariants: `aValidStoreIsAChain`, slot-monotone ancestry,
  accepted-block immutability. No liveness. `filter_block_tree` unimplemented.
- Casper FFG accountable safety (`lemma5`, on the `goal1` branch, never merged to
  master): conflicting finalized and justified checkpoints imply a `1/3` slashable
  set, under a fixed validator set.
- Never built `is_valid_merkle_branch`. Shuffling stubbed to identity, so no
  permutation proof. BLS unimplemented.

### Runtime Verification (K + Coq)

- Deposit-contract incremental Merkle tree: a full proof that the incremental root
  equals the naive full-tree root, plus KEVM bytecode refinement against an untrusted
  compiler, which surfaced real bugs. This is the canonical incremental-Merkle result.
- Phase 0 state transition: an executable K model, conformance-tested against the
  official vectors, not proved.
- Gasper in Coq: accountable safety, plausible liveness, and the slashable bound, with
  dynamic validator sets, on an abstract model rather than the executable spec.
- The bridge from the K state-transition model up to Gasper: ongoing, incomplete.
- Shuffling and rewards/penalties: not independently proved.

### Adjacent efforts

- Apalache / TLA+: bounded model-checking of 3SF (three-slot-finality) accountable
  safety (Konnov et al. 2025). It checks the property up to a bound, so it finds
  counterexamples rather than proving the general case, complementary to a deductive
  D2 proof.
- Nyx Foundation `formal-leanSpec`: a parallel Lean 4 formalization, with its own SSZ
  layer, of the post-quantum leanSpec (the Beam-chain minimal spec). It tracks the
  future PQ spec where Etheorem tracks the production consensus spec, so the two run
  alongside each other.

### Takeaways

1. SSZ round-trip on the non-composite shapes and refinement invariants are
   known-tractable; Dafny closed both, so we can lean on their shape. Their overflow
   bounds were assumed via axiom lemmas, so actually proving those is still open.
2. `is_valid_merkle_branch` soundness and shuffle-is-a-permutation are open ground.
   Neither effort proved either, so that's where the novelty is.
3. Our one real edge over both: a verified SHA-256 (`LeanSha256` plus the
   FFI-equivalence axioms) and the Poseidon2 proofs. Where Dafny and K could
   only differential-test merkleization soundness, we can close it against a
   concrete hash.

## Current proof surface

The crypto layer is well proved. Roughly 65 SizzLean theorems (round-trip over
`BasicSupported`, size bounds, injectivity, bit packing, wide-integer codec), 48
Poseidon2, and 23 SHA-256, with zero `sorry`. The axiom footprint is small and named: two
field-primality axioms (`bn254FrModulus_prime`, `blsFrModulus_prime`, LeanPoseidonProofs) and
the three-axiom SHA-256 bridge (`sha256Hash_eq_spec`, `sha256Combine_eq_spec`,
`sha256BatchCombine_eq_spec`, SizzLean), each visible through `#axioms` on any dependent proof.
The Merkle-branch completeness work is symbolic, so it adds none.
The narrow `uintN` arms (8 through 64) close by `bv_decide`, so `Lean.ofReduceBool`
(the compiler axiom) is in that footprint. The wide 128 and 256 arms (PR #18) close by
`Nat`-digit induction and add no axiom.

The consensus layer is mostly bare. Two proof sites sit on main: `uint64ModOfNatToNatLt`,
and the three `bv_decide` builder-index round-trip theorems PR #16 landed
(`EthCLSpecs/Proofs/BuilderIndex.lean`). Alongside them, off main, the in-progress
Merkle-branch stack (roughly 21 theorems in EthCLLib), around 40 `#guard` and
`native_decide` property checks, and roughly 60 `forkdef` state functions with no proofs
attached. A curated function-level candidates list for the Gloas surface lives in
[`CONSENSUS_PROOF_CANDIDATES.md`](../packages/EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md);
it complements this roadmap one altitude down, per-function where this doc is
per-tier.

A4 is the worked example, already started. The `isValidMerkleBranch` completeness proof
shows a passing verifier accepts the honest opening over a real Merkle tree, down to the
pure-Lean `LeanSha256`, symbolically. Its extension to the mix-in-length root that `processDeposit`
checks is in progress, the prerequisite for **C1**'s deposit arm.

A structural fact shapes the SSZ tier. `SizzLean.Proofs.decode_encode` is
proved over `SSZType.BasicSupported`, which covers every fixed-size shape. PR #18 closed
the last integer widths (`uintN 128/256`, `Proofs/UIntWide.lean`), and `Proofs/BitPack.lean`
folded in the two bit shapes: `packBitsLE_unpackBitsLEAux_inverse` is proved and the
`bitvector`/`bitlist` arms of the central theorems are closed. Variable-size containers
and variable-size lists sit outside `Supported` (the decoder returns `.error` for them);
fixed-element lists are covered and proved (`decode_encode_listFixed`), and `Union` is
not an `SSZType` constructor at all, so it cannot even be stated yet.

## Targets

Legend. Prior art: ✅ template exists, ⚠ partial, ★ greenfield. Difficulty (a guess): L, M, H.

### Tier A, SSZ and merkleization

- **A4 `is_valid_merkle_branch` completeness** ★ M. An honest inclusion proof is always
  accepted by the verifier, over a real Merkle tree down to the pure-Lean `LeanSha256`. Started (see the
  status paragraph above), symbolic and axiom-clean. The worked Tier A example.
- **A2 bit-packing round-trip** ★ M. Done for the proved direction:
  `packBitsLE_unpackBitsLEAux_inverse` (PR #10, `Proofs/BitPack.lean`) recovers
  the input bits from their packed bytes, up to false-padding (bits→bytes→bits).
  The byte-side composition (`packBitsLE` after unpacking arbitrary bytes) has
  no standalone identity and `unpackBitsLE` exists only as the `Aux` form.
- **A1 round-trip on bitvector and bitlist** ⚠ M. Done: PR #10 closed both arms of
  `decode_encode` and folded the bit shapes into `BasicSupported`.
- **A5 `merkleRootWithCache ≡ hashTreeRoot`** ⚠ M. The cached tree agrees with the spec
  merkleization.
- **A6 zero-hashes tower** and **A7 chunk and length plumbing** ⚠ L–M. The padding and
  chunking bookkeeping Dafny proved.
- **A9 generalized-index library** ★ M. Decompose `get_generalized_index` and
  `get_subtree_index` into the `(depth, index)` pair the merkleization theorems take, and
  bridge a gindex opening to that pair. Greenfield: neither prior effort built it. In
  progress. The `(depth, index)` decomposition (`gindex_decompose`,
  `getSubtreeIndex`) and `getPowerOfTwoCeil` are proved and axiom-clean;
  `getGeneralizedIndex` over `SSZType` is modeled but still miscomputes the chunk position
  for packed vectors and lists (it reads the raw element index), so that arm is still
  unfinished.
  This is the enabling dependency for every Merkle-proof consumer past deposits: the
  light-client header branches and the blob and data-column sidecar inclusion proofs all
  address leaves by generalized index rather than raw tree position, so each of them waits
  on A9. Deposits skip it, their index is a plain tree position.

### Tier B, shuffling and committees

Greenfield, high novelty. Neither prior effort proved a real shuffle. Determinism
needs no target here: the shuffle is a pure function, so same seed, same permutation
holds definitionally, where the informal efforts had to state it as a property.

- **B1 `computeShuffledPermutation` is a bijection** on `[0, count)`.
  `EthCLSpecs/Fulu/Committees.lean`. ★ M–H. The flagship result. Dafny stubbed the
  shuffle to identity, so no one has proved this.
- **B2 committee partition**: the union of committees is the active set, pairwise
  disjoint. Follows B1. ★ M.
- **B3 sampler termination**: the balance-weighted 10M-fuel bound always suffices. ★ M.

### Tier C, state-transition invariants and bounds

The Dafny-proven pattern: templates exist for the statements, but C1's proofs were
assumed there (`{:axiom}`), not carried out.

- **C1 overflow safety**: `increaseBalance` never wraps, total balance `< 2^64`, deposit
  index `+1 < 2^64`, registry `<= VALIDATOR_REGISTRY_LIMIT`.
  `EthCLSpecs/Fulu/{Balances,Operations}.lean`. ⚠ M. Dafny stated these bounds but
  assumed them via `{:axiom}` lemmas, so the template covers the statements, and the proofs
  themselves are new work.
- **C2 slot/epoch round-trip and monotonicity**: `computeEpochAtSlot
  (computeStartSlotAtEpoch e) = e` for `e < 2^59` (the raw `UInt64` multiply
  wraps above that, so the identity is false unbounded), plus slot
  monotonicity. `EthCLSpecs/Fulu/Time.lean`. ✅ M; the bound hypothesis is where the
  work hides.
- **C3 length invariant**: `|validators| = |balances|` preserved across transitions. ✅ M.
- **C4 committee-size bounds**: an active count in `[32, 2^22]` implies sizes in `(0, MAX]`.
  `EthCLSpecs/Fulu/Committees.lean`. ✅ (Dafny `ActiveValidatorBounds`). M.
- **C5 `isSlashableAttestationData` = spec** (double-vote or surround), with the
  `strictlySorted` well-formedness. `EthCLSpecs/Fulu/Operations.lean`. ⚠ M.
- **C6 registry-update legality**: a validator flows active to exited at most once, churn
  `<=` churn_limit. `EthCLSpecs/Fulu/EpochProcessing.lean`. ⚠ H.

### Tier D, deep consensus

Research-scale.

- **D1 fork-choice store invariants**: a valid store is a chain, ancestry slot-monotone,
  accepted blocks immutable. `EthCLSpecs/Fulu/ForkChoice.lean`.
  ✅ (Dafny `aValidStoreIsAChain`). M. The best entry into Tier D.
- **D2 Casper FFG accountable safety**: conflicting finalized and justified checkpoints
  imply a `1/3` slashable set. Needs an abstract FFG layer over
  `EthCLSpecs/Fulu/EpochProcessing.lean`.
  ✅✅ (Dafny `goal1` and RV Coq). H. Both prior efforts closed it, Dafny under a fixed
  validator set and RV Coq under dynamic sets, so it is hard yet demonstrably reachable.
  Apalache also bounded-model-checked the 3SF form (Konnov et al. 2025), up to a bound. A
  Lean version would be a headline result. One approach: extract an abstract
  checkpoint/justification-link model from the epoch-processing functions, prove the
  two-quorum intersection argument on that, then bridge the abstract model back to
  `EthCLSpecs/Fulu/EpochProcessing.lean` by refinement.
- **D3 plausible liveness**: with `>= 2/3` honest, new finalization stays possible. ✅
  (RV Coq, dynamic sets). Very H. Sits behind D2 and shares the abstract FFG model D2
  builds.
- **D4 Heze/FOCIL inclusion-list validity**: a satisfied inclusion list forces the required
  transactions into the block. ★ M–H.

## By function

The same targets, resolved to the concrete definitions they're about, in the layout
[`CONSENSUS_PROOF_CANDIDATES.md`](../packages/EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md)
uses, so the two docs compare side by side. Line numbers are as of this commit and will drift.

Several candidate rows over there are the same work as targets here: the churn
no-underflow candidates (`computeExitEpochAndUpdateChurn`, `reserveChurn`) are C6, the
fork-choice monotonicity and base-case candidates (`updateCheckpoints`,
`onAttesterSlashing`, `getForkchoiceStore`, `getHead`/`getWeight` determinism) sit
inside D1, and `initiateBuilderExit`'s unguarded exit-epoch arithmetic is a
C1-shaped overflow statement on the Gloas side.

### Tier A

| Target | Function(s) | Location | Status |
| ------ | ----------- | -------- | ------ |
| A4 | `isValidMerkleBranch` | `EthCLLib/Spec/SigningRoot.lean:68` (the verifier) | started; the completeness proof is not yet in-tree |
| A2 | `packBitsLE`, `unpackBitsLEAux` | `SizzLean/Spec/Serialize.lean:223`, `SizzLean/Spec/Deserialize.lean:178`, proof in `SizzLean/Proofs/BitPack.lean` | done |
| A1 | `decode_encode`, bit arms | `SizzLean/Proofs/Roundtrip.lean`, arms in `SizzLean/Proofs/BitPack.lean` | done |
| A5 | `hashTreeRoot` vs `Node.merkleRootWithCache` / `Node.merkleRoot`, `hashTreeRootCached` | `SizzLean/Spec/HashTreeRoot.lean:504`, `SizzLean/Cache/MerkleTree/Merkle.lean:52`, `SizzLean/Cache/TreeBacked.lean:306` | open; reuses the perfect-tree kit shared with the A4 stack |
| A6 | `zeroHashes` (private) | `SizzLean/Cache/MerkleTree/Zero.lean:107` | open |
| A7 | `padToChunk`, `chunkDepth`, `mixInLength` (private) | `SizzLean/Spec/HashTreeRoot.lean:100,288,302` | open |
| A9 | `getGeneralizedIndex`, `getSubtreeIndex`, `floorLog2`, `getPowerOfTwoCeil` | not yet in-tree | in progress; decomposition + `getPowerOfTwoCeil` proved, `getGeneralizedIndex` packed-position fix pending |

### Tier B

All in `EthCLSpecs/Fulu/Committees.lean`.

| Target | Function(s) | Location | Status |
| ------ | ----------- | -------- | ------ |
| B1 | `computeShuffledPermutation` | `Committees.lean:32` | open |
| B2 | `getBeaconCommittee`, on top of B1 | `Committees.lean:83` | open |
| B3 | `computeBalanceWeightedSelection` (the 10M-fuel call is at `:121`) | `Committees.lean:114` | open |

### Tier C

| Target | Function(s) | Location | Status |
| ------ | ----------- | -------- | ------ |
| C1 | `increaseBalance`, `processDeposit`, `processRegistryUpdates` | `Fulu/Balances.lean:29`, `Fulu/Operations.lean:214`, `Fulu/EpochProcessing.lean:165` | open; its deposit-arm Merkle prerequisite (the mix-in-length extension) is in progress, the overflow bounds are not started |
| C2 | `computeEpochAtSlot`, `computeStartSlotAtEpoch` | `Fulu/Time.lean:25,28` | open |
| C3 | `processDeposit` (the append site), then transition-wide preservation | `Fulu/Operations.lean:214` | open; rests on the in-progress mix-in extension, not started |
| C4 | `getBeaconCommittee` | `Fulu/Committees.lean:83` | open |
| C5 | `isSlashableAttestationData`, `strictlySorted` | `Fulu/Operations.lean:38,30` | open |
| C6 | `processRegistryUpdates`, `initiateValidatorExit`, `computeExitEpochAndUpdateChurn` | `Fulu/EpochProcessing.lean:165`, `Fulu/RegistryUpdates.lean:112,78` | open |

### Tier D

| Target | Function(s) | Location | Status |
| ------ | ----------- | -------- | ------ |
| D1 | `getAncestor`, `getHead`, `onBlock` (Gloas twins at `Gloas/ForkChoice.lean:156,446,594`) | `Fulu/ForkChoice.lean:105,200,387` | open |
| D2, D3 | `processJustificationAndFinalization`, behind an abstract FFG layer | `Fulu/EpochProcessing.lean:69` | open |
| D4 | `processInclusionList`, `isPayloadInclusionListSatisfied` | `Heze/ForkChoice.lean` (PR #6, in review) | open; workable now on the in-flight Heze layer, against the current alpha |

## Dependencies and entry points

No strict order here. Some targets rest on others, some are gentler first steps.

- A4 shows the merkleization-completeness shape end to end (status above). A1 and A2 have
  since landed on main, which leaves A5 as the natural next SSZ extension.
- A4 is load-bearing beyond Tier A. `processDeposit` accepts a deposit only behind the
  `isValidMerkleBranch` assert (`Fulu/Operations.lean:216`),
  so C1's deposit arm and C3 lean on the completeness theorem *plus a mix-in-length
  extension*: the deposit root mixes in the list length, so it isn't a plain perfect tree
  and the base theorem doesn't cover it. That extension is in progress, stated general over
  depth so the sidecar inclusion proofs reuse it, a blob or data-column commitment opens a
  `List` element that crosses the same length-mix-in node. A5 reuses the same perfect-tree
  kit. The `DataColumnSidecar.kzgCommitmentsInclusionProof` field (`Fulu/Blocks.lean:63`)
  is the other branch-proof consumer, not modeled yet.
- Tier C holds the quick wins. C1 and C2 are small, self-contained, and follow the Dafny
  template closely.
- B1 is the flagship shuffle result. B2 and B3 cluster around it, and B2 follows B1
  directly.
- D1 is the doorway into deep consensus and ties into the fork-choice work. D2 is the
  long-arc goal of accountable safety, and D3 shares the abstract FFG model D2 builds. D4
  follows the FOCIL work.

Both prior efforts closed accountable safety in their own settings, so I'm keeping D2 and
D3 on the list as reachable, although it's arguably deeper research.
