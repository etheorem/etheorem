# The Specs Architecture

This document describes the per-fork specs, Fulu first and Gloas as a diff over
it, for the Lean 4 consensus-spec library. It sits above its two siblings.
`SPEC_AUTHORING_MODEL.md` is the contract: it draws the line between what a spec
author writes and what the framework supplies, carries the canonical glossary,
and states the author/framework boundary table. `FRAMEWORK_ARCHITECTURE.md`
builds each "framework generates" cell of that table from below. This document
uses both from the author's side: it shows how the Fulu and Gloas specs are
organized, ported, tested, and eventually proved, written against the contract
and on top of the machinery. Read `SPEC_AUTHORING_MODEL.md` first. This document
quotes its glossary rather than re-coining terms, and cross-references both
siblings by section title so the links resolve.

A consensus spec sits at a small intersection. A reader fluent in the Python
`pyspec` may not have written Lean; a reader fluent in Lean may not know what
`process_epoch` does. This document teaches both sides as it goes. Where a spec
term needs grounding it gets a sentence; where a Lean idiom is load-bearing it
gets one too.

The thesis it earns: the spec author writes consensus logic and nothing else.
The module layout, the inheritance, the two configurations, and the conformance
wiring all fall out of the contract, so a fork is a clean port of the upstream
behavior with the plumbing tucked away.

---

## 1. Scope and goals

The library targets two forks in order. Fulu first, as the base. Gloas second,
as a diff over Fulu through the inheritance mechanism that
`SPEC_AUTHORING_MODEL.md` defines in its fork-declaration-model section. The
order is forced. A later fork is delivered as a diff over its parent, and Gloas's
parent is Fulu, so Fulu has to exist whole before Gloas can diff it.

### 1.1 The surface per fork

Each fork delivers the six deliverables of the contract's
what-a-fork-spec-is section, drawn from the upstream specification. The surface
that is in scope:

| In scope | Out of scope |
|---|---|
| `beacon-chain` (containers, helpers, state transition, epoch processing, operations) | the validator guide's honest-behavior duties |
| `fork-choice` (the `Store` and its `on_*` handlers) | the p2p networking layer |
| the `fork` upgrade and `genesis` construction | |
| Fulu's PeerDAS additions (EIP-7594) | |
| Gloas's ePBS additions (EIP-7732) | |

The domain line of the contract's domain-line section sets this boundary. A
helper that names a consensus concept is spec-owned and in scope; the validator
guide's duties and the network layer name no state-transition concept the
conformance vectors check, so they stay out.

Within Fulu, the core state transition and fork-choice land before the PeerDAS
data-availability surface, because data-availability needs KZG cell verification
and the KZG primitive is the latest-bound dependency. Building the transition
first lets it pass vectors while the crypto backend comes online behind the
`[CryptoBackend]` seam.

### 1.2 Both presets, minimal first

Both `minimal` and `mainnet` presets are supported from the start, through the
preset tier system that `FRAMEWORK_ARCHITECTURE.md` builds in its
preset-constant-config-tier-system section. Minimal comes first for fast
iteration: its smaller vector widths and shorter epochs make a failing vector
quick to reproduce. Mainnet vectors exist for both forks and run on demand rather
than on every push, since they are slower. The preset machinery carries both from
day one, so mainnet is a CI-schedule choice, never a missing capability.

### 1.3 The definition of "done"

A fork is done when two conditions hold together. It satisfies the fork interface
that the contract's inverted-conformance-contract section fixes, so the build
proves every entry point is present and correctly signed. And `PySpecTests`, the
conformance layer of `FRAMEWORK_ARCHITECTURE.md`'s conformance-framework section,
is green on every in-scope format at both presets. A `todo` stub or a
spec-faithful-mode annotation counts as a documented gap, never a silent pass: a
vector that reaches one fails loudly and points to the work. Conformance is the
goal for the first milestone; proofs are deferred (Section 9).

### 1.4 Excluded formats

Three vector formats are excluded: `ssz_static`, `bls`, and `kzg`. Each tests a
primitive the framework or a dependency owns, the SSZ serialization, the BLS
signature scheme, the KZG commitment scheme, rather than consensus logic the spec
author writes. They are a framework-library concern, checked by SizzLean's own
suite and the crypto backend's suite, so the spec does not re-run them. KZG the
primitive still lives behind the `[CryptoBackend]` seam, where Fulu's PeerDAS
paths call it; only the standalone `kzg` test format is out of scope. The
primitive is exercised through in-scope spec paths, never in isolation.

---

## 2. The accumulated-Fulu and Gloas-diff strategy

### 2.1 Fulu is the whole accumulated spec

The conceptual lineage runs Electra to Fulu to Gloas: Fulu is Electra plus
PeerDAS, Gloas is Fulu plus ePBS. That chain is useful as documentation. The
implemented diff realizes only part of it. Fulu is the base, authored whole;
Gloas is the one implemented diff over it.

"Authored whole" means the whole accumulated spec, not a small Fulu delta. The
consensus spec is cumulative. By Fulu, the state transition and fork-choice have
absorbed every prior fork: Phase 0 through Altair's sync committees, Bellatrix
and Capella's execution payload and withdrawals, Deneb's blobs, Electra's churn
and pending-deposit machinery, then Fulu's PeerDAS on top. None of those forks is
built as a separate layer. Fulu is the entire accumulated state transition and
fork-choice as of Fulu, authored as one snapshot. That is the heavy lift. Gloas
is the comparatively small ePBS diff over that base.

### 2.2 The port is driven off the generated Python

The accumulation is not done by hand, and the port is not driven off the
specification markdown alone. The upstream pyspec build system flattens the
layered markdown into a complete per-fork Python module, the authoritative,
disambiguated, executable form the vectors are generated from. That generated
`fulu` Python module is the porting source, with the markdown read for intent
where the Python is terse.

The generated module also defines the scope. Whatever it contains is what Fulu
needs, so there is no manual pruning of which prior-fork machinery to include. The
Gloas manifest of inherited, overridden, and new declarations is derivable by
diffing the generated `fulu` and `gloas` Python modules, computed rather than
hand-derived. The behavioral-conformance freedom that the contract's
authoring-style section grants means the Lean rendering follows what reads
naturally and answers only to the vectors, so the port re-expresses the Python's
behavior in idiomatic Lean rather than transcribing its file structure.

### 2.3 The PeerDAS and ePBS surface sketches

The two diffs have a recognizable shape.

Fulu's PeerDAS surface over Electra adds the `DataColumnSidecar` and `MatrixEntry`
containers, the fork-choice data-availability check `isDataAvailable`, and KZG
cell verification, the primitive that sits behind `[CryptoBackend]`. The
data-availability check reads which columns a node has and asks the KZG backend to
verify their cell proofs.

Gloas's ePBS diff over Fulu is larger. It adds the builder registry (the
`builders` field on `BeaconState`, the `Builder`, `BuilderPendingPayment`, and
`BuilderPendingWithdrawal` containers), the execution-payload bid
(`ExecutionPayloadBid`), the payload-timeliness committee (the `ptcWindow`
accessors, the `PayloadAttestation` container, the `processPayloadAttestation`
operation), the `executionPayloadAvailability` tracking on the state, a
restructured block-processing pipeline (the execution payload is revealed
separately under ePBS, so `processBlock` changes its step order), and the
payload-aware fork-choice fields on the `Store`. Building Fulu first lands the KZG
primitive and the data-availability surface before ePBS arrives, so Gloas inherits
both.

---

## 3. The module layout

Containers are declared in-spec through `forkcontainer`, the container front-end
of `FRAMEWORK_ARCHITECTURE.md`. There is no separate container library. The
organizing principle is cohesion and idiomatic Lean, the literate-by-default
principle of the project, rather than mirroring the pyspec's section order. The
spec re-expresses the same behavior in Lean and is free to group it by what reads
naturally.

### 3.1 The file order is the dependency order

Lean has no forward references, so a file can only mention names that an earlier
file in import order has defined. The file order is therefore the dependency
order. `BeaconState` references almost every container, so it sits low in the
order, and the operations on it sit below that. The layout falls into five layers,
loaded in this order: foundations, the component containers, the state, the state
operations, and fork choice.

The table below is the full Fulu fork in load order. Gloas is the same skeleton
through the fork diff, minus the PeerDAS-specific files where ePBS supersedes
them, plus the ePBS files.

| # | File | Layer | Contains |
|---|------|-------|----------|
| 1 | `Types` | foundations | Consensus type aliases (`Slot`, `Epoch`, `ValidatorIndex`, `Gwei`, `Root`, `BLSPubkey`, `ParticipationFlags`) over SizzLean basic types and crypto-backend types |
| 2 | `Constants` | foundations | Universal constant values (`GENESIS_SLOT`, `FAR_FUTURE_EPOCH`, domain tags, flag bits) and the spec's use of `[Preset]` / `[Config]` through `Const.*` |
| 3 | `Containers/Fork` | containers | `Fork`, `ForkData` |
| 4 | `Containers/Checkpoint` | containers | `Checkpoint` |
| 5 | `Containers/Validator` | containers | `Validator` plus `State`-free predicates (`isActiveValidator`, `isSlashableValidator`, `isEligibleForActivationQueue`) |
| 6 | `Containers/Eth1Data` | containers | `Eth1Data` |
| 7 | `Containers/BeaconBlockHeader` | containers | `BeaconBlockHeader`, `SignedBeaconBlockHeader` |
| 8 | `Containers/Attestation` | containers | `AttestationData`, `IndexedAttestation`, `Attestation` |
| 9 | `Containers/Slashing` | containers | `ProposerSlashing`, `AttesterSlashing` |
| 10 | `Containers/Deposit` | containers | `DepositMessage`, `DepositData`, `Deposit` |
| 11 | `Containers/Exit` | containers | `VoluntaryExit`, `SignedVoluntaryExit` |
| 12 | `Containers/Sync` | containers | `SyncCommittee`, `SyncAggregate` |
| 13 | `Containers/Withdrawal` | containers | `Withdrawal`, `BLSToExecutionChange`, `HistoricalSummary` |
| 14 | `Containers/Execution` | containers | `ExecutionPayload`, `ExecutionPayloadHeader`, `ExecutionRequests` plus request types |
| 15 | `Containers/PendingOps` | containers | `PendingDeposit`, `PendingPartialWithdrawal`, `PendingConsolidation` |
| 16 | `Containers/DataColumn` | containers | (Fulu / PeerDAS) `DataColumnSidecar`, `MatrixEntry` |
| 17 | `Containers/BeaconBlockBody` | containers | `BeaconBlockBody` |
| 18 | `Containers/BeaconBlock` | containers | `BeaconBlock`, `SignedBeaconBlock` |
| 19 | `State` | state | `BeaconState` definition only; imports all of the containers |
| 20 | `Time` | operations | `getCurrentEpoch`, `getPreviousEpoch`, `computeEpochAtSlot`, `computeStartSlotAtEpoch`, `computeActivationExitEpoch` |
| 21 | `Signing` | operations | `computeDomain`, `computeSigningRoot`, `getDomain` |
| 22 | `Randao` | operations | `getRandaoMix` |
| 23 | `Balances` | operations | `increaseBalance`, `decreaseBalance`, `getTotalBalance` |
| 24 | `Registry` (accessors) | operations | `getActiveValidatorIndices`, churn-limit accessors |
| 25 | `Committees` | operations | `getSeed`, `computeCommittee`, `getBeaconCommittee`, `computeProposerIndex`, `getBeaconProposerIndex` |
| 26 | `Accessors` (derived) | operations | `getTotalActiveBalance`, `getUnslashedParticipatingIndices`, `getAttestingIndices` (float-ups over rows 23, 24, 25) |
| 27 | `Predicates` | operations | `isValidIndexedAttestation`, `isEligibleForActivation`, `isSlashableAttestationData` |
| 28 | `Registry` (mutators) | operations | `initiateValidatorExit`, `slashValidator` |
| 29 | `Rewards` | operations | flag-index deltas, inactivity-penalty deltas |
| 30 | `Withdrawals` | operations | `getExpectedWithdrawals` |
| 31 | `EpochProcessing` | operations | `processEpoch` plus the generated-`fulu` substep set in order: `processJustificationAndFinalization`, `processInactivityUpdates`, `processRewardsAndPenalties`, `processRegistryUpdates`, `processSlashings`, `processEth1DataReset`, `processPendingDeposits`, `processPendingConsolidations` (Electra), `processEffectiveBalanceUpdates`, `processSlashingsReset`, `processRandaoMixesReset`, `processHistoricalSummariesUpdate`, `processParticipationFlagUpdates`, `processSyncCommitteeUpdates`, `processProposerLookahead` (Fulu) |
| 32 | `Operations` | operations | `processBlockHeader`, `processWithdrawals`, `processExecutionPayload`, `processRandao`, `processEth1Data`, `processOperations` plus every operation handler, `processSyncAggregate` (`fastAggregateVerify`) |
| 33 | `DataAvailability` | operations | (Fulu) `isDataAvailable`, KZG cell-verify glue |
| 34 | `Genesis` | operations | `initializeBeaconStateFromEth1`, `isValidGenesisState` |
| 35 | `Transition` | operations | `stateTransition`, `processSlots` (per slot calls `processSlot`, and `processEpoch` at epoch boundaries), `processSlot` (caches the state root into `stateRoots`), `processBlock` |
| 36 | `ForkChoice/Store` | fork choice | `Store` structure plus `LatestMessage` / `FcNode` records, `getCurrentSlot`, `getAncestor`, store accessors |
| 37 | `ForkChoice/Weight` | fork choice | `getWeight`, `getVotingSource`, `filterBlockTree` |
| 38 | `ForkChoice/Head` | fork choice | `getHead` |
| 39 | `ForkChoice/Handlers` | fork choice | `onTick`, `onBlock` (calls `stateTransition`), `onAttestation`, `onAttesterSlashing` |

### 3.2 Reading the layers

**Foundations (rows 1, 2).** `Types` and `Constants` precede the containers
because a container's capacity caps reference the constants. A field typed
`Vector Root Const.slotsPerHistoricalRoot` needs `Const.slotsPerHistoricalRoot` in
scope, so `Constants` is at the foundation, never a catch-all the rest of the spec
reaches into late.

**Containers (rows 3 to 18).** Each component container gets its own file, in
topological order among themselves: `Attestation` after `AttestationData` after
`Checkpoint`, all before `State`. A container file also holds the helpers that are
pure on that container, the ones taking the container and not the `State`.
`Validator` carries `isActiveValidator` because that predicate reads a validator's
activation and exit epochs and needs nothing from the state. These pure
predicates sit with the container they read.

**State (row 19).** The `BeaconState` definition only, no operations. Field access
is the framework's generic `sszGet` / `sszUpdate`, so there are no per-field
accessors to colocate, and the file is just the field list under `forkcontainer`.
It imports every container.

**State operations (rows 20 to 35), by concern.** Any helper that takes the
`State` cannot precede it, so it lives in a concern file that imports `State`.
These split by concern, not by kind, with no catch-all. There is no `Base`, no
`Misc`, no `Util`. An operation with no obvious concern file signals a missing
concern, not that it belongs in `State`, which would recreate `Base` under a new
name. Each concern file holds its accessors, mutators, and predicates together.
The generated Python's by-kind sections (a global `Accessors`, a global
`Mutators`, a global `Predicates`) are reorganized by concern here, following the
single-responsibility principle at file scale.

So "validator" code spans two layers. The container and its pure predicates sit up
top (row 5, `Containers/Validator`); the registry operations on the `State` sit in
the concern layer (rows 24 and 28, `Registry`). The file names keep them distinct,
and neither file holds anything that does not belong to its concern and its layer.

### 3.3 The read/write seam and import-cycle resolution

Concern files import one another, forming a directed graph, and Lean forbids
import cycles. By-concern grouping can manufacture a cycle that does not exist at
the function level. `slashValidator` (a registry mutator) calls `decreaseBalance`
(a balance operation), so `Registry` imports `Balances`. If `getTotalActiveBalance`
were placed in `Balances`, it would call `getActiveValidatorIndices` (a registry
accessor), forcing `Balances` to import `Registry`. The functions are acyclic; the
grouping created the cycle.

By-concern is the grouping heuristic. The acyclic import graph is the hard
constraint. The constraint wins. The spec's helper call graph is itself a directed
acyclic graph, confirmed during the port, so a valid file order always exists. Any
genuinely mutually recursive helpers share one file through a `mutual` block.

The seam shows in the table. `Balances` and `Registry` each appear twice, a low
accessor file (rows 23, 24) and a high derived or mutator file (rows 26, 28).
`Registry` must split because `Committees` (row 25) needs `getActiveValidatorIndices`
while `slashValidator` needs `getBeaconProposerIndex` from `Committees`. One
`Registry` file would cycle with `Committees`. A helper whose callees straddle two
concerns goes where imports flow one way, in the concern of its primary effect.
When it truly combines both, it floats to a file above both. `getTotalActiveBalance`
sits in `Accessors` (row 26), above `Balances` and `Registry`, rather than cycling
them.

The recurring seam is read-versus-write: pure accessors sit below the mutators that
call them. This reuses the spec's own accessor and mutator stratification as a
tiebreaker, not as the primary axis. Tiny concerns (`Time`, `Randao`, `Signing`)
may merge with an adjacent concern in the same stratum; every merge is weighed
against the `Base` smell. These placements fall out of the call graph during the
port, the same moment the concern-file set is fixed.

### 3.4 One directory per fork

Each fork is a directory of this shape, `EthCLSpecs/Fulu/…` and `EthCLSpecs/Gloas/…`, all
per-fork through the inheritance mechanism. There is no shared spec layer; the
framework is the only shared layer. Section 5 explains why a shared layer is
neither needed nor wanted. Each section is opened by its header macro,
`state_section` or `fork_choice_section`, from the effect-monad section of
`FRAMEWORK_ARCHITECTURE.md`. Fulu's files are the full accumulated spec ported
from the generated `fulu` Python; Gloas's files are the diff, an `inherit` for an
unchanged declaration and a full declaration for an overridden or new one, in the
corresponding file. The split extends per fork: Fulu adds a `DataAvailability`
file, Gloas adds builder and payload files.

### 3.5 The package structure

The four layers map onto separate Lake packages, so the dependency direction is
enforced by the build rather than by discipline. The framework is one package, the
specs another that requires it, and the proofs a third.

```
SizzLean (which pulls in LeanHazmatSha256), LeanHazmatBls, LeanHazmatKzg   (SSZ + crypto)
        │
        ▼
EthCLLib     the DSL, the fork-interface typeclass, and the generic PySpecTests
             driver; names no fork
        │
        ▼
EthCLSpecs   EthCLSpecs.Fulu and EthCLSpecs.Gloas implement the interface; the
             PySpecTests runner exe instantiates the generic driver at a fork; plus
             the unit-test lib
```

A separate package cannot import what it does not require, so `EthCLLib`
physically cannot reach a spec module. That is the domain line, machine-checked, the
same one-way enforcement `SizzLean` gets by not depending on `LeanEthCS`.

`PySpecTests` straddles the boundary cleanly along the fork-interface typeclass. Its
generic driver lives in `EthCLLib`: it decodes through `[SSZRepr]`,
dispatches each format to an interface method, compares by root, and classifies, all
written against the interface, so it depends on no concrete fork. Its runner exe lives
in `EthCLSpecs`: it is the thin piece that instantiates the generic driver at
`Fulu` or `Gloas` and runs the long-lived server the Python harness talks to. The
runner depends on the specs because it is in the specs package, so there is no cycle.
The framework needs the interface, the specs need the framework, and the runner needs
both and lives with the specs.

The proofs are a standalone package, `EthCLProofs`, that requires
`EthCLSpecs` and mathlib and stays out of the umbrella, the `LeanPoseidonProofs`
containment pattern, so mathlib never reaches the framework, the specs, the runner, or
the regular build. It is created when proofs begin (Section 11).

### 3.6 Per-package directory layout

The package name appears in a path exactly twice, by Lake convention: the package
directory and the library source root, since the namespace equals the library name
equals the package name (Section 3.4). Below the library root, nothing repeats. The
layout:

```
packages/EthCLLib/
├── lakefile.toml
├── EthCLLib.lean                  # library root, re-exports
├── EthCLLib/                      # library source, the EthCLLib.* namespace
│   ├── Forms/  Preset.lean  Monad.lean  Box.lean  Map.lean  Crypto.lean
│   │   Arith.lean  Loop.lean  Interface.lean  PySpecTests.lean
│   └── Tests/                     # the EthCLLib.Tests.* test library
└── (umbrella; requires SizzLean, LeanHazmatBls, LeanHazmatKzg)

packages/EthCLSpecs/
├── lakefile.toml
├── EthCLSpecs.lean                # library root
├── EthCLSpecs/                    # library source, the EthCLSpecs.* namespace
│   ├── Fulu/…   Gloas/…           # one directory per fork (Section 3.4)
│   ├── PySpecTests/Server.lean    # the runner exe, EthCLSpecs.PySpecTests.Server
│   └── Tests/                     # the EthCLSpecs.Tests.* test library
├── PySpecTests/                   # the Python pytest-xdist harness (package-level)
└── docs/                          # these documents
```

Three naming rules fix the directories:

- **The conformance runner is `PySpecTests`, not `conformance`.** The name is the
  glossary term, and it covers both sides: the Lean runner exe is
  `EthCLSpecs.PySpecTests.*`, and the Python harness is a package-level `PySpecTests/`
  directory. The Lean source lives in the library tree, the Python at the package
  level, and they share the one name.
- **Test libraries do not repeat the package name.** Tests live in a `Tests/`
  subdirectory of the library, namespace `EthCLLib.Tests` / `EthCLSpecs.Tests`, built
  as their own `lean_lib` (globbed from `*/Tests/`, excluded from the shipped
  library), not a separate `EthCLLibTests/` sibling. The directory is `Tests`; the
  package name appears only at the structural library-root level. The `*.Tests`
  namespaces do not collide the way a bare `Tests` in two packages would.
- **The `packages/<Pkg>/<Pkg>/` doubling stays.** It is forced by the
  namespace-equals-library-name convention and is uniform across the repository
  (`packages/SizzLean/SizzLean/`); it is the only repeat, and nothing repeats in a
  deeper subdirectory (files are `Fulu/Types.lean`, not `Fulu/FuluTypes.lean`).

---

## 4. The container layer per fork

The author declares each SSZ container through `forkcontainer` and each non-SSZ
structure through `forkstruct`, the two SSZ-versus-not forms of the container
front-end. Every container is `[Preset]`-parameterized uniformly. The macro adds
the binder always, so the author never decides per container whether a container
needs the preset. A preset-free container like `Checkpoint` carries the binder too,
and its two concrete-preset instances are definitionally equal, so the uniformity
costs nothing.

The full `SSZRepr` is always derived. There is no serialize-only, deserialize-only,
or hash-tree-root-only classification. Carrying an unused `deserialize` costs
nothing, and the one distinction that matters is SSZ versus not, which is exactly
the choice between `forkcontainer` and `forkstruct`. `forkstruct` is for the
fork-choice `Store`, `FcNode`, and `LatestMessage`, the pyspec `@dataclass`es that
never cross the wire. The boxing-model part of `FRAMEWORK_ARCHITECTURE.md`'s
container front-end owns why these stay non-SSZ.

### 4.1 Inherit or rewrite

Fork-incremental declaration follows two cases, the same two that functions follow.
An unchanged container is `inherit`ed, not rewritten in the fork. A changed or new
one is declared in full. There is no append form. SSZ field order is load-bearing
for serialization and Merkleization, so a fork that changes a container restates
its complete field list explicitly on the page, checked by conformance, rather
than merging onto a parent by a rule the reader cannot see.

The Gloas container manifest:

```lean
namespace EthCLSpecs.Gloas

-- Unchanged from Fulu: inherited, the field list is not restated.
inherit Checkpoint
inherit Validator
inherit Attestation

-- Changed: a full redeclaration restating the complete field list.
forkcontainer BeaconState where
  -- ... the accumulated fields, with latestExecutionPayloadHeader
  --     replaced by latestBlockHash in place, then the ePBS fields:
  builders                    : List Builder Const.builderRegistryLimit
  executionPayloadAvailability : Bitvector Const.slotsPerHistoricalRoot
  -- ...

forkcontainer BeaconBlockBody where
  -- ... the accumulated fields, with executionPayload dropped
  --     (ePBS reveals the payload separately)

-- New in Gloas: fresh declarations.
forkcontainer ExecutionPayloadBid where
  -- ...
forkcontainer Builder where
  -- ...
forkcontainer PayloadAttestation where
  -- ...

end EthCLSpecs.Gloas
```

Gloas's `BeaconState` replaces `latestExecutionPayloadHeader` with
`latestBlockHash` in place, then appends the ePBS fields, so it is a full
redeclaration. Its `BeaconBlockBody` drops `executionPayload`, also a full
redeclaration. The brand-new ePBS containers (`Builder`, `ExecutionPayloadBid`,
`PayloadAttestation`, and the rest) are fresh `forkcontainer` declarations. Every
unchanged container is `inherit`ed. An inherited container's field types and
capacity caps late-bind in the Gloas namespace through raw field-list capture
replayed in the child, so a field whose capacity names `Const.x` resolves to
Gloas's tier (Section 8).

---

## 5. The state-transition authoring contract

This section states the architectural decisions that constrain how an author
writes a step. They follow the contract's authoring-style section and the
effect-monad section of `FRAMEWORK_ARCHITECTURE.md`, applied to the consensus
helpers a fork delivers.

### 5.1 State-free pure, state-reading monadic

A state-free helper is a pure function. `computeEpochAtSlot`, `isActiveValidator`,
and `computeDomain` take explicit arguments, read no `State`, and return a value.
They are callable anywhere, from a step or from another helper, and they reason
cleanly in a later proof.

An accessor that reads the `State` is a monadic action in `StateTransition`, not a
pure function threaded with `(← get)`. `getCurrentEpoch` has type
`StateTransition Epoch`.

```lean
def getCurrentEpoch : StateTransition Epoch := do
  let state ← get
  return computeEpochAtSlot (sszGet state slot)
```

The reason is grounded in how Lean reads a `get`-prefixed name, verified against
the toolchain's standard library. A top-level `getX` reads as monadic in Lean:
`getEnv`, `getRef`, and `MonadState.get` are all monadic actions. A pure `get` is
a dot-method on data: `List.get`, `Expr.getAppFn`. A pure top-level
`getCurrentEpoch s` would read against that grain. And a field read is `sszGet`
over the box regardless, so there is no plain projection left to keep pure. Making
the state-reading layer monadic matches the language convention and keeps the
field-read discipline uniform.

The `get` an accessor calls is the standard library's `MonadState.get`, the same
`get` the contract's `State`-from-the-author's-view section shows. Monadic is
introduced only where an accessor actually reads the state in the transition. The
state-free helpers stay pure. A pure core like `State.currentEpoch` is extracted
under a monadic accessor only where a deferred proof later needs the pure lemma.
The practical effect: `get` itself nearly vanishes from spec bodies, because reads
go through `sszGet` and the monadic accessors rather than an explicit
`let state ← get` at every line.

### 5.2 Steps and the pipeline

Mutating steps are likewise monad actions in `StateTransition`, written in a
section opened by `state_section`. A step uses the closed set of primitives from
the contract's step-writing-primitives section: `assert`, `sszGet`, `sszUpdate`,
`modifyState`, `appendState` (append to a list field, over SizzLean's cap-clamping
`sszAppend` / `SSZList.push`), indexed access, and do-block sequencing.

The step-composition model is the same. A pipeline like `processBlock` or
`processEpoch` is itself a `forkdef` whose do-block calls its sub-steps in order.

```lean
forkdef processBlock : StateTransition Unit := do
  processBlockHeader
  processWithdrawals
  processExecutionPayload
  processRandao
  processEth1Data
  processOperations
  processSyncAggregate
```

The pipeline is an ordinary do-block, not a declarative list and not a generated
call sequence. It is inherited, overridden, or rewritten by the same rule as any
step. An inherited pipeline late-binds to the running fork's overrides through the
raw-capture replay: when Gloas inherits a caller, the called sub-step names in the
replayed body resolve to Gloas's overrides by ordinary name resolution. No
name-generation appears anywhere in the design.

### 5.3 The inherit / override / new manifest

Across forks each step is inherited, overridden, or new, the three fates over two
forms of the fork-declaration-model section. The author writes `inherit` for an
unchanged step and a full `forkdef` for an overridden or new one, and does not mark
which of the two a full declaration is; the resolver knows from the lineage.

```lean
namespace EthCLSpecs.Gloas

inherit getCurrentEpoch                  -- unchanged from Fulu

forkdef processBlock : StateTransition Unit := do   -- overrides Fulu's:
  processBlockHeader                                -- ePBS reveals the payload
  processWithdrawals                                -- separately, so the order
  processRandao                                     -- changes and the payload
  processEth1Data                                   -- step is gone from the block
  processOperations
  processSyncAggregate

forkdef processPayloadAttestation : StateTransition Unit := do  -- new in Gloas
  ...

end EthCLSpecs.Gloas
```

A fork that reorders or changes the sequence rewrites the do-block, the same
inherit-or-rewrite rule as containers. Gloas's `processBlock` is an override
because ePBS reveals the execution payload separately, so the block no longer runs
`processExecutionPayload` inline and the step order shifts. By the domain line, the
consensus helpers (`get_*`, `compute_*`, `is_*`) are spec-owned. There is no shared
spec layer, so fork-invariant helpers are inherited per fork and fork-varying ones
are per-fork overrides or new declarations.

The pyspec-to-Lean correspondence (a Python `assert` becomes the `assert` macro, an
in-place `state.field = …` becomes `sszUpdate`) is evidence for these decisions,
not a thing the author transcribes mechanically. The behavioral-conformance freedom
lets the Lean read naturally.

---

## 6. Genesis construction and fork upgrade

Two state-lifecycle functions sit outside the per-slot transition. They are
per-fork `forkdef`s and they are the `genesis` and `fork` entry points of the fork
interface.

### 6.1 Genesis

`initializeBeaconStateFromEth1` is a `StateTransition Unit`, not a state-builder. It
runs over a default initial state already threaded through the monad: it sets the
genesis fields, then runs the same monadic `processDeposit` that block processing
uses, over each genesis deposit.

```lean
forkdef initializeBeaconStateFromEth1
    (eth1BlockHash : Hash32) (eth1Timestamp : UInt64)
    (deposits : List Deposit) : StateTransition Unit := do
  modifyState fun state => -- set genesisTime, fork, eth1Data, latest header, ...
    ...
  for d in deposits do
    processDeposit d            -- the same monadic step block processing runs
  -- effective-balance and activation finalization follow
```

The runner is the sole anchor. It boxes `default : BeaconState` with the config's
flavour, `FastBox` for the runner and `UncachedBox Sha256Spec` for proofs, and runs
genesis over that boxed state. So genesis never touches a box and the box type is never passed to
it. The flavour choice lives at the one anchor where the state is first built, the
arrangement the contract's `State`-from-the-author's-view section describes.

`isValidGenesisState` is a pure `State → Bool` predicate. The harness calls it
standalone, not inside a transition, so it stays pure under the state-reading rule
of Section 5: it does not read the threaded state, it inspects a state it is handed,
which reads cleanly as a pure predicate.

Both are per-fork. Gloas overrides `initializeBeaconStateFromEth1` to initialize the
ePBS fields, and the `genesis` vector format exercises them.

### 6.2 Fork upgrade

`upgradeToGloas : Fulu.State → Gloas.State` reads a finished Fulu state and
constructs the Gloas one.

```lean
def upgradeToGloas (pre : Fulu.State) : Gloas.State :=
  -- reads Fulu fields by sszGet, writes the Gloas BeaconState,
  -- carrying common fields across and initializing the ePBS ones
  ...
```

It is the single sanctioned cross-fork reference. It names both forks' `State`
types, so it lives in Gloas, imports Fulu, and reads Fulu fields by `sszGet`. This
one explicit dependency does not reintroduce a shared spec layer. A shared layer
would be a place both forks import for common helpers, which the inheritance
mechanism removes the need for; `upgradeToGloas` is the opposite, a deliberate
single edge from the child to the parent, named once, for the one operation that
genuinely spans two forks.

Only `upgradeToGloas` is implemented. `upgradeToFulu` would require an Electra
state, and Electra is not built, so only the Fulu-to-Gloas `fork` and `transition`
vectors run; Electra-to-Fulu upgrade vectors are out of scope. This is the runtime
counterpart to the static fork diff of Section 2. Section 2 says what changes
between forks; the upgrade performs the change on a live state.

---

## 7. Fork-choice authoring

The fork choice is the second state machine, written in `StoreTransition` over
`Store map` in a section opened by `fork_choice_section`. The `Store` and its `on_*`
handlers are the fork-choice entry points of the fork interface. The
`runStateTransition` nested-machine bridge of `FRAMEWORK_ARCHITECTURE.md`'s
effect-monad section runs the full state transition inside the `onBlock` handler
and surfaces any inner failure through `StoreTransitionError.transition`. The
step-and-check harness shape comes from the conformance framework.

### 7.1 The read layer is pure, the handlers are monadic

The fork-choice read layer is pure functions over the `Store`. `getHead`,
`getWeight`, `filterBlockTree`, and their helpers take a `Store` and return a value.
The `on_*` handlers are the monadic `StoreTransition` actions that mutate the store
and call the read layer on `(← get)`.

```lean
-- read layer: pure, recursive, takes the Store as an argument
def getWeight (store : Store map) (root : Root) : Gwei := ...

-- handler: monadic, mutates the store, calls the read layer on the current store
forkdef onBlock (signedBlock : SignedBeaconBlock) : StoreTransition Unit := do
  let store ← get
  ...
  let post ← runStateTransition pre (stateTransition signedBlock)
  ...
```

This diverges from the monadic state-transition accessors of Section 5, and the
divergence is deliberate. The fork-choice reads are genuinely recursive: `getHead`
walks the block tree, `getWeight` sums a subtree, `filterBlockTree` prunes
recursively. A pure recursive function takes a clean `termination_by` measure on its
argument and reasons cleanly in a later proof. Monadic recursion would drag the
termination proof and the equation lemmas through the monad for read-only walks that
never mutate, which is friction for no gain. Purity is infectious upward: a pure walk
cannot call a monadic accessor, so the whole read layer is pure together.

The same principle drives both machines: be monadic only where it helps and does not
hurt. It lands on monadic in the state transition because the accessors read the
threaded state and do not recurse, and it lands on pure here because the recursion
makes monadic hurt. The state-transition accessors of Section 5 and the fork-choice
reads here are two applications of one rule, not a contradiction.

### 7.2 Per-loop termination

The recursive fork-choice walks (`getHead` and its siblings, the filtered block
tree, the weight recursion, the unrealized-justification walk) are the loops that
need a termination strategy. The control-flow section of `FRAMEWORK_ARCHITECTURE.md`
gives the two options. Well-founded recursion through `termination_by` and
`decreasing_by` is honest and carries no artificial bound, but it forces the
invariant proof at definition time. The framework's `fuelLoop` defers that proof at
the cost of a defined-but-unreachable default branch.

The per-loop rule is explicit. Default to well-founded recursion when the measure is
clean. `getHead`, for instance, has a clean measure when child slots strictly
increase, so `maxSlot - currentSlot` strictly decreases and `termination_by` closes
it. Reach for `fuelLoop` only when the up-front invariant proof would block the
definition from existing before proofs are in scope. Record the choice and its reason
at each such loop, so a later reader knows whether a bound is honest or deferred.

---

## 8. Crypto usage on the spec side

The crypto split of `FRAMEWORK_ARCHITECTURE.md`'s crypto layer puts the
domain-agnostic mechanics in the framework and the consensus-aware part in the spec.
This section is the spec side.

### 8.1 `getDomain` is a monadic accessor

The author writes `getDomain`, a monadic accessor by the state-reading rule of
Section 5, because it reads `state.fork` and the genesis validators root. It selects
the `DOMAIN_*` constant for the operation and delegates to the framework's pure
`computeDomain`.

```lean
def getDomain (domainType : DomainType) (epoch : Option Epoch)
    : StateTransition Domain := do
  let state ← get
  let epoch := epoch.getD (← getCurrentEpoch)
  let forkVersion := -- state.fork.previous or .current, by epoch
    if epoch < sszGet state fork.epoch then sszGet state fork.previousVersion
    else sszGet state fork.currentVersion
  return computeDomain domainType (some forkVersion) (sszGet state genesisValidatorsRoot)
```

### 8.2 The deposit exception

The author owns the per-signature fork-version choice. Most signatures take the fork
version from the state at the relevant epoch, which is what `getDomain` does. A
deposit is the exception. It uses a fixed `GENESIS_FORK_VERSION` and a zero genesis
validators root through `computeDomain` directly, bypassing `getDomain`, because a
deposit signature is made before the depositor knows the chain it will join.

```lean
forkdef processDeposit (deposit : Deposit) : StateTransition Unit := do
  -- ... merkle-branch check against eth1Data.depositRoot ...
  let domain := computeDomain Const.domainDeposit
                  (some Const.genesisForkVersion) (zeroBytes 32)  -- fixed, zero gvr
  let signingRoot := computeSigningRoot deposit.data.message domain
  if blsVerify deposit.data.pubkey signingRoot deposit.data.signature then
    -- add or top up the validator
    ...
  -- else: skip this deposit; a bad deposit signature does not reject the block
```

The deposit's `verify` is a conditional, not a gate. A bad deposit signature skips
the validator rather than rejecting the block, which is the one place crypto
verification branches instead of asserting.

### 8.3 `verify` as a gate, `todo` for the unreachable

The usual flow is `getDomain`, then `blsVerifySigned` asserted as the gate; it folds the
framework's agnostic `computeSigningRoot` and the BLS verify into one call over the
spec's SSZ-typed pubkey, object, domain, and signature.

```lean
forkdef verifyBlockSignature (block : SignedBeaconBlock) : StateTransition Unit := do
  let domain ← getDomain Const.domainBeaconProposer none
  let pubkey ← proposerPubkey block.message.proposerIndex
  assert (blsVerifySigned pubkey block.message domain block.signature)   -- a gate
```

A crypto-dependent path that no in-scope vector reaches is a `todo`, the deferral
work-queue of the error model in `FRAMEWORK_ARCHITECTURE.md`. The discipline: a
`todo` carries a documented claim that no in-scope vector reaches it, and a vector
that does reach one fails loudly rather than passing silently. The crypto layer is
the most common home for `todo`, since the verify-gates are pervasive and the FFI
backend is the latest-bound dependency, so crypto-gated branches are stubbed first
and filled in as the backend and the vectors come online. Each remaining `todo`
records why it is unreachable by any in-scope vector, and the spec-faithful-mode
annotations of the conformance framework mark it.

---

## 9. Constants and presets per fork

Each fork sources its numerics into the three tiers of
`FRAMEWORK_ARCHITECTURE.md`'s preset-constant-config-tier-system section.
Classification happens once, here, at sourcing time. The author writes `Const.x` at
every use site and never classifies the tier there.

| Tier | Where the value goes | Fulu examples | Gloas adds |
|---|---|---|---|
| Preset (`[Preset]`) | the `minimal` and `mainnet` instances | `SLOTS_PER_EPOCH` (8 / 32), `SLOTS_PER_HISTORICAL_ROOT` (64 / 8192) | `PTC_SIZE` (16 / 512) |
| Universal | a `Const` abbrev with a literal body | `FAR_FUTURE_EPOCH`, `VALIDATOR_REGISTRY_LIMIT`, the `DOMAIN_*` tags | `BUILDER_REGISTRY_LIMIT` |
| Config (`[Config]`) | the `[Config]` instance | `GENESIS_FORK_VERSION`, `SECONDS_PER_SLOT` | `GLOAS_FORK_EPOCH` |

The preset-varying values go into the `minimal` and `mainnet` `[Preset]` instances,
the fixed values into universal `Const` abbrevs, and the network values into the
`[Config]` instance, all read through `Const`. A preset constant shapes a type (a
vector width), the universal and config tiers do not. The author writes
`Const.slotsPerEpoch` and the SCREAMING_SNAKE `SLOTS_PER_EPOCH` of the spec maps to
that `Const.camelCase` projection.

### 9.1 The tier system is per fork

The tier system is per fork, not shared. Each fork has its own `Preset` and `Config`
classes and its own `Const` abbrevs. Gloas inherits Fulu's through the inheritance
mechanism and appends the ePBS constants: `PTC_SIZE` to the preset tier,
`BUILDER_REGISTRY_LIMIT` to the universal tier, `GLOAS_FORK_EPOCH` to the config
tier.

This is forced by container-cap late-binding, not a stylistic choice. A container
cap names `Const.x`, so an inherited container must resolve that constant to the
running fork's tier. A shared constants layer could not provide that, because the
inherited container's cap would early-bind to the shared symbol rather than the
child fork's value, and it would contradict the no-shared-spec-layer rule of
Section 3. Both `minimal` and `mainnet` instances are supplied from the start, as
`@[reducible] def`s injected at the test boundary, so the spec is generic over the
preset and the runner picks per test.

---

## 10. The conformance plan per fork

Once a fork satisfies the fork interface, `PySpecTests` drives every spec-relevant
format against it. The author writes no handler table and maps nothing to tests, the
inverted-conformance-contract of `SPEC_AUTHORING_MODEL.md`; the author implements the
interface and `PySpecTests`, written once and fork-agnostic, runs every format.

### 10.1 The formats each fork runs

| Format | Entry point driven | In scope |
|---|---|---|
| `sanity/blocks`, `sanity/slots` | `stateTransition` / `processSlots` | yes |
| `finality`, `random` | `stateTransition` | yes |
| `epoch_processing/*` | a single `process_*` epoch sub-step | yes |
| `operations/*` | a single operation handler | yes |
| `rewards/*` | a single delta function | yes |
| `fork_choice` | the `on_*` handlers | yes |
| `genesis` | `initializeBeaconStateFromEth1` | yes |
| `fork` | `upgradeToGloas` | yes (Fulu to Gloas only) |
| `transition` | `stateTransition` with `upgradeToGloas` mid-fold | yes (Fulu to Gloas only) |
| `ssz_static`, `bls`, `kzg` | n/a | no (framework-library concern) |

The `rewards/*` format is in scope and drives a single delta function in isolation,
the reward and penalty deltas of the `Rewards` concern file (row 29). `fork` and
`transition` run only the Fulu-to-Gloas upgrade, since Electra is not built. Both
presets run; mainnet runs on demand rather than on every CI pass.

### 10.2 The reject-faithfulness audit

The audit reads the classify-mode bucket of the error model against each vector's
valid-or-invalid marking. The vectors are the operational reference, so matching the
verdict is necessary but not sufficient; the audit checks that the spec rejects at
the same point and for the same reason the upstream pyspec does.

| Vector marking | Faithful result | A failure |
|---|---|---|
| valid | the matching post-state by root | any error (`assert`, `outOfBounds`, `todo`); an `outOfBounds` here is the framework's bug-smell |
| invalid | a faithful `assert` rejection | a `todo` (an unimplemented path is not a validation, so it fails and points to work) |

A valid vector must produce the matching post-state by root. Any error is a failure,
and an `outOfBounds` on a valid vector is the bug-smell of the error model, surfacing
a likely framework or spec bug rather than a validation. An invalid vector must be
rejected by `assert`, the faithful rejection. A `todo` is never a faithful rejection;
an unimplemented path is not a validation, so a `todo` on an invalid vector fails and
points to the work. An `outOfBounds` or `missingKey` counts as rejected but is
flagged, and the audit confirms the spec rejects at the same point and for the same
reason pyspec does, never by a coincidental downstream bounds error that happens to
land on a rejected vector. That mechanism check is where spec-faithfulness lives,
alongside the spec-faithful-mode annotations for the unreachable `todo` branches.

---

## 11. The proof plan

Proofs are deferred past the first milestone, the deferred proof-support layer of
`FRAMEWORK_ARCHITECTURE.md`. The specs stay proof-friendly meanwhile: total
functions, fuel or well-founded recursion over `partial`, and the seven
anti-patterns of that layer avoided in every definition.

### 11.1 Proofs run at the pure config only

When proofs start, they run only at the pure configuration of the contract's
one-spec-body-two-configurations duality: `UncachedBox Sha256Spec` (uncached, so the
getter-setter laws hold by `rfl`), the pure `StateTransition` monad (`StateT` over
`Except`), and `treeMap` (clean insert and lookup laws, relevant only to fork-choice proofs, since
the state-transition machine holds no map).

The fast configuration (`FastBox`, `EStateM`, `hashMap`) is never a proof target.
Conformance establishes it empirically. The fast-versus-pure gap is closed at the
dependency level, not the spec level. SizzLean's cache-coherence test proves
`FastBox` equals `PureBox` on the hash-tree-root, and the FFI-equivalence axioms
handle the hasher, so there is no spec-level fast-equals-pure theorem to prove. The
specs inherit the gap-closing from the dependency.

### 11.2 The hasher is per goal

The hasher is a per-goal axis, not a fast-versus-pure bundle. Symbolic
state-transition proofs use the opaque `Sha256` directly: equality of two roots
follows from the same hash over the same buffers, axiom-free, the first hasher case
of the project's proof discipline. Only a goal that needs a hash's concrete bytes
swaps to `Sha256Spec` (the kernel-reducible case) or invokes the named
FFI-equivalence axioms (the symbolic-then-computational case). The proof picks the
hasher by what the goal needs, independent of the box flavour and the monad.

### 11.3 The techniques and the candidate theorems

When proofs start, the techniques are the gate-split on `assert` conditions and the
abstract `[CryptoBackend]`, both from the deferred proof-support layer, with
arithmetic lifted to `Nat` through the `UInt64`-to-`Nat` correspondence lemmas of the
arithmetic layer. The candidate theorems per fork are invariant preservation and
happy-path correctness. Each is proved per fork, since inheritance is by symbol and
Fulu's and Gloas's steps are distinct symbols. A theorem is itself a declaration,
though, so it can ride the inheritance replay into the child namespace: an unchanged
inherited chain re-checks cheaply, and the proof cost concentrates on the diff. The
theorems module is the containment boundary if proofs ever need mathlib, keeping it
off the framework, spec, runner, and `PySpecTests` paths, the discipline the
repository applies to its Poseidon proofs.

---

## 12. Spec-revision tracking and the discrepancy policy

The pinned version per fork is the `pyspecPinnedVersion` constant of the contract's
spec-revision-pin section: the latest upstream tag carrying that fork's vectors,
stable or pre-release. Fulu pins a stable release. Gloas tracks the consensus-specs
main branch, so it pins a pre-release or alpha tag, or a dev commit, while it is
unreleased. The two forks sit at different pins at the same time.

The values below are illustrative and are bumped to the current latest release at
implementation time (the repo's existing `scripts/run_conformance.py` pins
`v1.7.0-alpha.10` at this writing); the implementation also confirms the chosen tag
actually carries Gloas vectors, falling back to a dev commit if not.

```lean
namespace EthCLSpecs.Fulu
def pyspecPinnedVersion : String := "v1.7.0-alpha.10"   -- latest release at writing
end EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas
def pyspecPinnedVersion : String := "v1.7.0-alpha.10"   -- same tag while Gloas is unreleased
end EthCLSpecs.Gloas
```

### 12.1 The directional policy

The discrepancy policy is directional, not symmetric. The vectors are generated from
the Python pyspec and are the operational reference, so a Lean-versus-vector
divergence almost always means the Lean is wrong and the fix goes in Lean. The spec
markdown is the ultimate authority. "Spec wins" bites only in the rare case a vector
contradicts the spec text, an upstream pyspec bug, where Lean follows the text, the
vector fails, and the divergence is recorded rather than papered over by bending Lean
to a wrong vector.

The record lives in a per-fork `DISCREPANCIES.md`, keyed by vector id, so the audit
trail is one grep away. Each entry carries the vector id, the spec-text citation, and
the upstream issue link. This keeps the rare spec-wins case honest: a failing vector
is either a Lean bug to fix or a logged discrepancy with a citation, never a silent
adjustment.

---

## 13. What the GloasSpec experiment teaches

An earlier GloasSpec experiment ported a Gloas state transition and fork choice by
hand. It is a design reference. The new specs are authored fresh on the framework,
with nothing ported.

What carries over is the consensus knowledge the experiment validated. The step
ordering for `processBlock` and `processEpoch` is one: the experiment confirmed the
canonical sub-step sequence, which the load-order table's row 31 and the pipeline of
Section 5 reuse. The reject-reason vocabulary is the other: the experiment's
debugging surfaced which failure kinds a port hits, now the typed
`StateTransitionError` and `StoreTransitionError` constructors of the error model.

The experiment's module split is superseded. It used a flat `Spec/{Constants, Base,
…}` shape with a `Base` catch-all and an accessor-mutator-predicate grouping by kind.
The layout of Section 3 is authoritative instead: the five-layer stratification, the
by-concern files, no `Base`, and `Constants` at the foundation. The organizing
discipline is the cohesion of Section 3 plus the state-free-pure / state-reading-
monadic split of Section 5.

What the framework now generates the author no longer hand-rolls. The experiment
wrote size proofs and derived instances by hand; `forkcontainer` derives them. It
wired the monad and the discharge by hand; the header macros and `runStateTransition`
do that. It hand-maintained constants; the per-fork tier system carries them. And it
had no cross-fork inheritance; the inheritance mechanism supplies it. The experiment
proved the consensus shape was right. The framework regenerates that shape
mechanically and adds both presets and the two configurations the experiment never
had.
