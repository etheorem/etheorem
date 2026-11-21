# EthCLSpecs: Implementation Notes

The as-built companion to the four design documents in this directory
(`SPEC_AUTHORING_MODEL.md`, `SPECS_ARCHITECTURE.md`, `FRAMEWORK_ARCHITECTURE.md`, and
the glossary). Those four are the design of record. This file records how
`EthCLSpecs` / `EthCLLib` realize them: the current architecture, the places the code
deviates from a doc (with the reason), and the spec-faithfulness decisions worth
knowing. Everything here describes the tree as it stands against the
`v1.7.0-beta.4` pin.

## Scope and conformance

Three forks, **Fulu**, **Gloas**, and **Heze**, against the `consensus-specs` minimal and
mainnet archives at `v1.7.0-beta.4` (a pre-release, so the harness pins the tag
explicitly rather than reading `gh release latest`). The counts below are the
beta.4 run, `--subset=0`, with no failure and no xfail on either preset. The Heze
`fork_base_state` vectors, the alpha.12 xfails, match the spec at beta.4
(`DISCREPANCIES.md`).

| | minimal | mainnet |
|---|---|---|
| Fulu  | **5318 passed** | **859 passed** |
| Gloas | **6760 passed** | **1094 passed** |
| Heze  | **6972 passed** | **1073 passed** |

Fulu's collected formats: `epoch_processing`, `operations` (including the standalone
`execution_payload`), `rewards`, `sanity/blocks`, `sanity/slots`, `finality`,
`random`, `fork_choice` (including the PeerDAS data-availability `on_block` cases and
`get_proposer_head`). Gloas adds `fork`, `transition`, and the full ePBS
`fork_choice`. `DISCREPANCIES.md` records no open vector at beta.4. Every vector the
implemented formats reach matches by root or rejects faithfully. Deliberate divergences from the spec *text* that no vector
observes are catalogued per fork in this file.

**Out of scope** (deselected in `walk_cases`, not collected):

- **Fulu `fork` / `transition`** (Electra→Fulu): the upgrade and the pre-fork Electra
  blocks both need a complete Electra parent fork the library never builds. The
  **Gloas** `fork` / `transition` (Fulu→Gloas) and the **Heze** ones (Gloas→Heze)
  are in scope. Heze `fork_base_state`, open at alpha.12, passes at beta.4.
- **`light_client`, `networking`, `merkle_proof`, `sync`**: not state-transition or
  fork-choice formats; outside `IN_SCOPE_RUNNERS`.
- **`genesis`**: no vectors at the pin (see Genesis below).

**CI.** The `ethcl` job in `lean_action_ci.yml` runs `just ethcl-test` (builds all
four libraries, firing the framework and spec self-tests) and `just
ethcl-pyspec-smoke` (the `pytest-xdist` dev subset at minimal for all three forks
through the per-worker `pyspec_server`). It is green iff no in-scope vector hits a
bug-smell or a real mismatch. Mainnet and the full sweep run on demand
(`--preset=mainnet`, `--subset=0`).

## Inheritance and capture

The capture/replay mechanism lives in `EthCLLib.Internal.Capture` (two
`SimplePersistentEnvExtension`s: `lineageExt` for `fork … from …` edges, `captureExt`
for the raw declaration bodies), `EthCLLib.Spec.Forms` (the `fork` / `forkdef` /
`forkabbrev` / `forkinstance` / `forkcontainer` / `forkstruct` / `inherit` command
elaborators), and `EthCLLib.Spec.Tiers` (the four `Preset` / `Config` forms).
`inherit Foo` walks `lineageExt` from the current namespace strictly upward and
replays the nearest ancestor's captured `Foo` in the current namespace, re-emitting
whichever declaration kind the capture recorded. The body is the
author's own un-stamped syntax, spliced by quotation, so its sibling identifiers
late-bind at the child site by ordinary name resolution. Antiquoting pre-existing
syntax adds no macro scopes, so no blanket hygiene override is needed.

- **The `fork` keyword reserves the token `fork`.** A `scoped syntax "fork " …` makes
  `fork` a keyword in every module that opens `EthCLLib.Spec`, so a binding named
  `fork` fails to parse. The captured-declaration field is `forkNs`, and elaborators
  use `forkNs` locals. Spec authors must not name a binding `fork`.
- **`fork` identity is the current namespace; the parent is the sibling.** `fork Gloas
from Fulu` records `(currNamespace, currNamespace.getPrefix ++ Fulu)`, which assumes
  both forks share a prefix (`EthCLSpecs.Fulu`, `EthCLSpecs.Gloas`), as
  `SPECS_ARCHITECTURE.md` §3.4 mandates. The `Name` argument is documentation; identity
  comes from the namespace.
- **`inherit` is a pure consumer** and never re-captures, so a grandchild walks past an
  unchanged intermediate fork to the nearest ancestor that captured the symbol.
- **Capture keys split the namespace at the nearest registered fork.** Constants sit
  inside `namespace Const` within the fork, so keying on the raw `currNamespace` would
  file them under `EthCLSpecs.Fulu.Const`, which is no fork and which no lineage walk
  reaches. `captureKey` walks the namespace's prefixes against `lineageExt`, nearest
  prefix winning, and stores the residual path as the name, so a `forkabbrev` written
  in `Const` keys as `(EthCLSpecs.Fulu, Const.slotsPerEpoch)`.
- **Three elaborator properties the constant tiers rest on**, each pinned by
  `EthCLLib/Tests/ForkScoping.lean` rather than assumed:
  1. A composite `declId` scopes its body. `def Const.foo` written inside
     `namespace Gloas` lands at `Gloas.Const.foo` *and* resolves its body's
     unqualified names as if inside `Gloas.Const`, so late binding reaches into the
     sub-namespace and a replayed `Const.payloadTimelyThreshold` divides Gloas's
     `ptcSize`.
  2. Section-variable auto-binding survives a replay. `inherit` runs `elabCommand`
     from inside a command elaborator, and the surrounding `section variable
     [Preset] [Config]` is still picked up by the ordinary used-variable rule, so a
     child's inherited constants bind to the child's classes with nothing restated.
  3. Abbrev-ness survives replay, which is why `forkabbrev` exists at all. The test
     asserts it behaviourally, by synthesising an instance *through* an inherited
     alias: instance search unfolds a reducible definition and not a `def`, so a
     demotion would fail there rather than silently degrade SSZRepr synthesis.
- **`forkinstance` requires a name**, unlike Lean's `instance`. The capture key is a
  name and `inherit` has nothing else to spell. Its binders ride inside the captured
  `declSig` (`bracketedBinder* >> ": " term`), so no separate binder slot is needed;
  `forkstruct` is the one kind that fills one, since `structure` takes its parameters
  beside the field block.
- **Tier declarations merge instead of replaying.** A `Preset` / `Config` class or one
  of their value sets is a single declaration, so `inherit` cannot fuse two of them and
  refuses a tier capture outright. The child's own `forkpreset` / `forkconfig` /
  `forkpresetvalues` / `forkconfigvalues` collects the ancestors' captured blocks along
  the lineage, merges by entry name (child-most-wins, ancestor order preserved), and
  emits one flat declaration. A fork that adds no field still writes the bare form, so
  the class it emits is its own.
- **The downgrade bridge needs its own namespace, not just `scoped`.** A fork's body
  files sit *inside* the fork's namespace, where a `scoped` instance is already active,
  so `scoped instance … : Fulu.Preset` in `EthCLSpecs.Gloas` would be reachable from
  every Gloas module. The generated bridge lands in `EthCLSpecs.Gloas.Downgrade`
  instead; `Upgrade.lean` and `Interface.lean` write `open scoped Downgrade`, and
  nothing else can satisfy a parent-class constraint. The instances still resolve
  `Preset` and its projections, since the fork's namespace encloses the sub-namespace.
- **Gloas re-declares Fulu's unchanged component containers with `inherit`**
  (`Gloas.Inherited`, 28 types in dependency order: `Checkpoint`, `Validator`,
  `Attestation`, the slashing / deposit / exit evidence, the sync structures, the
  pending-queue records) rather than reaching across the fork boundary for them. Each
  replays Fulu's field block in the `EthCLSpecs.Gloas` namespace, so `Gloas.Validator` is
  a fresh structure with Fulu's exact fields, hence Fulu's exact SSZ encoding and Merkle
  root, and the fork is a complete, flat namespace (`SPECS_ARCHITECTURE.md` §3.4). The
  price falls at the upgrade boundary: `upgradeToGloas` converts each Fulu component value
  to its Gloas twin field-by-field (`cvValidator`, `cvCheckpoint`, …, with SizzLean's
  `SSZList.mapCap` for the list-typed fields), since `Gloas.Validator` is a distinct type from
  `Fulu.Validator`. Dependency order (a field's type inherited before the container that
  uses it), this fork's own constants and aliases from `Gloas/Types.lean` and
  `Gloas/Constants.lean`, and current-namespace priority for the types together make
  each replayed body bind its siblings to the Gloas-local copy. A plain `def` that the capture mechanism can't replay (`addressOf`) is
  restated for the Gloas validator, the same way `balanceAfterWithdrawals` is. `inherit`
  creating a fresh type is also the right tool for declarations a fork genuinely changes
  (`BeaconState`, `BeaconBlockBody`).

## Container and struct macros

`forkcontainer` (`Forms.lean` `emitContainer`) derives `Inhabited`, `DecidableEq`,
`BEq`, `Ord`, `Hashable`, and `SizzLean.SSZRepr`. `forkstruct` (`emitStruct`) is the
plain-structure variant. It also captures and replays arbitrary bracketed binders, so
a parameterized `forkstruct Store (map : MapKind) [HasherTag]` (with the auto
`[Preset]` first) is expressible. Both take `declModifiers` so a `/-- … -/` docstring
can precede them without derailing the parse, and both emit the `deriving` in a
_separate_ `deriving instance … for` command. `Forms.lean` `import SizzLean`, so the
class names resolve as globals rather than hygiene-stamped `SizzLean.SSZRepr✝`.

`Ord` / `Hashable` derive universally now that SizzLean carries them for the collection
types (`SSZList` / `Bitvector` / `Bitlist`), so the design docs' §5 "every container"
wording holds and a map-key container (`Checkpoint`) needs no hand-written derive. The
Gloas `ForkChoiceNode` is a `forkstruct` (no SSZ derive), so it keeps its own
`deriving instance BEq, Inhabited for …`. `Root`-keyed maps still need an explicit
`Ord (Vector UInt8 32)` (`instOrdBytes32` in `Fulu/ForkChoice.lean`) for `MapKind`.

`forkstruct`'s bracketed-binder capture has two practical notes the fork-choice structs
rely on: `emitStruct` puts `[Preset]` first then the extra binders (so `Store map`
resolves with `map` the only explicit parameter), and it emits no `deriving`, so a
struct's `Inhabited` (and the map-key `Ord` / `BEq` / `Hashable`) is added by a
following `deriving instance … for …`.

A `forkcontainer` carries the SizzLean container attributes through capture and
replay: `@[sizzlean_progressive]` (EIP-7495) and, since the beta.4 re-pin,
`@[sizzlean_progressive_gaps i …]`, the field positions an `active_fields` mask leaves at
`0`. The capture records the gap indices (`CapturedDecl.progressiveGaps`) and the replay
re-emits both attributes on the child fork's copy, so an `inherit`ed gapped container keeps
its shape. Heze's `BeaconState` (gaps 8, 9, 10, 28) and `BeaconBlockBody` (gaps 1, 6) are
the users, the positions of the fields EIP-8015 removed. A `treeMap` keyed by a pair needs
`Ord` on the pair, so `EthCLLib/Spec/FiniteMap.lean` gives `α × β` the lexicographic `Ord`
(Heze's inclusion-list store is keyed by `(Slot, Root)`).

## Crypto seam

`EthCLLib.Spec.Crypto` defines `CryptoBackend` (BLS `verify` / `fastAggregateVerify` /
`ethFastAggregateVerify` / `aggregatePubkeys`, KZG `kzgVerifyCellProofBatch`) over raw
`ByteArray` of the wire sizes (sk 32, pubkey 48, signature 96, blob 131072, commitment
48, cell 2048, proof 48). The class carries no SSZ dependency. `aggregatePubkeys` is a
deterministic aggregation rather than a verify gate, so it is its own member.

The single-value wire conversion is a coercion. SizzLean provides
`CoeOut (Vector UInt8 n) ByteArray` (`Repr/Instances.lean`, the canonical `⟨v.toArray⟩`),
so a `Root` / pubkey / signature is usable wherever the seam wants `ByteArray` with nothing
written at the call site. `CoeOut` is the source-keyed coercion class (the same one core
Lean uses for `Fin n → Nat`); a plain `Coe` fails here because its source is a semi-out-param
and the parametric `Vector UInt8 ?n` leaves a metavariable. The conversion fires for function
arguments, `++`, and `!=`, which covers the hashing concatenations and the fork-choice root
checks. It deliberately does not lift through `Array`, so a pubkey/commitment set keeps an
explicit `.map vecToBytes`; and the reverse direction (`bytesToVec` / `bytesToRoot`) stays an
explicit function, since it picks a length and truncates.

The spec does not call the seam directly. It calls the vector-typed wrappers: `blsVerify` /
`blsFastAggregateVerify` / `blsEthFastAggregateVerify` / `blsAggregatePubkeys` in `Crypto`
(beside the seam), and `blsVerifySigned` in `SigningRoot` (it folds in `computeSigningRoot`,
so it lives beside the helper it composes; `SigningRoot` imports `Crypto` for `blsVerify`).
Each is a thin definitional wrapper, so a wrapper call reduces to the exact seam call it
replaces. The KZG batch is called inline (its arguments are different-width vector arrays).
A gate then reads `assert (blsVerifySigned pubkey obj domain sig)`, naming the values, with
the wire-byte conversion out of the spec body.

Four backends: `ffi` (production), `verifyOff` (`bls_setting: 2`, BLS gated, KZG kept
real), `symbolic` (proofs; returns a zero 48-byte point for aggregation, never
executed), and `caching`. `caching` memoizes BLS `verify`, the repeated hot path, keyed
by the exact `(pubkey, message, signature)` wire bytes behind an `@[implemented_by]`
swap: the logical definition stays the `ffi` primitive (transparency is `rfl`, in
`Spec/Crypto.lean`), and only the compiled code consults the global memo. The runner
injects `caching`. `CryptoBackend.forBlsSetting blsSetting` is the single home for the
per-case selection (`2` → `verifyOff`, else the real backend), so a `PySpecTests` entry
point writes `CryptoBackend.forBlsSetting cmeta.blsSetting` rather than re-spelling the test.

- **Backends are `@[reducible]`.** A `def` whose result type is a class trips a lint
  unless reducible, and reducibility is what lets `native_decide` reduce the record to
  expose the FFI calls. The hasher tags (`fastHasherTag` / `pureHasherTag`) carry it
  too.
- **Inject by `@`, not a named instance argument.** `[CryptoBackend]` is an anonymous
  instance binder, so a call site picks the backend with `@f CryptoBackend.ffi …` or
  `letI`, not `(CryptoBackend := …)`.

The sync-aggregate participant set is computed one way: the bit-selected committee
pubkeys are passed to `ethFastAggregateVerify`, which aggregates whatever list it is
given. This matches the spec result for all three of its cases (all-participate,
majority-subtract, full list) and keeps the seam to `ethFastAggregateVerify` alone,
with no G1 add/neg and no precomputed-aggregate dependency.

## Engine seam

`EthCLLib.Spec.Engine` is the execution-layer sibling of the crypto seam: a spec
function whose answer belongs to an external execution client routes through a
typeclass. Unlike `CryptoBackend` these ship a global default, the optimistic instance
answering the constant `true` (the seam table in `FRAMEWORK_ARCHITECTURE.md` §1). A
local `letI` overrides it.

Three predicates cross the boundary, split across two classes by what the spec calls
them. `[ExecutionEngine]` holds the two literal `execution_engine.*` methods,
`is_inclusion_list_satisfied` (Heze) and `verify_and_notify_new_payload` (Gloas).
`[DataAvailability]` holds `is_data_available` in its Gloas-and-later form, which is a
free function whose sidecar retrieval the spec marks implementation-dependent.
Fulu's `is_data_available` predates that change and takes the columns the runner
supplies, so it checks them for real and reads no seam.

Each has a refuting pin over the branch no vector reaches: `pinRecordRefuted`
(`Heze/ForkChoice.lean`) for the inclusion-list gate, `pinEngineRefuted`
(`Gloas/ForkChoice.lean`) for the other two.

## State, presets, and the header macro

`State` is the boxed `SSZ.Box _ BeaconState`. Hashing runs through the `[HasherTag]`
seam (`sha`). The `Preset` / `Config` / `Const` three-tier constant system carries the
per-fork values; the fork interfaces are preset-parameterized (`fuluInterfaceFor (P :
Preset) (C : Config)`, `gloasInterfaceFor (P) (C) (forkVersion)`) so `minimal` and
`mainnet` instances coexist (the preset is a parameter, not a global instance), and the
runner selects fork × preset (`pyspec_server [fork] [preset]`).

- **The section header is two macros: `state_preamble` declares, `state_section` opens.**
  The split follows the seam that declarations persist across modules while `variable`s
  do not. `state_preamble BeaconState` runs once in the `State` module and declares
  `abbrev State` plus the concrete-domain `modifyState` (`State → State`); `state_section`
  opens each operation file's `section` and re-establishes the
  `[Preset] [HasherTag] [Config] [CryptoBackend]` selectors plus the monad /
  `MonadStateOf` / `MonadExceptOf` line (`[Config]` / `[CryptoBackend]` are
  instance-implicit, so they attach only to the substeps that use them). Because `State` is declared
  once in a module everyone imports, the declaration is unconditional and needs no guard;
  the variables re-emit per file because they do not persist. The fork-choice counterpart
  is `fork_choice_section map`, which emits the same selectors plus the store variables
  (`{map} [FcMap map]`, `MonadStateOf (Store map)`).
- **`modifyState` carries no binder annotation.** Its concrete `State → State` domain (the
  preamble emits it per fork, since `State` is per-fork) flows the expected type into a
  step's lambda, so `modifyState fun state => …` types `state : State` with no
  `(state : State)`. A generic framework `modifyState` could not do this: its `S` would
  be a metavariable when the `sszUpdate` macro in the body fires.

## State access, indexing, and the error model

Reads and writes go through `sszGet` / `sszUpdate`. The index accessor is chosen by three
questions: is the index _data-derived_ (supplied by a data field and not otherwise bounded), has a
validation already proved it in range, and is a reject channel in scope (a monadic step or
an `Except` query) at the read.

- **A data-derived index with a reject channel** uses `sszGetIdx` / `bitlistGetIdx`
  (`Spec/State.lean`), which build an `Except IndexError` and hand it to `liftErr`,
  surfacing `outOfBounds i xs.size` with the real index and bound (the audit's `likelyBug`
  bucket) rather than masking as a default. This covers the operation reads in a state step
  (`process_attestation`'s participation reads, `process_withdrawal_request`'s balance read,
  the pending-consolidation source reads) and the pure queries that return `Except IndexError`
  because their index is untrusted or a parameter (`get_base_reward`, `get_attesting_indices`,
  the reward-delta helpers), whose monadic callers bind them through `liftErr`.
- **An index a spec validation checks** is read through `assertH (i < size)`
  (`Spec/Assert.lean`): the assert returns the witness, so the read is the proof-carrying,
  reject-free `vs[i]'h.down`, with no default fallback, the bad index having rejected at the
  `assertH`. Plain `assert` stays the Unit-returning form for validations whose proof nothing
  downstream needs. `process_voluntary_exit`, `process_proposer_slashing`, the block-header
  proposer read, and the Gloas withdrawal sweep take this form, ten sites in all.
- **A structurally-bounded index** uses the total bang `vs[i]!` / `vget v i`, or `vmodGet`
  for a `% LEN` ring-buffer read (proof-carrying via the preset length bound). The index is
  provably in range, a `Fin n` iterating a length-`n` vector, a `for i in [0:xs.size]` loop,
  or a constant, so an out-of-range value is impossible. Making the still-total ones
  proof-carrying is the residual recorded in `FUTURE_WORK.md`.
- **A data-derived index in a pure query with no reject channel and a valid-by-construction
  index** reads total `vs[i]!`, resting on the invariant the query assumes (validators /
  balances / participation share a length; the input is well-formed). Making it reject
  means either an `Except` return, when the index is genuinely untrusted (the first case
  above), or the proof-carrying form once the length invariants are proved (`FUTURE_WORK.md`).
  `getWeight`, `computeCommittee`, and the builder-registry queries carry a reject channel
  instead. `getWeight` reads each validator through `sszGetIdx` in `getAttestationScore`.
  `isActiveBuilder` reads the builder through `getAt` and `liftErr`, and
  `getBuilderBalanceAfterWithdrawals` through `sszGetIdx`. `computeCommittee` returns
  `Except StateTransitionError`. It binds its checked bounds, then asserts each position
  below `len(indices)`, as `compute_shuffled_index` does, before its structural reads of
  the permutation and of `indices`.

`vs[i]?` is the faithful option read (`none` past the end); the `GetElem` instance uses
the real validity `i < vs.size`, so `vs[i]!` and `vs[i]?` behave like `Array`'s.

An `SSZList` carries its own collection surface, so spec bodies stay off the subtype's
`.val` projection. `vs.size`, `vs.foldl`, `vs.map`, `vs.any`, `vs.all`, `vs.findIdx?`,
`vs.contains`, `vs.toList`, and `for x in vs` read the list directly. `vs.toArray` hands
back the underlying `Array` for the operations the surface does not cover (`.filter`,
`.qsort`, or passing the buffer to an `Array`-typed helper). `Bitlist` mirrors the list:
`bits[i]!` / `bits[i]?` read a bit, `bits.size` the length. These live in SizzLean
(`Repr/Instances.lean`), next to `SSZList` itself.

`outOfBounds` carries the real index and bound: `sszGetIdx` reads the underlying array,
builds SizzLean's `IndexError (idx, bound)` (a payload-carrying constructor) on a miss, and
hands it to `liftErr`, which converts it to the context monad's reject via `[ErrorConv
IndexError E]`, reporting `i` / `size` directly. Decode failures no longer borrow
`outOfBounds`: deserializing a vector's bytes is the runner's job, not the spec's, so an
`Interface` deserializer's `.error` becomes `RunError.decode` (the runner error type below),
not a fabricated index.

`StoreTransitionError.missingKey` carries the 32-byte root (`Vector UInt8 32`).
`StateTransitionError` and `StoreTransitionError` classify by constructor into the
`ClassifyBucket`s: pass, expected rejection, `todo`, out of scope, likely bug, and
uncaught fault. A checked fault reaches the state machine through
`StateTransitionError.ofArithFault`, which keeps its `ArithCause`: a range fault becomes
`.arithmetic` and a zero divisor becomes `.zeroDivision`.

`RunError E` (`EthCLLib/Spec/Errors.lean`) is the runner-level error one layer above a spec
reject: `decode what` is a wire-deserialization failure (always a bug-smell, a well-formed
vector decodes), `spec e` carries a spec reject of type `E` through unchanged. Every
`ForkInterface` method returns `Except (RunError …) …`; `RunError.classify` (via the
`Classify` class over the two spec error types) sends `decode → likelyBug` and
`spec e → e.classify`, and `RunError.ofSpec` lifts a spec-level `Except` into it once a
method leaves decoding and runs spec code. This removed the old decode hacks (the
`outOfBounds 0 0` fabrication on the state path and the `assert "… decode failed"` on the
fork-choice anchor path), so a decode failure is named for what it is and never masquerades
as a consensus reject.

**Element writes: infallible `[i]!` vs checked `[i]`.** SizzLean's `sszUpdate` element
index comes in two forms. The checked `field[i] := v` is _fallible_ (`Except
IndexError`, matching the pyspec's `IndexError`), for a write that should reject an
out-of-range index. The bang `field[i]! := v` is _total_: it returns the bare `State`,
an out-of-range write being a silent no-op that mirrors `Array.set!`, and it emits the
same spine address and root as the checked form. The reset / caching writes
(`process_slot`'s root caching, the slashings / randao resets, the builder-payment
slots) key an index that is in range by construction (`idx = … % VECTOR_LENGTH`), so
they use `field[i]!`: total (it fits the `modifyState fun state => State` contexts with
no reject path) and, for the composite-element fields (`Vector Bytes32`, the
builder-payment vector), the cached O(log n) single-leaf update rather than an O(field)
rebuild. Both forms work over a preset-resolved (symbolic) cap (the derive's
`capToShapeSyntax` mirror in SizzLean).

**Root caching: `getStateRoot` threads the warm box.** `Box.hashTreeRoot` returns
`(root, warm-box)`, the warm box holding the committed intermediate-node tree, so taking
a root is `modifyGet`-shaped. `getStateRoot` (`Spec/State.lean`) is the primitive that
encapsulates it: it reads the boxed state, takes the root, and writes the warm box back
through `MonadState`, so a later root reuses the tree instead of rebuilding it. It pins
the state type `S` from the section's `MonadState S m` (the state type is an `outParam`),
then recovers the box through the `StateRoot` class, so the box's hasher and value type
need not be inferred as metavariables. The `state_transition` spine and the monadic
interface folds call it. The non-monadic sites use the pure `stateRoot` (root plus warm
box, `Spec/State.lean`), which keeps spec bodies off `Box.hashTreeRoot`: `process_slot`
calls it inside its `Id.run` block, since it needs both halves while it keeps mutating,
and `onExecutionPayloadEnvelope` calls it and returns the warm box, which the handler
stores back into `blockStates`. The pure `stateRoot!` (`Spec/State.lean`) is the discard
form, its `!` marking that it drops the warm box (the convenient-but-lossy variant, like
`Array.get!`). It is reserved for the terminal `Interface` sites, where the root is the
function's return value and the box dies with the call. Whether retention actually caches
is the box flavour's call (a cached box keeps the tree, a pure box does not), so the spec
threads unconditionally and the runner picks the flavour. Memory: the warm tree scales with state size, so at mainnet under high
`pytest-xdist` parallelism the retained trees can exhaust memory and crash workers; the
runner caps `-n` accordingly (mainnet runs at `-n 4`, Gloas mainnet at `-n 2`, until
per-test cleanup lands). That is a runner concern, not a reason to drop the threading
from the spec.

`CaseRequest` renames the pyspec metadata field to `caseMeta`, since `meta` is a
section-modifier keyword that fails to project.

## Authoring conventions

State binders are readable. The threaded state is `state`; where a step's previous state
is not reused, the next binding shadows it (`fun state => Id.run do let mut state :=
state`). Where a `← get` snapshot is read alongside a separate mutable (so two bindings
are live at once), the snapshot keeps `state` and the mutable is `stateAcc`. Element reads
spell out `validator` / `builder`, and the domain abbreviations are expanded:
`latestHeader`, `committeesPerSlot`, `epochsPerVector`, `indexedAttestation`,
`pendingDeposit`, `builderIndex`, `randomBytes`, `syncCommittee`, `prevStateRoot`. The
runner-glue binders follow suit: a post-state is `post`, the fork-choice interpreter's
threaded store is `storeAcc` / `store'`. The terse names that stay are the ones
`SPEC_AUTHORING_MODEL.md` §2.3 does not target: a loop index `i`, a type variable (`H`),
the monad variable, the `acc` of a fold, and one-line record-update callbacks
(`fun b => { b with … }`) whose binder is obvious within its single line.

Spec bodies carry a single `open EthCLLib.Spec`. The module re-exports the SSZ
collection vocabulary (`export SizzLean.Repr (SSZList Bitvector Bitlist)`, plus the
byte / collection / hasher helpers), so a pure spec body needs nothing more (Gloas adds
`open EthCLSpecs.Fulu` for the shared constants and primitive aliases; its component
_types_ are inherited into the Gloas namespace, not opened from Fulu). The residual `open SizzLean.Cache` /
`Hasher` survive only in the interface / fork-choice / upgrade glue, which name the box
representation (`SSZ.Box` / `Sha256` / `HasherTag`) directly; re-exporting those into
the author surface would defeat the `sszGet` / `sszUpdate` encapsulation.

## Module layout

**EthCLLib** (`SPECS_ARCHITECTURE.md` §3.6). §3.6 sketches an `EthCLLib/Forms/{…}` tree
that names concerns rather than a mandated layout. The realized layout is finer: the
author surface under `EthCLLib/Spec/` (`Arith`, `Assert`, `Crypto`, `Errors`,
`FiniteMap`, `Forms`, `Hasher`, `Header`, `Loop`, `SigningRoot`, `State`, aggregated by
`Spec.lean`), the pyspec driver under `EthCLLib/PySpecTests/` (`Driver`,
`Interface`), and the capture base under `EthCLLib/Internal/` (`Capture`). The §3.6
concerns map on: `Preset` / `Monad` / `Box` → `Spec.State` + `Spec.Header`; `Map` →
`Spec.FiniteMap`; `Crypto` / `Arith` / `Loop` → the same-named `Spec.*`; `Interface` /
`PySpecTests` → `PySpecTests.Interface` + `PySpecTests.Driver`. The names `FiniteMap` /
`Errors` / `Header` read better than the sketch, so §3.6 is reconciled by this mapping.

`Spec.Arith` carries `umax` / `umin` / `isqrt`, type-directed `uintToBytes`, byte
conversions, `vget`, `vecSliceEq` (fixed-window byte-slice equality), `vmodGet`
(ring-buffer read index), `shiftWindow`, `sszDrop` / `sszOfArray`, and `bitGet` /
`bitSet`. The checked arithmetic lives beside it: `Spec.Checked` (`Checked`,
`ArithFault`, the lift), `Spec.CLUint` (`CLUint64`, `CLUint8`, and the participation-flag
helpers `CLUint8.hasFlag` / `addFlag`, which return `Checked`), `Spec.CLInt`,
`Spec.CLTotal`, and the scoped elaborator `Spec.Elab` (`FRAMEWORK_ARCHITECTURE.md` §10).
The append lives in SizzLean: `SSZList.push` takes a proof
that the list has room, and `SSZList.push?` / `sszAppend?` return `none` on a full list.
`appendState` (`Spec.Header`) turns that `none` into the `.listFull` fault, the spec's
`List.append` raise, and `setOrAppendState` models `set_or_append_list` on top of it.
`sszOfArray` takes a proof that its array fits. `sszOfArrayM` (`Spec.Header`) is the
spec's `List[T, N](a)` for an array of any size: it raises `.listFull` on too many
elements, over SizzLean's `SSZList.ofArray?`. `Spec.State`
carries `getStateRoot` / `stateRoot` / `stateRoot!`. `Spec.RunState` carries
`MonadRunState`, the class saying a state-machine monad can be run from a starting state,
and `runToRoot` (run a boxed-state action to its post-root, generic over that class, the
state-machine twin of `runOn`). `Spec.NestedMachine` carries `NestedStateMachine` and the
`runNestedStateTransition` / `evalNestedStateTransition` bridges. `Spec.SigningRoot` carries
`htr`, `computeForkDataRoot`, `computeDomain`, `computeSigningRoot`, `isValidMerkleBranch`,
and the signing-root verify combinator `blsVerifySigned`, over `[HasherTag]`. `Spec.Loop`
carries `Step` / `fuelLoop` / `fuelIterateM` / `fuelIterateM!`. `Spec.FiniteMap` carries
`MapKind`, `FcMap` (with `lookupD` / `getOrThrow` / `getOrThrowKey` / `values` /
`filterKeys`), `treeMap`, `hashMap`, and `Hashable (Vector …)`.

**EthCLSpecs** is split by concern within each fork (`SPECS_ARCHITECTURE.md` §3.1); no
`Helpers` / `Base` / `Misc` / `Util` catch-all exists. Fulu component containers are
one file each under `Fulu/Containers/` in topological order (`Fork`, `Checkpoint`,
`Validator`, `Eth1Data`, `BeaconBlockHeader`, `Sync`, `Execution`, `Deposit`,
`PendingOps`, `Withdrawal`); `Containers.lean` re-exports them; `BeaconState` is its own
`Fulu/State.lean`; the block-body / attestation / execution-payload containers stay in
`Fulu/Blocks.lean`. Pure-on-`Validator` predicates (`isActiveValidator`,
`isSlashableValidator`, `isEligibleForActivationQueue`, the credential predicates,
`getMaxEffectiveBalance`) sit in `Containers/Validator`; `isEligibleForActivation` reads
the finalized checkpoint, so it lives in the operation layer.

The Fulu operation layer, by concern in load order: `Time` (epoch/slot conversions,
`computeActivationExitEpoch`, the pure `currentEpochOf` / `previousEpochOf`), `Signing`
(`getDomain`), `Randao`, `Balances`, `Registry` (the read accessors), `Committees`
(with `getBeaconProposerIndex`), `Accessors` (the derived float-ups
`getTotalActiveBalance`, `getUnslashedParticipatingIndices`, block-root reads,
`getPendingBalanceToWithdraw`), `RegistryUpdates` (churn limits, the lifecycle mutators
`initiateValidatorExit` / `slashValidator`, the consolidation / compounding mutators,
`modValidator`, and `isEligibleForActivation`), `Rewards`, `Deposits`. `Committees`,
`Withdrawals`, `EpochProcessing`, `Operations`, `Transition`, `ForkChoice` round it out.

**The read/write seam** (§3.3) splits the Registry concern across the `Committees` row:
the read accessors (`getActiveValidatorIndices`) sit below `Committees` in `Registry`
(because `getBeaconCommittee` needs the active set), the mutators (`slashValidator`) sit
above it in `RegistryUpdates` (because `slashValidator` calls `getBeaconProposerIndex`).
The derived `getTotalActiveBalance` straddles `Balances` and `Registry`, so it floats up
into `Accessors`. This is a split by concern forced by the seam, not a by-kind
`Accessors.lean` / `Mutators.lean` grouping. §3.2's tiny-concern merge allows the
single-predicate `Predicates` row (`isEligibleForActivation`) to fold into
`RegistryUpdates`.

**Naming.** The runner is _PySpecTests_ on both sides: the Lean exe at
`EthCLSpecs/PySpecTests/Server.lean` (the `lean_exe` root), the Python harness at the
package-level `packages/EthCLSpecs/PySpecTests/`. Test libraries are `EthCLLib/Tests/`
and `EthCLSpecs/Tests/` (namespaces `EthCLLib.Tests.*` / `EthCLSpecs.Tests.*`), each its
own `lean_lib`, excluded from the shipped library for free (Lake's default lib glob is
`roots.map Glob.one`, so the main lib never reaches `Tests/`). The
`packages/<Pkg>/<Pkg>/` doubling is forced by namespace-equals-library-name.

The per-fork `ForkInterface` instance and its decode / run glue (`fuluInterfaceFor`,
`stateRootImpl`, the dispatchers, `pyspecPinnedVersion`) live in
`EthCLSpecs.<Fork>.Interface` (`Fulu/Interface.lean`, `Gloas/Interface.lean`), a
sub-namespace kept out of the bare `EthCLSpecs.Fulu` / `EthCLSpecs.Gloas` spec namespace.
The interface is the seam to the pyspec harness, not consensus logic, so it does not
sit among the spec helpers; it reaches the spec's `forkdef`s through the enclosing fork
namespace, and the `Server` selects `EthCLSpecs.<Fork>.Interface.<fork>Interface`.

## Fork choice

Fork choice is the second monadic state machine (`SPEC_AUTHORING_MODEL.md` §3.2,
`FRAMEWORK_ARCHITECTURE.md` §6–7, §9). `Store` (with `map : MapKind` and `[HasherTag]`,
plus the auto `[Preset]`), `LatestMessage`, and the Gloas `ForkChoiceNode` are
`forkstruct`s. The section opens with `fork_choice_section map`; the handlers are `forkdef
on* : StoreTransition Unit` over the typed `StoreTransitionError`. They write the same
`assert` / `todo` the state machine uses (resolved to `StoreTransitionError` through
`SpecReject` from the section's monad), `missingKey` for `FcMap` misses, and the inner
`state_transition` runs through `runNestedStateTransition` (`Spec/NestedMachine.lean`, converting an inner
failure as `StoreTransitionError.transition`). `ForkInterface.runForkChoice` returns `Except (RunError
StoreTransitionError) Unit`, and `Server` classifies the typed reject (`.spec (.todo _)
→ todo`, everything else, a `decode` or any other spec reject, `→ bug`), so no `"TODO:"`
string convention is involved. The `FcStep` wire
protocol the harness builds from `steps.yaml` carries the per-step block / attestation
files; a `block` step also feeds the block's own attestations and attester-slashings.

The interpreter does not own the valid/invalid policy. It runs each step to an `Except
StoreTransitionError (Store)` outcome (`runOn` projects the handler's `EStateM` result),
then pipes it through the framework `checkStepValidity before expectedValid outcome`,
which is the runner's per-step check, fork-agnostic over the store type. The snapshot is
the pre-step store (free, since stores are immutable values): a step expected valid that
succeeds threads its new store; one expected invalid that is rejected rolls back to the
snapshot and continues (the rejection is the expected result); the two mismatches, a valid
step rejected or an invalid step accepted, are returned as the run's failure (the first the
step's own error, the second a typed `assert`). The fork interpreters only run steps and
thread the store; the policy lives in `checkStepValidity`. A step that carries a `valid`
flag is `block`, the standalone `attestation` / `attester_slashing`, and in Gloas the
`execution_payload` envelope and `payload_attestation_message`; a step with no flag (`tick`,
the block's own `is_from_block` sub-attestations) is implicitly `valid := true`. The
harness then reports a returned error by its constructor (a `.todo` as a work-queue
`xfail`, a `.outOfScope` as a `skip`, any
other as a bug-smell test failure). The `valid` flag on the standalone `attestation` /
`attester_slashing` steps matters for the `validate_on_attestation` vectors, where the wire
`valid: false` marks an attestation `on_attestation` is meant to reject.

`on_block` returns early, with the store unchanged, for a block root already in
`store.blocks` (new at v1.7.0-beta.4). Otherwise it reads the current head before inserting
the block and applies the proposer boost only when the block is timely, no boost is already
set, and the block shares the head's dependent root (`get_dependent_root`, gated by
`MIN_SEED_LOOKAHEAD`), the v1.7 rule.

The store clock counts milliseconds at v1.7.0-beta.4: `Store.timeMs` and
`Store.genesisTimeMs` replace the second-based `time` and `genesis_time`. `on_tick` takes
milliseconds. A vector's `tick` step still carries seconds, so the harness casts it through the
checked `Uint64(tick)` and passes `seconds_to_milliseconds` of the result, as the reference
runner does. It reads the `time` check back through `milliseconds_to_seconds`. The clock
values are the checked kind (`SPEC_ARITHMETIC.md`), so `compute_slot_at_time_ms` and
`compute_time_at_slot_ms` raise where pyspec raises, including the zero divisor of a
`SLOT_DURATION_MS = 0` configuration. `get_current_slot` drops the `GENESIS_SLOT +` term.

The linear DAG walks route through fuel-bounded combinators (§12). `getAncestor` and the
`getHead` descent read `store.blocks` as they go, so they thread the store monad through
`fuelLoop`. The one tree walk, `filterNodeTree` (beta.4's node-based replacement for
`filter_block_tree`), recurses over every child inside a fold,
which a linear combinator cannot express, so it keeps a local fuel-bounded `where` helper.
The totality the doc wants is met either way.

The fork-choice weight path runs on checked `Gwei` and raises where the pyspec's `uint64`
operations raise. Its root is `getTotalBalance` (`phase0/beacon-chain.md:1559-1570`), whose
`sum(...)` is a checked fold that returns `Except StateTransitionError Gwei`.
`calculateCommitteeFraction` divides `getTotalBalance` over the unslashed active validators
by `SLOTS_PER_EPOCH` (v1.7.0-beta.4), and `computeProposerScore` and the re-org threshold
are its products. `getAttestationScore` folds the effective balances with the checked add,
and `getWeight`'s proposer-boost add binds the same way. `getTotalBalance` and
`getTotalActiveBalance` return `Except`, so every pure caller carries the reject channel
(§7.1's rule, one layer over). A fault takes a total balance near the `uint64` bound,
which no preset's validator set approaches.

The reference catches different exceptions per step kind, so what satisfies a
`valid: false` step varies too. `expect_assertion_error` (`context.py:451-462`) catches
`IndexError` for the attestation, attester-slashing, envelope, and PTC-message steps.
`add_block` catches `AssertionError` and `BlockNotFoundException` alone
(`fork_choice.py:383-387`). `FcStepKind` carries that table, and `checkStepValidity`
(`PySpecTests/Interface.lean`) reads it.

The Gloas fork choice is the node-based (`ForkChoiceNode = (root, payload_status)`)
ePBS rewrite: `get_ancestor` / `is_ancestor` / `get_weight` / `get_node_children` /
`get_head` thread the payload status, with the ePBS handlers
`on_execution_payload_envelope` (envelope verification) and
`on_payload_attestation_message` (PTC vote recording) and the payload-status / vote
checks; the `FcStep` protocol grows the envelope / PTC-message steps. EIP-7732 genuinely
differs here, so Gloas overrides most handlers rather than inheriting them, and the
`forkstruct` / `inherit` reuse pays off less than it does for the state transition.

## Fulu state transition

`Fulu/Transition.lean` is the spine: `process_slot` (cache state / block roots),
`process_slots` (with `process_epoch` at boundaries), `process_epoch` (the full Fulu
ordering), `process_block_header`, `process_randao`, `process_eth1_data`,
`process_sync_aggregate`, `process_execution_payload`, `process_block`,
`verify_block_signature`, `state_transition`. `Fulu/Withdrawals.lean` holds
`get_expected_withdrawals` (the EIP-7251 pending-partial queue then the Capella
validator sweep) and `process_withdrawals`. `Fulu/EpochProcessing.lean` holds every
`process_epoch` substep; `Fulu/Committees.lean` holds the swap-or-not shuffle and
everything built on it (`get_seed`, `compute_committee` / `get_beacon_committee`, the
balance-weighted sampler, `compute_proposer_indices` / `get_beacon_proposer_indices`,
`get_next_sync_committee`), pure functions of the boxed state. `getBeaconProposerIndex`
reads the precomputed `proposerLookahead` (Fulu EIP-7917), so the proposer needs no
runtime shuffle; only committees and building the lookahead / sync committee do.

Spec-faithfulness facts worth knowing:

- **`process_pending_deposits` resets `deposit_balance_to_consume` by stop reason.** A
  not-finalized / per-epoch-limit stop resets it to zero; a churn-limit stop carries
  `available_for_processing − processed_amount` forward. `processPendingDeposits`
  keeps the pinned text's `is_churn_limit_reached` local, set only in the churn
  branch, and the write-back reads it.
- **The old deposit mechanism is gone.** Fulu removes it (consensus-specs #4704, in the
  text since alpha.12): `process_operations` asserts `len(body.deposits) == 0` and runs no
  deposit loop, `process_deposit_request` no longer writes `deposit_requests_start_index`,
  and `process_pending_deposits` has no eth1-bridge stop. The tree ran the Electra forms of
  all three until the beta.4 re-pin found the gap; `DISCREPANCIES.md` records the fix. Gloas
  carried the same stale eth1-bridge stop in its own `processPendingDeposits`, removed
  with it.
- **`apply_pending_deposit` is signature-gated.** A new pubkey joins the registry only
  when `is_valid_deposit_signature` passes (the proof-of-possession the deposit contract
  does not check). The domain is fixed (`compute_domain(DOMAIN_DEPOSIT)`, genesis fork
  version, zero `genesis_validators_root`), so the check is one `[CryptoBackend].verify`.
- **`initiate_validator_exit` raises past the `uint64` bound.** The `exit_epoch +
  MIN_VALIDATOR_WITHDRAWABILITY_DELAY` sum is the checked `Epoch` add, so an over-range
  case raises the `.arithmetic` fault, the pyspec's `ValueError`.
  `test_invalid_large_withdrawable_epoch` catches it in its own `except ValueError`
  wrapper (`RunnerCaughtSet.valueError`). Valid exits never approach the bound. Gloas
  inherits the substep with no Gloas-side change.
- **The balance-weighted sampler rejects on an empty candidate set.**
  `compute_balance_weighted_selection` asserts `total > 0` (`gloas/beacon-chain.md:1213`),
  so proposer sampling, the sync committee, and `compute_ptc` reject with `.assert` when
  no validator qualifies (zero active, or all slashed under the EIP-8045 filter). No
  conformance vector reaches the empty case; `Tests/GloasCommitteesPins.lean` pins the
  three reject sites. At Fulu this is an error-class divergence. The pyspec's Fulu
  samplers fail differently on empty input. Electra's `get_next_sync_committee_indices`
  computes `i % active_validator_count` unguarded and raises Python `ZeroDivisionError`.
  `compute_proposer_index` raises its own `AssertionError`. Etheorem routes the Fulu
  paths through the same balance-weighted sampler, so every empty-set case rejects with
  `.assert`. Both sides fail the transition; only the reject class differs.
- **`process_execution_payload` takes the execution engine as valid.** It checks
  parent-hash / prev-randao / timestamp consistency and caches the header;
  `verify_and_notify_new_payload` is the consumer's responsibility, which is valid for
  `sanity/blocks`. The timestamp is `compute_time_at_slot(state.genesis_time, state.slot)`,
  beta.4's signature, a checked `uint64` op over `compute_time_at_slot_ms`, and the
  standalone `operations/execution_payload` format threads the test's `execution.yaml`
  engine answer via `CaseMeta.executionValid` to model an engine rejection. The blob count
  is bounded by `get_blob_parameters(epoch).max_blobs_per_block`, read from the
  `BLOB_SCHEDULE` config (`Fulu/BlobParameters.lean`). The tree lacked that assert until the
  beta.4 re-pin; `DISCREPANCIES.md` records the fix. The skip is safe for the in-scope corpus
  by audit, not just by
  assumption: every invalid `sanity/blocks` / `finality` / `random` case (82, across
  both presets and both forks) rejects through a consensus `assert` the in-block
  pipeline models, signatures, blob-count limits, payload-attestation checks, the
  execution-requests root, slot / parent consistency, duplicate operations, the state
  root, so none reaches a clean run that an engine answer alone would have rejected.
  An invalid block that depended on the engine answer would run clean and surface as a
  `likelyBug` "expected a rejection but ran clean", not a silent pass.

`CryptoBackend.aggregatePubkeys` exists because `get_next_sync_committee` needs BLS
pubkey aggregation (the `ffi` / `verifyOff` backends delegate to
`LeanHazmat.Bls.ethAggregatePubkeys`; the `symbolic` backend returns a zero point).

`process_sync_aggregate` verifies against the participants' pubkeys with
`eth_fast_aggregate_verify`, one branch. The Fulu text has three, chosen by
`get_set_bit_count(sync_committee_bits)`: with every bit set it verifies the committee's
cached `aggregate_pubkey`, with more than half set it subtracts the non-participants from that
aggregate, and otherwise it aggregates the participants. The three agree whenever
`aggregate_pubkey` is the sum of the committee's `pubkeys`. `get_next_sync_committee`
guarantees that for every committee the transition builds, but a hand-built state can break
it, and then the one branch can answer differently. Modeling the other two needs BLS point
addition and negation on the crypto seam, which `CryptoBackend` does not carry. This is a
divergence from the spec text that predates the beta.4 re-pin.

## Gloas diff

`EthCLSpecs.Gloas` is `fork Gloas from Fulu` plus the EIP-7732 ePBS diff. The
`BeaconState` is the 46-field ePBS shape: `latestExecutionPayloadBid` replaces
`latestExecutionPayloadHeader`, `latestBlockHash` sits after `nextSyncCommittee`, and
the ePBS tail appends `builders`, `nextWithdrawalBuilderIndex`,
`executionPayloadAvailability`, `builderPendingPayments`, `builderPendingWithdrawals`,
`latestExecutionPayloadBid`, `payloadExpectedWithdrawals`, `ptcWindow`. The containers
are declared in-spec, tracking `specs/gloas/beacon-chain.md` (and `fork.md` for
`upgradeToGloas`). Gloas extends Fulu's three constant tiers with the
ePBS values: `ptcSize` / `maxBuildersPerWithdrawalsSweep` (preset);
`maxPayloadAttestations` /
the builder-payment threshold and builder prefixes and domains (universal); and
`gloasForkVersion` / `gloasForkEpoch` / `gasLimitSchedule` / `churnLimitQuotientGloas` /
`consolidationChurnLimitQuotient` / `maxPerEpochActivationChurnLimitGloas` /
`minBuilderWithdrawabilityDelay` (config). `GLOAS_FORK_EPOCH` is far in the future in both
shipped configs, and `get_ptc` asserts against it (v1.7.0-beta.4), so the runner applies each
vector's `config.yaml` fork-epoch override (`0` for a vector that starts in Gloas, the
`fork_epoch` for a transition vector). The Harness section has the mechanism.

At the alpha.12 re-pin the Gloas (and, by `inherit`, Heze) containers went progressive
(EIP-7495): the state lists, the block-body lists, and the wire lists carry
`ProgressiveList` / `ProgressiveBitlist` fields with no capacity. Two consequences
travel with that switch:

* The `BasicSupported` codec theorems (#117) do not carry over. `BasicSupported`
  names exactly the shapes with landed roundtrip proofs, and the progressive
  constructors are outside it (`SizzLean/Spec/Supported.lean` records the same
  exclusion for `Supported` / `SupportedBounded`). The `Proofs/{Gloas,Heze}/Codec.lean`
  modules are therefore dropped for Gloas and Heze until the progressive roundtrip
  proofs land in SizzLean; Fulu keeps its module. Wire conformance for the
  progressive containers still holds through the `ssz_static` vectors, which the
  runners execute.
* An append to a progressive field can never raise `.listFull` (no cap). The
  `appendState` sites inherited from Fulu keep the #120 raise shape on Fulu's capped
  lists, and the Gloas re-elaborations dispatch on the field: `ProgressiveList.push?`
  is total, so the `none` branch is unreachable there. The two Fulu substeps whose
  bodies pin the capped list constructor (`processPendingDeposits`,
  `processParticipationFlagUpdates`) get Gloas-local bodies that build the
  progressive list directly; Heze inherits those overrides.

`upgradeToGloas` copies the carried-over fields and initializes the ePBS fields, the
cached bid as a self-build bid for the pre-state's latest block (`parent_block_hash`,
`parent_block_root`, `prev_randao`, `slot`, and `BUILDER_INDEX_SELF_BUILD`, filled at
v1.7.0-beta.4) and the PTC window zeroed. `completeUpgradeToGloas` then runs on the boxed
post-state: it fills `ptc_window` with `initialize_ptc_window(post)`, Gloas's own
`compute_ptc` over the Gloas state (beta.4; alpha.12 computed it over the Fulu pre-state),
and onboards builders from the pending-deposit queue
(`onboard_builders_from_pending_deposits`). The split follows the spec, which builds the
state, then writes `ptc_window`, then onboards. `upgradeToGloas` takes `GLOAS_FORK_VERSION` as
a parameter and sets `fork := {previous := pre.fork.current, current := GLOAS_FORK_VERSION,
epoch := currentEpoch}`.

**Epoch inheritance is the framework's reason to exist.** `Gloas.EpochProcessing`
`inherit`s the Fulu epoch substeps and their ~50 helper / time / RANDAO `forkdef`
dependencies verbatim. Each captured Fulu declaration re-elaborates in the Gloas
namespace against `Gloas.State`, sibling calls rebinding to the Gloas copies, no substep
body restated. EIP-7732 changes none of these substeps and `Gloas.BeaconState` carries
every field they read, so the replay typechecks and runs. A short module of `inherit`
statements turns the entire Fulu epoch transition into a green Gloas one; the `inherit`
order is the Fulu load order, so each body's dependencies are already in scope when it
replays.

The churn substeps are the exception: EIP-8061 gives Gloas its own
`CHURN_LIMIT_QUOTIENT_GLOAS` / `CONSOLIDATION_CHURN_LIMIT_QUOTIENT` /
`MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`, so `getExitChurnLimit`,
`getActivationChurnLimit`, `getConsolidationChurnLimit`, `computeExitEpochAndUpdateChurn`,
and `processPendingDeposits` are Gloas `forkdef` overrides ahead of the inherited
exit / registry / consolidation handlers. The Fulu committee helpers are `forkdef`s
inherited into Gloas, which carries `process_sync_committee_updates`,
`process_proposer_lookahead`, the new `process_ptc_window`, the EIP-8045
slashed-proposer filter in `get_beacon_proposer_indices`, and `compute_ptc`.

`Gloas.Operations` inherits the handlers EIP-7732 leaves unchanged (`proposer_slashing`,
`attester_slashing`, `bls_to_execution_change`, `withdrawal_request`,
`consolidation_request`, `sync_aggregate`) verbatim. At v1.7.0-beta.4 the builder-payment
cleanup moved from `process_proposer_slashing` into `slash_validator`, a Gloas `forkdef`
that restates Fulu's body and then voids every pending payment the slashed validator
proposed, on both slashing paths; `process_proposer_slashing` went back to the inherited
body. The ePBS-modified handlers are Gloas `forkdef`s:
`process_voluntary_exit` and `process_deposit_request` (each fronted by a builder-index
branch over the builder registry). The builder-registry helpers (`is_builder_index`,
`is_active_builder`, `get_pending_balance_to_withdraw_for_builder`,
`initiate_builder_exit`, `apply_deposit_for_builder`, `add_builder_to_registry`,
`get_index_for_new_builder`, and the rest) land here and feed
`onboard_builders_from_pending_deposits`. The payload-aware `process_attestation` (the
`data.index < 2` payload bit and the same-slot builder-payment weight accounting), the
new `process_payload_attestation`, the bid (`process_execution_payload_bid`),
`process_parent_execution_payload`, and the PTC read helpers complete the surface.

Two predicates in `Gloas.Operations` handle an attesting index past the
validator registry differently from the spec text:

- **`isValidIndexedAttestation` returns `false` for the out-of-range index.**
  The spec's `is_valid_indexed_attestation` (`specs/gloas/beacon-chain.md:1022-1041`)
  carries no range check, so its bare `state.validators[index]` read raises
  `IndexError`. The Lean forkdef range-checks the indices before the pubkey
  read and answers `false`. Every caller wraps the predicate in an `assert`,
  so both outcomes invalidate the containing block or fork-choice step, and
  the reference runner counts the `IndexError` as the step's expected
  rejection. No conformance vector can observe the difference. The forkdef's
  docstring records the choice (`EthCLSpecs/Gloas/Operations.lean`).
- **`isValidIndexedPayloadAttestation` makes the same choice for the payload
  attestation.** The spec's `is_valid_indexed_payload_attestation`
  (`specs/gloas/beacon-chain.md:1094-1110`) reads `state.validators[index]`
  bare over the PTC-derived indices and raises `IndexError` the same way. The
  Lean forkdef returns `false` on an out-of-range index. Its callers,
  `process_payload_attestation` and the fork-choice payload-attestation
  message handler (`on_payload_attestation_message`), assert the predicate,
  so a bad index rejects the containing block or step on both sides and no
  vector can tell the two outcomes apart. The docstring on the forkdef
  records it (`EthCLSpecs/Gloas/Operations.lean`).

The v1.7.0-beta.4 changes to that surface:

- `process_block` reads `parent_slot = state.latest_block_header.slot` before
  `process_block_header` replaces the header, and passes it through `process_operations` to
  each `process_attestation`, where `get_attestation_participation_flag_indices` reads the
  payload-availability bit at the parent's slot. A validator adds its effective balance to
  the slot's payment weight only when it held no flag before the attestation
  (`had_no_participation`).
- `get_ptc` asserts `epoch >= GLOAS_FORK_EPOCH`, so a pre-fork slot has no PTC.
- `apply_parent_execution_payload` takes the parent slot from the latest block header, where
  alpha.12 read the cached bid's slot, and settles the builder payment before it processes
  the parent's execution requests, so a builder exit in the same payload sees the payment
  still pending.
- `process_execution_payload_bid` asserts `bid.block_hash != bid.parent_block_hash`.
- The builder sweep in `get_builders_sweep_withdrawals` reads
  `get_builder_balance_after_withdrawals`, the balance net of the withdrawals already queued
  in the payload, so a builder is not paid twice. `apply_withdrawals` floors with
  `saturating_sub`.
- `verify_execution_payload_envelope_signature` moves into the beacon-chain document and
  returns `Except StateTransitionError Bool` (its bare indexed reads raise); its fork-choice
  caller wraps the reject.

The builder-aware `process_withdrawals` is the four-phase sweep (builder queue, pending
partials, builder sweep, validator sweep) with the running-list cap that composes across
phases. `Gloas/Transition.lean` reshapes `process_block` (drop
`process_execution_payload`, prepend `process_parent_execution_payload`, add
`process_execution_payload_bid`, payload-free `process_withdrawals`, the in-body
`process_payload_attestation`s), `process_slot` (clear the next slot's
payload-availability bit), and `process_epoch` (builder-pending-payments and
`process_ptc_window` last). The `transition` format folds pre-fork Fulu blocks, applies
`upgradeToGloas` plus onboarding at the boundary, then folds post-fork Gloas blocks.

## Heze diff

EIP-7805 changes no state-transition substep. At v1.7.0-beta.4 two other EIPs do, so
Heze re-instantiates the Gloas spine with three changes:

- **EIP-8015 removes the eth1 deposit machinery.** `BeaconState` drops `eth1_data`,
  `eth1_data_votes`, `eth1_deposit_index`, and `deposit_requests_start_index`, and
  `BeaconBlockBody` drops `eth1_data` and `deposits`. Both stay progressive containers with
  gaps at the removed positions (`active_fields` 0 bits), which the SizzLean deriving handler
  expresses as `@[sizzlean_progressive_gaps …]` and the `forkcontainer` replay carries
  through. `process_block` loses `process_eth1_data`, `process_epoch` loses
  `process_eth1_data_reset`, and `process_operations` loses its deposits assert.
  `upgrade_to_heze` opens with `assert pre.eth1_deposit_index ==
  pre.deposit_requests_start_index`, so it returns `Except`.
- **EIP-8365 stops new validators with BLS withdrawal credentials.** Heze's
  `apply_pending_deposit` returns early for a new pubkey whose credentials carry
  `BLS_WITHDRAWAL_PREFIX`.
- **The inclusion-list signature reads `compute_fork_version`.** The domain takes the fork
  version of the list's own epoch, where alpha.12 read the state's fork through
  `get_domain`.

The fork-choice inclusion-list layer is the rest of the diff. At beta.4 the
`InclusionListStore` is keyed by `(slot, dependent_root)`, each stored entry carries its
own timeliness, `on_inclusion_list` asserts the retention window, the transaction sizes,
the dependent block, and committee membership on the dependent state, and
`record_payload_inclusion_list_satisfaction` takes the slot from the block in the store
and the key from its shuffling dependent root. FOCIL ships no behavioral conformance vector
at the pin, so the divergences below are anchored to the pinned spec text and the
`EthCLSpecs.Tests.HezeForkChoicePins` pins.

- **`is_inclusion_list_satisfied`** (`heze/fork-choice.md:54-62`) defers its answer to
  `ExecutionEngine.is_inclusion_list_satisfied`, an Engine-API call against an external
  execution client. This harness has no execution layer, so the call goes through the
  `[ExecutionEngine]` typeclass (the Engine seam above), whose default instance answers
  the constant `true`. That default is the execution-layer trust boundary of the FOCIL
  gate. No conformance vector reaches the discriminating `false` branch.

- **The `InclusionListStore` rides inside the fork-choice `Store` as a field.** The
  spec keeps it as a process-lifetime singleton reached through
  `get_inclusion_list_store()` (`heze/inclusion-list.md:52-58`), and this framework has no
  ambient singleton to hang it off. Behavior is identical. The rationale lives on the
  `InclusionListStore` declaration (`EthCLSpecs/Heze/ForkChoice.lean`).

## Tier membership follows the upstream file

A value's tier is decided by the upstream file that declares it, never by whether
the two presets currently agree on it. Everything under
`presets/{minimal,mainnet}/*.yaml` is a `Preset` field, everything under
`configs/{minimal,mainnet}.yaml` a `Config` field, and a value the spec lists in a
constants table (weights, flag indices, domain tags, sentinels, prefix bytes)
stays flat in `Const`.

Reading that rule off the documents has one trap worth naming, because it is the
one that bit. The beacon-chain documents write `## Constants` and `## Preset`; the
fork-choice documents write `### Constant`, singular, one heading level deeper. A
sweep that matches only the beacon-chain shape drops every fork-choice constant
and comes back clean.

The rule earns its keep on the preset side, where a value shapes a type. A flat
literal for a preset-file value looks right for as long as the two files agree,
and the day one of them moves it produces a wrong cap, a wrong Merkle root, and a
green build. Config values never shape a type, so a wrong one shows up as a wrong
number and conformance catches it.

`scripts/check_constant_tiers.py` (`just check-constants`) is the standing check,
over both the tier and the fork that introduces each name. It moved 58 entries
when it was first run against the pinned `v1.7.0-alpha.11` documents: 47
preset-file values and 10 config-file values that were flat literals, plus one
constant filed under the wrong fork (below).

Two constants have no upstream table, so the attribution the check relies on
cannot place them. `G2_POINT_AT_INFINITY` is defined in the BLS document, and
`MAX_RANDOM_VALUE` is a local inside Electra's
`compute_balance_weighted_selection`. Both are ordinary flat `Const` entries,
placed by reading the spec text; the check lists them by name each run so a
re-pin re-examines them.

Two entries carry the phase 0 caps `MAX_ATTESTATIONS` (128) and
`MAX_ATTESTER_SLASHINGS` (2) beside their Electra successors (8 and 1). Nothing
at this fork reads the phase 0 pair; the Electra block body reads
`maxAttestationsElectra` / `maxAttesterSlashingsElectra`. They are kept because
they are distinct upstream keys, and set to the upstream values so the tier reads
as a faithful transcription of the file.

## A constant can arrive later than the function that reads it

`CONSOLIDATION_CHURN_LIMIT_QUOTIENT` sat in Fulu's `Config` and belongs to Gloas.
Electra has `get_consolidation_churn_limit`, but it computes a difference of two
churn limits and names no quotient; EIP-7732 rewrites the function to divide the
total active balance by a quotient of its own, and the constant arrives with it.
The name appears in no pre-Gloas document.

The trap generalizes: a fork can keep a function's *name* while replacing its
body, so "Electra already had this function" is not evidence that Electra had its
constants. Attribution has to come from the document that tables the constant,
not from the call site.

## Config-tier values that bite

Three config values differ enough between presets to be worth flagging, because each one
was a real reject-faithfulness gap until set per preset:

- **`MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`** is `128000000000` Gwei at minimal,
  `256000000000` at mainnet. It only binds in `consolidation_request`, where a
  large-balance state pushes the balance churn between the two maxima, so
  `get_consolidation_churn_limit = balance_churn − activation_exit_churn` needs the right
  minimal value. The exit / registry vectors floor at `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA`
  below both maxima, so the cap never binds there.
- **`GLOAS_FORK_VERSION`** is `0x07000001` at minimal, `0x07000000` at mainnet.
  `upgradeToGloas` takes it as a parameter so the gloas `fork` format matches at both
  presets.
- **`MIN_BUILDER_WITHDRAWABILITY_DELAY`** is `2` at minimal, `8192` at mainnet. It bites
  only on the builder-exit branch at mainnet (minimal's `2` is correct), where
  `initiate_builder_exit` sets the builder's `withdrawable_epoch`. The full mainnet sweep
  is what exercises it.

Two more config values are read by v1.7.0-beta.4 code and differ per vector rather than per
preset:

- **The fork schedule.** Fulu's `Config` carries every `*_FORK_VERSION` / `*_FORK_EPOCH`
  pair from Altair on, Gloas adds `GLOAS_FORK_EPOCH`, and Heze adds `HEZE_FORK_EPOCH`. The
  shipped minimal config sets every epoch far in the future; a vector overrides them in its
  own `config.yaml`. Two sites read them: `get_ptc`'s `GLOAS_FORK_EPOCH` assert and Heze's
  `compute_fork_version`, which the inclusion-list signature domain takes.
- **`BLOB_SCHEDULE`** feeds `get_blob_parameters`, the blob-count bound in
  `process_execution_payload` and the data-column sidecar check. It is empty at minimal, and
  mainnet lists two BPO steps. No in-scope vector overrides it.

## Harness

`pyspec_server` is a long-lived, crash-tolerant loop (a malformed request reports failed
and the loop continues), one per `pytest-xdist` worker via the `conftest.py` session
fixture (re-spawn on death). `harness.py` does acquisition / walk / snappy / request
encoding; `test_pyspec.py` is the reject-faithfulness check. The server emits one
tab-separated line per case, so two detail sources that could embed a newline and
desync the worker are flattened at the chokepoint: `EthCLLib.Spec.sanitizeDescr` takes
the first trimmed line of an `assert` descriptor, and `CaseResult.render` flattens any
newline / tab in the detail to a space (the detail is diagnostic only). The
`ServerClient` drains non-protocol lines (lake / startup stdout) and retries once on a
desynced or dead server, so the parallel run is deterministic.

Three request fields are new at the v1.7.0-beta.4 re-pin:

- **`cfg=`**, the trailing field of every request: the case's fork-epoch overrides, read
  from its `config.yaml` (`<FORK>_FORK_EPOCH` keys) and, for a `transition` vector, the
  post-fork's epoch from `meta.yaml`. The server builds the fork interface for the case from
  the preset's config with those values set (`applyConfigOverrides`). A key the fork does not
  model is accepted only at the far-future value; any other value is an error, so an
  override never drops silently.
- **`parent_slot`**, field 10 of an `operations/attestation` request at Gloas and Heze,
  from the case's `meta.yaml`. `process_attestation` takes it.
- **`viable_for_head`**, a fork-choice check line built from the
  `viable_for_head_roots_and_weights` check: the expected set of leaves in the filtered
  node tree, each with its weight and (Gloas on) payload status. The comparison is as sets.

A `tick` step's time is in seconds in the vectors, and the harness sends
`seconds_to_milliseconds(tick)` to `on_tick`, as the reference runner does.

## Genesis

`SPECS_ARCHITECTURE.md` §10.1 marks `genesis` in scope and §6.1 names
`initializeBeaconStateFromEth1` / `isValidGenesisState`. The pytest corpus carries no
`genesis` vectors for Fulu, Gloas, or Heze at the `v1.7.0-beta.4` pin, so there is nothing to
drive; both stay a `todo` stub in `Interface.lean`.

## Proofs

Consensus proofs currently live in `EthCLSpecs.Proofs`
(`EthCLSpecs/EthCLSpecs/Proofs/`), colocated with the consensus specifications
and remaining mathlib-free, following the `SizzLean.Proofs` pattern. The
standalone `EthCLProofs` package described in `SPECS_ARCHITECTURE.md` and
`PLAN.md` remains reserved for proofs that require mathlib, following the
conditional design described in `SPECS_ARCHITECTURE.md` §11.3 and the
`LeanPoseidonProofs` containment pattern. No current proof requires that
separation.

- **`Proofs/Gloas/BuilderIndex.lean`** establishes three `bv_decide` theorems over
  `isBuilderIndex`, `toBuilderIndex`, and `convertBuilderIndexToValidatorIndex`,
  proving the builder-index flag round-trip and tagging properties.

- **`Proofs/Gloas/GetPtc.lean`** proves `getPtc`'s `else`-branch offset into
  `ptcWindow` stays in range for its two guarded call sites:
  `getPtcElseOffset_lt_next_slot` under `process_payload_attestation`'s guarantee
  (`data.slot + 1 == state.slot`), and `getPtcElseOffset_lt_same_slot` under
  the fork-choice replay callers' exact-equality guarantee (`slot ==
  curSlot`). Both via `UInt64`/`Nat` bridging lemmas and `omega`, no mathlib.

- **`Proofs/Gloas/BuilderPendingPayments.lean`** proves `processBuilderPendingPayments`'s
  local behavior for one call. A quorum error propagates and returns no state.
  After a successful quorum computation, the withdrawals loop reduces to a
  `ProgressiveList.push` fold over the qualifying previous-epoch payments' withdrawals,
  in slot order, and the payment window shifts down by `SLOTS_PER_EPOCH`. Every
  qualifying withdrawal is appended. It does not prove protocol-wide exactly-once settlement or say
  anything about `settleBuilderPayment` / `slashValidator`, the other paths
  that clear a `BuilderPendingPayment`.

- **`Proofs/Gloas/CanBuilderCoverBid.lean`** characterizes `canBuilderCoverBid`, whose
  result is an `Except StateTransitionError Bool`: the raising builder read, then the
  checked `Gwei` chain. `canBuilderCoverBid_eq` is the exact run equation.
  `canBuilderCoverBid_ok_iff` states that, under the read's success, the pending sum's
  success, and the success conditions of the `+` and `-` steps, `true` is exactly the
  bid fitting the remainder, as one `Nat` inequality. `canBuilderCoverBid_ok_toNat_add_le`
  restates it as an addition-fits-in-balance fact.

- **`Proofs/Gloas/InitializePtcWindow.lean`** gives the whole vector equation
  `initializePtcWindow_eq` over the window entries: each entry is an `Except`
  carrying its own faults, the checked per-entry add `current_epoch + e`
  (the `.arithmetic` fault at `current_epoch = UINT64_MAX`), the checked
  `compute_start_slot_at_epoch` product, the checked `start_slot + index` add, and the
  `compute_ptc` read (the empty-candidate reject), and `completeUpgradeToGloas` maps the
  entries in index order. Its two index regions (the empty first-epoch
  placeholder and the remainder binding the checked add then Gloas's
  `computePtc`) are read off the equation, `initializePtcWindow_getElem` joins
  them at the element level, and a `default` corollary restates the first
  region. The equation carries
  `@[characterizes EthCLSpecs.Gloas.initializePtcWindow]`. At v1.7.0-beta.4 the
  function is a Gloas `forkdef` over the Gloas state; alpha.12 kept it a plain
  `def` over the Fulu pre-state, outside the coverage denominator.

- **`Proofs/Gloas/InitiateBuilderExit.lean`** gives the whole-transition
  `initiateBuilderExit_run_eq` contract at the box. An out-of-range builder index
  raises `outOfBounds`. An in-range index reaches the checked epoch-plus-delay add.
  An addition fault propagates. A successful addition writes the builder through
  `ProgressiveList.set!` and returns the updated pure box. The success theorem
  requires both the in-range index and the sum bound. The shipped minimal and
  mainnet corollaries discharge the sum bound and keep the in-range index premise.

- **`EthCLLib/Proofs/Run.lean`** (framework package) names the `StateT`-over-`Except`
  bind, throw, and
  `Except` facts every pure runner rewrites with (`run_bind`, `run_pure`,
  `run_throw`, `except_bind_ok`, `except_bind_error`). They are stated at an
  arbitrary state and error type, so they apply to `GloasRun` and
  `ForkChoiceStoreRun`. The same module pins the box:
  `pureState v` is the uncached box of the plain value, `runPure act v` runs an
  action on it and returns the result as a value. A contract theorem states the
  run at the box level, `act.run (pureState v) = .ok (a, pureState w)`, which
  the nested-machine bridge consumes by application, and `runPure_of_run_ok`
  derives the `runPure` form from it. `runPure_eq`, `runPure_pure`,
  `runPure_throw` are the remaining `rfl` facts proofs rewrite with. There is
  no `runPure_bind`: a bind law would have to know every intermediate box is
  uncached, so a composite body goes through `runPure_eq` to the box level.
  The module lives in the framework's generic proof toolkit,
  because the facts belong to no fork.

- **`Proofs/Gloas/Run.lean`** names `GloasRun`, the pure `StateT`/`Except`
  state-transition monad the Gloas proofs pin their `forkdef` bodies to.
  `StateTransition` is a parameter of a fork body, so every run theorem has to fix
  it; this fixes it once. Gloas call sites use the `EthCLLib/Proofs/Run.lean` facts
  (`run_bind` and friends) directly, as Heze does.

- **`EthCLLib/Proofs/StoreRun.lean`** (framework package) names `ForkChoiceStoreRun`, the shared pure
  store-machine runner every fork's fork-choice proofs pin at that fork's
  `Store`. It also holds the store-specific equations under the store machine's
  `.transition` wrapper: `throwArithmetic_run` and `throwZeroDivision_run` for the two
  explicit throws, and `liftChecked_ok_run` / `liftChecked_error_run` for a lifted
  checked expression, whose fault becomes `.transition (StateTransitionError.ofArithFault e)`. The generic `StateT`/`Except` equations live in
  `EthCLLib/Proofs/Run.lean`. The module lives in the framework's generic
  proof toolkit because the runner is a monad over an arbitrary store type
  and so belongs to no fork.

- **`Proofs/Gloas/IsValidIndexedPayloadAttestation.lean`** proves a two-layer,
  backend-generic characterization of `isValidIndexedPayloadAttestation`. Layer 1
  mirrors the implementation's literal validation gates, `validators[i.toPlainNat]!`
  included. Layer 2 restates them semantically and binds the in-range proof in an
  `∃`, so its pubkey array reads the registry through `Array.attach` and no
  panicking index survives into the public statement. No mathlib.

- **`Proofs/Gloas/ProcessOperations.lean`** places its public declarations in
  `EthCLSpecs.Proofs.Gloas`. It characterizes Gloas `processOperations` at
  `GloasRun`; handlers and later failure postconditions remain opaque. Every
  statement takes the beta.4 `parentSlot` argument, and the attestation fold is
  `processAttestation · parentSlot`. The `KeepsUncached` facts behind its split
  (`Proofs/Gloas/KeepsUncached.lean`) cover the beta.4 bodies: `slashValidator`'s
  payment loop through `pureState_forIn_range_id`, and `processAttestation`'s
  `had_no_participation` read through `keepsUncached_sszGetIdx` and `ite_bind`
  (`EthCLLib/Proofs/KeepsUncached.lean`, `EthCLLib/Proofs/Run.lean`).

- **`EthCLLib/Proofs/LawfulFcMap.lean`** places its public declarations in
  `EthCLLib.Proofs`. It defines the key-indexed `LawfulFcMap map K` interface
  and generic same-key insertion theorems, with concrete instances for
  `treeMap` and `hashMap`. The FOCIL handler postconditions that use those
  laws remain tracked by the `onExecutionPayloadEnvelope` entry in
  `PROOF_LEDGER.md`.

- **`Proofs/Heze/IsPayloadInclusionListSatisfied.lean`** places its theorems in
  `EthCLSpecs.Proofs.Heze`. `isPayloadInclusionListSatisfied_run` is the
  complete `.run` equation at `ForkChoiceStoreRun (Store map)` and carries
  `@[characterizes]`. A missing satisfaction key is the membership assert. A
  recorded value is returned only when the payload is verified, otherwise
  `false`. The four corollaries name the missing-record reject, an unverified
  recorded value, a recorded `false`, and a recorded `true` with a verified
  payload. Success leaves `runnerStore` unchanged. Verdict production and
  payload/verdict pairing remain later handler work, tracked by the
  `onExecutionPayloadEnvelope` entry in `PROOF_LEDGER.md`.

- **`Proofs/Heze/ShouldExtendPayload.lean`** places its theorems in
  `EthCLSpecs.Proofs.Heze` because `shouldExtendPayload` exists in both Gloas
  and Heze. `shouldExtendPayload_run` is the complete `.run` equation at
  `ForkChoiceStoreRun (Store map)` and carries `@[characterizes]`. The
  right-hand side is the evaluation order: block lookup, the slot increment,
  `getCurrentSlot`, the slot assertion, `isPayloadVerified`,
  `isPayloadInclusionListSatisfied`, then the inherited Gloas tail. Named
  corollaries cover the prefix rejects, the FOCIL gate, the vote membership
  asserts, and the inherited Gloas accept and reject arms. Successful binds
  keep the intermediate runner states. A reject returns the error alone.
  `shouldExtendPayload_run_eq_false_of_recorded_unsatisfied` survives as a
  corollary: if the initial block lookup and slot checks succeed, Heze
  rejects a verified payload when the queried root has a recorded `false`
  inclusion-list satisfaction result, and the runner state remains
  unchanged. The bind lemmas it cites are the fork-neutral `run_bind`, `run_throw`,
  `except_bind_ok`, and `except_bind_error` in `EthCLLib/Proofs/Run.lean`. They
  are stated at an arbitrary state type, so they apply to
  `ForkChoiceStoreRun`. The checked slot increment reads through `hadd_un_eq`
  (`EthCLLib/Proofs/CLUint.lean`). The successful path that records
  the result of `isInclusionListSatisfied` is proved in
  `Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`. The successful
  handler path that writes `blockStates`, `payloads`, and
  `payloadInclusionListSatisfaction` at the same
  `signedEnv.message.beaconBlockRoot` is proved in
  `Proofs/Heze/OnExecutionPayloadEnvelope.lean`. Handler postconditions
  that pair `payloads[root]` with the satisfaction entry, and composition of
  those writes with this read, remain tracked by the
  `onExecutionPayloadEnvelope` entry in `PROOF_LEDGER.md`.

- **`Proofs/Heze/GetInclusionListTransactions.lean`** proves the committee run
  equation and the transactions contract.
  `getInclusionListCommittee_run_eq` is the complete committee `.run`
  equation on the concatenated `getBeaconCommittee` indices, tagged
  `@[characterizes EthCLSpecs.Heze.getInclusionListCommittee]`; the empty
  array throws the exact empty-committee arithmetic error. At v1.7.0-beta.4
  `getInclusionListTransactions` is pure, and
  `mem_getInclusionListTransactions_iff`, tagged
  `@[characterizes EthCLSpecs.Heze.getInclusionListTransactions]`, states its
  result: a transaction is in it exactly when the list of a counted item for
  the key carries it (sender not an equivocator for the key, entry timely when
  only timely lists count). `getInclusionListTransactions_nodup` proves the
  result holds no duplicate, and
  `not_mem_getInclusionListTransactions_of_equivocators` names the equivocator
  exclusion. The items are `inclusionListItems`, the map fold, since `FcMap`
  has no fold law. The list-membership lemmas `mem_arrayUnion_iff` and
  `nodup_arrayUnion` live in `EthCLLib/Proofs/Arith.lean`.

- **`Proofs/Heze/RecordPayloadInclusionListSatisfaction.lean`** proves
  `recordPayloadInclusionListSatisfaction_run` in
  `EthCLSpecs.Proofs.Heze` and tags it
  `@[characterizes EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction]`.
  The equation is complete at `ForkChoiceStoreRun (Store map)`. A block
  missing from `store.blocks` is `missingKey root`, and a slot-zero block is
  the checked-sub arithmetic error. Otherwise the result matches on the
  dependent-root walk at the previous slot's epoch. A walk error is returned
  unchanged. A successful walk returns `store` with
  `payloadInclusionListSatisfaction[root]` set to
  `isInclusionListSatisfied payload ilTxs`, for the timely transactions
  `ilTxs` stored under `(block.slot - 1, dependentRoot)`, paired with the
  walk's runner state. Public corollaries name the missing block, slot zero,
  and an arbitrary walk error. `recordPayloadInclusionListSatisfaction_run_eq`
  restates the successful branch. The generic `FcMap` interface does not
  specify how insert affects a later lookup.

- **`Proofs/Heze/OnExecutionPayloadEnvelope.lean`** proves
  `onExecutionPayloadEnvelope_run` in `EthCLSpecs.Proofs.Heze` and tags it
  `@[characterizes EthCLSpecs.Heze.onExecutionPayloadEnvelope]`. The
  equation is complete at `ForkChoiceStoreRun (Store map)`. Missing
  `blockStates` and failed data availability are `.assert` errors.
  Verification and recorder errors propagate unchanged. On recorder
  success the handler's final `set` writes `blockStates` and `payloads`
  on the recorder's explicitly returned store and discards the
  recorder-produced runner state. `.error err` contains no post-state.
  `onExecutionPayloadEnvelope_run_eq_of_successful_checks` restates the
  successful branch as the original store updated by three same-root
  `FcMap.insert` expressions. `recordPayloadInclusionListSatisfaction_run`
  characterizes the recorder's missing-block, slot-zero, and walk outcomes. The
  `proposed` `onExecutionPayloadEnvelope` row in `PROOF_LEDGER.md` lists
  lookup-after-insert and composition with the read-side theorems.

- **`Proofs/Gloas/UpdateCheckpoints.lean`** rewrites Gloas's `updateCheckpoints` as a
  single record update, which doubles as the frame condition that no other Store
  field moves. On top of it sit unchanged-or-advances characterizations for the
  justified and finalized checkpoints, plus monotonicity corollaries proving that
  neither recorded epoch decreases. The proofs use ordinary case analysis and
  core `UInt64` ordering lemmas. Their theorems live in `EthCLSpecs.Proofs.Gloas`
  rather than the flat `EthCLSpecs.Proofs`, since Fulu declares the same function.

- **`PROOF_LEDGER.md`** tracks candidate consensus proof targets and their status.

## Stage 9 documentation audit record

### Scope, revisions, and counting

This record consolidates the eight documentation families of WS-92, task 9.2
(WS-101). The source tree is `epic/WS-92` at `40d5e58`. It includes all eight
family merges and the four 9.5 code tasks. The arithmetic contract is
`SPEC_ARITHMETIC.md`; the Python pin is `eth_consensus_specs` 1.7.0b4,
spec tag `v1.7.0-beta.4`.

The tables below count resolved finding groups. One row is one group, even when
several declarations share the correction. Review corrections to an existing
group replace its first answer. Separate review findings have separate rows.
Inspected matches that need no edit appear under retained dispositions and do
not increase these counts. Cross-family rows track shared resolutions separately;
their counts must not be added to the family counts.

| Family | Audited corpus | Resolved groups | Delivered head |
|---|---|---:|---|
| 9.1a, WS-97 | `SPEC_ARITHMETIC.md`, `SPEC_AUTHORING_MODEL.md`, `SPEC_ARITHMETIC_LINTING.md`, and root `docs/CODING_STYLE.md` | 23 | `c5c7b09` |
| 9.1b, WS-98 | This directory's `FRAMEWORK_ARCHITECTURE.md`, `SPECS_ARCHITECTURE.md`, `IMPLEMENTATION_NOTES.md`, `DISCREPANCIES.md`, `PROOF_LEDGER.md`, `FUTURE_WORK.md`, `PLAN.md`, and `README.md` | 15 | `e86a07e` |
| 9.1c, WS-99 | Root README, contributor and agent instructions, security and conduct documents, PR template, `docs/monorepo-arch.md`, EthCLSpecs and PySpecTests READMEs; SizzLean README, manual and documents; hazmat, LeanRlp, LeanPoseidon, LeanSha256 documents; `scripts/compbench/README.md` | 3 | `b7bbaf6` |
| 9.1d1, WS-100 | All 28 EthCLLib files: `Spec/`, `Internal/`, `EthCLLib.lean`, `Spec.lean`, `Proofs.lean`, and `Tests.lean` | 22 | `f074361` |
| 9.1d2, WS-107 | All 30 EthCLLib files in `Proofs/`, `Tests/`, `PySpecTests/`; targeted searches over 217 Lean files in SizzLean, hazmat, LeanRlp, LeanPoseidon, LeanPoseidonProofs, LeanSha256, and `scripts/ProofCoverage.lean` | 10 | `2c6c605` |
| 9.1d3, WS-108 | The 33 Fulu files, including containers, plus `EthCLSpecs.lean`, `Forms.lean`, `Fulu.lean`, `Gloas.lean`, `Heze.lean`, `Proofs.lean`, and `Tests.lean`, 40 files total | 19 | `4792eb3` |
| 9.1d4, WS-109 | All 37 files in Gloas and Heze, including containers and interfaces | 18 | `311b724` |
| 9.1d5, WS-110 | All 58 files in EthCLSpecs `Proofs/`, `Tests/`, `PySpecTests/`, and the bench | 26 | `3fbe87d` |

The total is 136 resolved family groups. The 9.1d5 count of 58 files includes the
three pin modules added by 9.5a, 9.5b, and 9.5c. Its issue estimated 55 files.
The temporary arithmetic plan is outside the family corpus. Task 9.3 owns the
integrated verification sweep; task 9.4 owns the index and status updates.

Source hand-offs are issue comments. These IDs preserve the detailed evidence:

| Family | Findings and final corrections, comment IDs |
|---|---|
| 9.1a | `01a1fc1f-76c7-777e-9a77-edc7878a71a6`; `01a1fc25-1d88-734b-95e0-f2dbec3d0013` |
| 9.1b | `01a1fc1f-f8dc-7522-b726-0c868a56e2ca`; `01a1fc22-8303-73f4-84ed-6c6cfb29d066`; `01a1fc25-36ef-7ef8-84eb-5408a3fd48b4` |
| 9.1c | `01a1fc21-bcc4-726e-aa79-320a34cb3a3c`; `01a1fc26-eeb0-7104-ab3b-f7e1846711da` |
| 9.1d1 | `01a1fc37-d58d-718a-b6f8-74ee6299d0b5`; `01a1fc58-7b51-79d3-8d94-d65969ac2576`; `01a1fce1-e3fe-7783-89a1-57cecccf4187` |
| 9.1d2 | `01a1fc6c-fbe6-7cae-91bd-61186e01ef9c` |
| 9.1d3 | `01a1fd07-02d1-70bb-82a0-eab3fce8de10` |
| 9.1d4 | `01a1fcea-9800-7589-8c7e-347b99b17e80`; `01a1fd50-d6ba-7c23-912f-4a491e86c677` |
| 9.1d5 | `01a1fd0b-755b-705e-8bb4-77660a57efc5`; `01a1fd2f-9656-7300-893a-82bf4c8c993a`; `01a1fd46-1a44-71ac-8298-ab68504ed10f` |

### Family findings and resolutions

Paths in A and B are relative to this directory, except root `docs/CODING_STYLE.md`.
Paths in D1 and D2 are relative to `packages/EthCLLib/EthCLLib/`.
Paths in D3 through D5 are relative to `packages/EthCLSpecs/`.

| ID | Document or site | Conflict and recorded resolution |
|---|---|---|
| A01 | Arithmetic §2 | The Heze assertion count omitted configuration checks. Records 177 function assertions and 13 module assertions, 190 total. |
| A02 | Arithmetic §4.1 | The fault row invented a shift-count cause. Names `.range` and `.zeroDivision`; a negative shift count is `.range`. |
| A03 | Arithmetic §4.2 | The matrix omitted implemented operand pairs and operators. Adds Lean `Int`, bitwise, shifts, power, positive divisors, mixed `&&&`, and 8-bit routes. |
| A04 | Arithmetic §4.3 | The reward example used the wrong read and a placeholder write. Uses the body's `liftErr (getAt rewards vi)` and `setAt`. |
| A05 | Arithmetic §4.5 | The sum seed lacked its type. Uses `(0 : Gwei)` and states the checked-fold behavior. |
| A06 | Arithmetic §4.5 | The literal gate was hypothetical. Names the implemented `NeZero` bounds at both widths. |
| A07 | Arithmetic §4.6 | The indexing description omitted `idx?` and helper names. Matches `ToIndex`, `getAt`, `setAt`, and `sszGetIdx`. |
| A08 | Authoring §5 | The boundary table taught raw `UInt64` arithmetic. Describes the checked surface. |
| A09 | Authoring §§6–7 | Two slot increments omitted binds. Each binds `nextSlot` before the store. |
| A10 | Authoring §7 | The primitive table omitted checked binds and generic reads/writes. Adds them and states the accepted index kinds. |
| A11 | Authoring §4.1 | The glossary omitted checked types and fault constructors. Adds them. |
| A12 | Linting | Enforcement wording implied an active checker. States that no arithmetic linter enforces these rules; the proposal remains deferred. |
| A13 | Coding style §1 | `processAttestation` had an old signature, unbound arithmetic, and stale paragraph counts. Uses the current Gloas form and five headers. |
| A14 | Coding style §1 | The tree-filter example used a removed function and unbound horizon. Uses `filterNodeTree.go` with the short-circuit bind. |
| A15 | Coding style §2 | `getHead.better` assumed pure weight queries. Uses monadic `betterOf`. |
| A16 | Coding style §4 | The clock example used raw arithmetic and `.toNat`. Uses current `onTick`, checked binds, and structural `toPlainNat` fuel. |
| A17 | Coding style §4 | The withdrawal cursor wrapped and defaulted on zero divisors. Uses the checked modulo and its empty-registry fault. |
| A18 | Coding style §4 | The deposit-scan counterexample omitted a bind and used historical prose. Shows a hypothetical port with Python's addition order. |
| A19 | Coding style §§5, 7 | Examples named removed helpers and narrowed raw intermediates. Uses current committee validation, `getCurrentSlot`, and `computeActivationExitEpoch`. |
| A20 | Coding style backlog | Completed items remained candidates. Retains the request-ladder item only. |
| A21 | Arithmetic §4.2 review | `CLInt` division/modulo with `Nat` was still absent. Adds `Nat` and Lean `Int` in either order, returning `Checked CLInt`. |
| A22 | Coding style §1 review | `getExpectedWithdrawals` remained a paragraphing candidate despite existing phase breaks. Removes it. |
| A23 | Coding style §1 review | An abbreviated snippet omitted text without marking the cut. Adds the omission marker. |

| ID | Document or site | Conflict and recorded resolution |
|---|---|---|
| B01 | Notes, indexing | Queries were described as total reads without a reject channel. Names the raising builder/weight reads and `computeCommittee`'s checked bounds and assertion. |
| B02 | Framework §10 | Raw arithmetic, narrowing, and correspondence guidance was obsolete. Describes checked modules, conversions, binds, codec boundaries, and laws. |
| B03 | Framework §6 | Buckets and arithmetic causes were incomplete. Adds `ArithCause`, the lift, `outOfScope`, and current constructor descriptions. |
| B04 | Framework §§4, 8.1 | A slot store omitted its bind; the maximum literal used a checked arithmetic expression. Binds the add and uses the bounded hexadecimal literal. |
| B05 | Framework §§13–15 | Bucket names and test/proof references were stale. Uses current buckets, checked tests, and law modules. |
| B06 | Specs architecture | Alias, timestamp, constant-kind, caught-error, and proof guidance used raw types. Matches checked units and current error handling. |
| B07 | Notes, fork choice | Weight sums were described as wrapping. States the checked `Gwei` fold and raising queries. |
| B08 | Notes, validator exit | Overflow rejection was described as an explicit assert. Names the checked epoch add and `valueError` wrapper. |
| B09 | Notes, error model/module map | Buckets were incomplete and flag helpers were attributed to `Arith`. Names all buckets and the `Checked` flag helpers in `CLUint`. |
| B10 | Notes, proofs | Theorem names, result types, and PTC fault counts were stale. Names current equations, four fallible PTC stages, and lift laws. X12 below completes the success/error descriptions. |
| B11 | Discrepancies | The closed large-withdrawable-epoch entry named an assert. Names the checked add. No open arithmetic discrepancy remains there. |
| B12 | Future work | The residual indexing sketch treated raising queries as total and used an unchecked fold. Restricts the residual and uses `Checked`, `foldlM`, and `toPlainNat`. |
| B13 | Plan | Raw `UInt64` and `Nat` lifting appeared as current design. Labels those passages **Superseded** and points to the contract. |
| B14 | Proof ledger | Conversion names, folds, PTC fault counts, and migration history were stale. Uses current names and four fallible stages; removes historical clauses. |
| B15 | Docs README | The future-work entry described the wrong residual. Updates its description; structural links stay assigned to 9.4. |

| ID | Document or site | Conflict and recorded resolution |
|---|---|---|
| C01 | `CONTRIBUTING.md` | Both builder-exit examples need the current conversion and rejecting out-of-range contract. Both use `.toPlainNat` and `.error (.outOfBounds …)`; only boxed/plain state differs. |
| C02 | SizzLean architecture §7 | Consensus units were raw wrappers and their instances were attributed to SizzLean. Names `CLUint64` and EthCLLib's instance; keeps `Vector UInt8` byte instances in SizzLean. |
| C03 | `SECURITY.md` | The C-shim path did not exist. Names the hazmat and LeanPoseidon `csrc/` paths. This is an incidental accuracy correction. |

| ID | Module or site | Conflict and recorded resolution |
|---|---|---|
| D1-01 | `Spec/Arith` introduction | Raw `UInt64` and unbounded `Nat` were presented as spec arithmetic. Labels structural, codec, and proved-total helpers; names checked modules. |
| D1-02 | `Spec/Arith` indexing | Default reads were offered as generic spec reads. Restricts total reads to known bounds and names raising reads. |
| D1-03 | Raw `umax`, `umin`, `saturatingSub` | Helpers lacked a raw-word label. Labels them and points to checked forms. |
| D1-04 | `isqrt`, `isqrtAux` | The raw helper was equated with the spec-facing function. Names the iteration and `CLUint64.integerSquareroot`. |
| D1-05 | Modulo lemma, `vmodGet` | The raw modulo route had stale callers. Labels the proved-total route through `ValidModulus` and names current callers. |
| D1-06 | `Errors` helper section | Raw helper advice and caller claims were false. Fork bodies use checked operators; only tests call `checkedAdd/Sub/Mul`. `checkedSucc` models the spec counter and supplies a termination bound. |
| D1-07 | Arithmetic throw helpers | The named caller was stale. Describes the checked lift and the Heze `CLInt` modulo route. |
| D1-08 | Arithmetic error constructors | Prose omitted the lift. Names `ofArithFault` and keeps source examples as examples. |
| D1-09 | `Errors`, Python context | Four spans pointed to configuration code. Uses `context.py:451-462`. |
| D1-10 | Store expected rejection | The wrapper span was stale. Uses `fork_choice.py:383-387`, the `add_block` except clause. |
| D1-11 | `ArithCause`, `arithCause` | A temporary-stage narrative described the core. Names the module and lift theorem. |
| D1-12 | `Checked` introduction | Temporary stages appeared as owners. Names the current operator modules. |
| D1-13 | `Elab` hazards | Spike history and a combined bind could teach an invalid authoring form. Describes the hazard and requires split conversion binds. |
| D1-14 | `Elab` cost note | An early measurement implied future fork use. Labels it **Historical** and removes the forward claim. |
| D1-15 | `toPlainNat` | The docstring equated it with Python `int(x)`. States Lean `Nat`; `toCLInt` models Python `int`. |
| D1-16 | `ofNatLT` | Caller restrictions omitted guarded fork-body uses. Requires the caller's guard or preset proof. |
| D1-17 | Width paragraph | Closed stages appeared as future work. States 32-bit codec-only and 256-bit data-only use. |
| D1-18 | 8-bit/SSZ sections | Migration history described current fields. Uses current-state descriptions. |
| D1-19 | `CLTotal` divisor | A temporary stage tag was redundant. Removes it. |
| D1-20 | `sszGetIdx` | A preceding assert was called `IndexError`. Names `AssertionError`. |
| D1-21 | `isValidMerkleBranch` | The removed deposit caller was still named. Names pinned light-client/sidecar callers outside the modeled bodies and current framework tests/proofs. Closes the 9.5c route. |
| D1-22 | Proof root | `saturatingSub` was ambiguous. Names the raw-word theorem and checked law module. |

| ID | Module or site | Conflict and recorded resolution |
|---|---|---|
| D2-01 | `Proofs/MerkleBranch`, `branchFold` | Public visibility had a false outside-module justification. Names public theorem statements that expose the fold. |
| D2-02 | Reconstruction theorem | The docstring still claimed fork-ledger consumers. Describes its reconstruction contract. |
| D2-03 | Honest-opening theorem | The removed deposit-ledger dependency and replacement row name were wrong. Names SizzLean's `branch × opening` row. Closes the 9.5c route. |
| D2-04 | `PySpecTests/Driver` | Fork choice and rewards were described as future work. Names current interface dispatch. |
| D2-05 | `Tests/CLCheckedElab` introduction | The tested hazard description was unclear. Names the two elaboration hazards. |
| D2-06 | `reserveChurn` test | A self-referential shape label obscured the check. Names the conversion, checked add, and non-literal `Nat`. |
| D2-07 | Runner interface/error tests | Python helper spans were stale. Uses context `451-462`, helper `240-245`, `460-463`, `429-433`, `486-493`, block except `383-387`, tick `306-310`, and replay `394-400`. |
| D2-08 | Authoring/law/replay/fold comments | Temporary stages appeared as future consumers. Describes current tests and proof uses. |
| D2-09 | Elaboration tests | Temporary stages and external spike findings obscured expression shapes. Names the tested operators directly. |
| D2-10 | Literal tests | The docstring denied a checked power route. Distinguishes bare result types from `Checked CLUint64` power. |

| ID | Module or site | Conflict and recorded resolution |
|---|---|---|
| D3-01 | Fulu constants introduction | Unbounded reward intermediates and narrowing were taught as current. Names checked constants, structural sizes, and mixed `Gwei op Nat`. |
| D3-02 | Derived constant views | The description claimed a raw config consumer. States proof-carrying `ofNatLT`. |
| D3-03 | Period views | Contrastive wrapping prose obscured preset rejection. States the pinned module's raising behavior. |
| D3-04 | Slot-to-epoch views | Temporary-stage references described consumers. Names slot-to-epoch formulas. |
| D3-05 | Effective balance increment | `Gwei` was equated with `UInt64`; the `Nat` view had a false caller list. Names `CLUint64`, body `…G` uses, and test-only `Nat` uses. |
| D3-06 | Reward weights | Checked weights were labelled `Nat`. Separates the structural factor from checked weights. |
| D3-07 | Rewards introduction | A closed epoch retype was still promised. Describes checked epoch subtraction. |
| D3-08 | `getBaseReward` | Jargon obscured the reject route. Names the `ArithFault` lift. |
| D3-09 | `balanceAfterWithdrawals` | Repeated prose and a stale context span obscured faults. Removes repetition and uses `451-462`; X07 supplies the exact exception class. |
| D3-10 | Fulu config setters | The bound check before the raw conversion was omitted. States `applyConfigOverrides`' range check before `UInt64.ofNat`. |
| D3-11 | Operations introduction | Input reads were described as assertion-guarded. Names raising reads, `.outOfBounds`, and `assertionAndIndex`. |
| D3-12 | Attestation comment | Punctuation conflicted with the writing rules. Splits the sentence and uses commas. |
| D3-13 | Pubkey lookup | The removed deposit caller and raw index type remained. Names current callers and checked index casts. |
| D3-14 | Tree filter | The epoch comparison was labelled `UInt64` with historical wording. Names `Epoch`. |
| D3-15 | `onTick` | Contrastive wording obscured fuel exhaustion. States the thrown reject on an exhausted bound. |
| D3-16 | Inactivity field | A completed rename was still justified. Describes the current `CLUint64` element. |
| D3-17 | Epoch-processing introduction | Completed substeps appeared as future work. Lists current substeps and the transition spine. |
| D3-18 | EthCLSpecs root | Gloas appeared as a future fork. Names all three current forks and their lineage. |
| D3-19 | Python spans | Rewards, registry, accessors, time, committees, epoch processing, operations, and registry-update spans were stale. Checks them against 1.7.0b4. Seven moved Lean citations in the proof ledger receive span-only updates. |

| ID | Module or site | Conflict and recorded resolution |
|---|---|---|
| D4-01 | PTC initialization | The library, helper name, fault count, offset bound, and pin history were stale. Names `SSZValueError`, checked operators, general offset bounds, and current fallible stages. |
| D4-02 | Attestation inclusion slot | Hypothetical wrapping prose obscured the real fault. Names checked `Slot` addition and `uncaughtFault`. |
| D4-03 | Payload attestation | Wrapping prose obscured the checked add. Names `.arithmetic` at the maximum slot and its classification. |
| D4-04 | Fork-choice attestation | The comment justified a hypothetical wrap. Names `SSZValueError` and `.transition (.arithmetic …)`. |
| D4-05 | Envelope slot number | A data-only field was promised a retype. Labels the raw field as comparison-only data. |
| D4-06 | Gloas `onTick` | Fuel/history prose was stale. States the `todo` reject on fuel exhaustion. Closes the deferred phrasing item. |
| D4-07 | `getPtc` | The comment assumed `MIN_SEED_LOOKAHEAD = 1`. Uses `(MIN_SEED_LOOKAHEAD + 2) * SLOTS_PER_EPOCH`. |
| D4-08 | Progressive lists | Pin history and issue labels obscured current behavior. Describes the pin and capped-constructor `.listFull` fault. |
| D4-09 | Gloas/Heze withdrawals | Context spans and exception names were stale. Uses `451-462` and checked subtraction's `SSZValueError`. |
| D4-10 | Operation interfaces | Comments depended on the temporary plan. Names the `maxHeartbeats` annotation directly. |
| D4-11 | Fork-choice interfaces | Block/replay/vote-check helper spans were stale. Uses `323-426`, return `387`, replay `394-400`, and vote checks `511-513`. |
| D4-12 | Python function spans | Churn, quorum, cover-bid, and withdrawal spans included blank lines or missed code. Uses `7876-7886`, `6678-6685`, `7867-7873`, `7767-7775`, and `8003-8031`. |
| D4-13 | Gloas constants | Temporary audit labels and jargon obscured current facts. Uses current-state descriptions. |
| D4-14 | Builder-deposit domain | An implemented signature check was described as deferred. Names `isValidBuilderDepositSignature`. |
| D4-15 | Epoch-processing introduction | Restated and implemented substeps were called inherited or `todo`. Lists current overrides and new substeps. |
| D4-16 | Churn/slashing comment | `slashValidator` was called inherited. States that Gloas restates it. |
| D4-17 | Payment index | A removed caller remained listed. Names parent-payload, attestation, and payload-bid callers. |
| D4-18 | Builder-deposit/flag comments | Pin history and punctuation conflicted with the writing rules. Uses current-state wording and commas. |

| ID | Module or site | Conflict and recorded resolution |
|---|---|---|
| D5-01 | Fulu balance proofs | A removed `processDeposit` caller remained. Names `applyPendingDeposit`. Closes the 9.5c route. |
| D5-02 | Fulu balance proof introduction | The library, overflow class, and contract section were wrong. Names `eth-ssz-specs` 0.1.0, `SSZValueError`, and §4.2. |
| D5-03 | Fulu balance theorems | Pin history and a nonexistent theorem name remained. Uses the pinned source and `decreaseBalance_written_toNat`. |
| D5-04 | `GetPtc` proofs | A checked offset was described as raw. States the checked chain and the equality obtained from a passing caller. |
| D5-05 | Cover-bid proof | Prose moved the subtraction before its guard. Matches the theorem's else-branch bind. |
| D5-06 | PTC-window proof | Two/three-fault descriptions omitted fallible stages. Names three checked steps and `computePtc` rejects. |
| D5-07 | Builder-exit proof | Migration history, a raw slot type, and delay 8192 were wrong. Names checked addition and the shipped delay 64. |
| D5-08 | Uncached proof | A referenced lemma did not exist. Names current/previous attestation-loop lemmas. |
| D5-09 | Proof indices | Theorem names, predicates, result types, and the fork-choice index were stale. Uses current names and checked contracts; adds `ForkChoiceRun`. |
| D5-10 | Epoch pins | All failures were described as lifted `.arithmetic`. Distinguishes direct `.range` causes from lifted faults. |
| D5-11 | Fulu fork-choice pins | The context span and exception class were stale. Uses `451-462` and `SSZValueError`. |
| D5-12 | Heze fork-choice pins | An empty-committee guard was invented. Names `CLInt` modulo by zero and its uncaught `.zeroDivision`. |
| D5-13 | Arithmetic pins | Old forms appeared as past behavior. States checked counterfactuals and verifies each against the pin. |
| D5-14 | Pin Python spans | Epoch, cast, and lookup spans were short or long. Uses `1871-1891`, `1252-1275`, and `4515-4518`. |
| D5-15 | Walking skeleton | A tested `outOfScope` entry was called `todo`. Names the actual entry and skip bucket. |
| D5-16 | Constant-view tests | Proof fields were implicit and the sentence combined claims. Names all four fields and splits the sentence. Closes the deferred item. |
| D5-17 | Pin/proof headers | Temporary stages, untracked script paths, and historical labels obscured current claims. Removes them while keeping oracle claims. |
| D5-18 | Server protocol | Eight fields and unwired fork choice were claimed. Documents nine required fields, optional `cfg=`, and current dispatch. |
| D5-19 | Bench example | The documented interface call omitted `forkVersion`. Adds `gloasForkVersionMainnet` in the comment example. |
| D5-20 | Proof/pin style | Banned words and history obscured claims. Uses direct current descriptions and counterfactual pin forms. |
| D5-21 | Fork-choice payment bridge | The prose promised unconditional writes. States the successful quorum premise and absence of a capacity premise. |
| D5-22 | Payment proof | Module, section, theorem, and index prose described success only. States propagated quorum errors and both writes after quorum success. |
| D5-23 | Builder-exit premises | Several descriptions omitted an in-range index or confused sum-bound requirements. Names both success premises, the bound-free out-of-range reject, and shipped corollaries that discharge only the sum bound. |
| D5-24 | Operations proof | The success reading omitted six length bounds. Names those bounds in the introduction, summary, and theorem docstring. |
| D5-25 | Gloas payment index | The proof index described the success postcondition alone. Names the run equation and propagated quorum error. |
| D5-26 | Payment readings | “Unconditional” could imply success. Uses “reading with no side hypothesis” for the premise-free equivalences. |

### Cross-family resolutions

These rows reconcile the routed findings on the integrated source tree. A repeated
route has one disposition. The consolidation changes documentation and comments only.

| ID | Shared finding | Resolution at 9.2 |
|---|---|---|
| X01 | Raw arithmetic guidance repeated in the contract, framework architecture, and `Spec/Arith` | A08, B02, and D1-01 agree on checked operators. The raw helpers retain their explicit framework labels. |
| X02 | Missing binds repeated in authoring, framework, and coding-style examples | A09, A13–A19, and B04 resolve the duplicates. Current examples bind fallible arithmetic immediately and preserve branch order. |
| X03 | Conversion names and raw config construction | Checks the actual signatures in the table below. Clarifies `trustedOfUInt64`'s docstring and both Gloas/Heze config comments: the runner validates before `UInt64.ofNat`. Fulu already states that check. |
| X04 | Width rule required arithmetic matrices for data-only widths | Clarifies contract §4.1: 64/8-bit arithmetic has matrices; 32-bit codec and 256-bit data uses keep codec rules. Any future arithmetic use requires a checked surface first. |
| X05 | Framework proof/test prose still taught raw helpers as fork operators | Labels `Proofs/Arith` as raw-word laws and points to `Proofs.CLUint`. Labels `Tests/FrameworkUtils`' raw helpers. Corrects Fulu `isFinalizationOk` to name checked `Epoch` subtraction. |
| X06 | Modulo-bound comments named the implementation lemma as direct consumer | Fulu constants now name `ValidModulus` and `vmodGet`. The raw lemma remains a proved internal implementation. |
| X07 | Pinned exception library and repeated context/block spans | Uses `eth-ssz-specs` and `SSZValueError` in Fulu balance/withdrawal comments. Fixes the notes' context/block spans and the four Fulu interface block/replay anchors. The `add_block` span is `323-426` (ends on the `return` line, not the following blank line) and its `except` clause is `383-387`, now used consistently in `Spec/Errors`, this record, and `PySpecTests/Interface`. D4/D5 already resolve their copies. |
| X08 | Sync-aggregate lookup span ended one line early | Extends both `Spec/Errors` and Fulu transition comments to `4515-4518`, matching D5-14. |
| X09 | PTC-window fault counts disagreed between documents and proofs | B10/B14, D4-01, and D5-06 name the same sequence: epoch add, start-slot product, slot add, and `computePtc`. |
| X10 | Removed `processDeposit` survived in SizzLean records | Reconciles SizzLean's plan and ledger dependency, opening, deposit-tree, and related-work passages. Removes the invalid operations citation. Keeps incremental-tree work explicitly out of modeled-fork scope; the framework branch bridge remains proved. D1-21, D2-03, and D5-01 close the Lean copies. |
| X11 | Deferred Fulu/Gloas comments and restatements | D3/D4 resolve constants, Python spans, and fuel phrasing; D5 resolves constant-view proof fields. Restated comments agree on checked arithmetic. Different sampler faults retain their documented source-specific behavior. |
| X12 | Success-only or unconditional claims repeated in the ledger and notes | Qualifies the ledger's builder-exit row with both premises. Rewrites the notes' builder-exit entry to include index and arithmetic rejects. Qualifies the notes' payment writes with quorum success and states error propagation. Matches D5-21–D5-25. |
| X13 | Framework style items explicitly routed by WS-100 | Replaces “standing case”, “escape hatch”, and “ride” wording at the eight named sites in `Errors`, `State`, `Assert`, `Forms`, `FiniteMap`, `Hasher`, `NestedMachine`, and `Internal/Capture`. |
| X14 | Notes called removed Heze corollaries a current history record | Removes the alpha.12 collector sentence. The entry describes the current equations and membership theorems. |
| X15 | Proposed removal of unused raw helpers and duplicate `len` functions | Retains the APIs with explicit raw/structural labels. Removal and deduplication are optional code work, outside this documentation task. Both `CLInt.len` and generic `Spec.len` return `CLInt`. |
| X16 | Builder/validator cast comments and a suggested size-bound lemma | Retains the comments verified in 9.1d4 against the size bounds. The proposed reusable lemma is optional code work; no documentation conflict requires it. |
| X17 | A trusted maximum-value fixture could use a checked literal | Retains the in-range fixture. The existing trusted construction is accurate test setup; literal replacement is optional code work. |
| X18 | The ledger's builder-exit row and the proof module's "no-wrap" header | The `processBuilderExitRequest` row now states the exact result: the selected builder receives `withdrawableEpoch` equal to the `Nat` sum of the current epoch and the delay, under the shipped sum bound. The `InitiateBuilderExit` section header and the `Gloas.lean` proof index now name the sum bound instead of no-wrap; the checked add raises past the bound, so it cannot wrap. Routed by the 9.1b review (`01a1fc22-8303-73f4-84ed-6c6cfb29d066`). |
| X19 | `PLAN.md` used `todo` for two meanings | The classify-bucket bullet now calls `todo` the work-queue bucket, matching `FRAMEWORK_ARCHITECTURE.md` §6 and the separate `outOfScope` skip bucket. The fork-choice note in this record likewise reports `.todo` as a work-queue `xfail` and `.outOfScope` as a `skip`. Routed by the 9.1b review (`01a1fc22-8303-73f4-84ed-6c6cfb29d066`). |
| X20 | The §10 `Spec/Arith.lean` row omitted the raw-word helpers and the modulo-bound route | The row now lists `umax` / `umin` / `saturatingSub` and `ValidModulus` / `vmodGet`, matching this record and D1-03/D1-05. This is the cross-family description mismatch the reviewer routed. |

### Conversion result types

The declaration determines whether a name returns a checked value or a plain
integer. These signatures reconcile the document and docstring uses.

| Declaration | Actual result | Documented use |
|---|---|---|
| `CLUint64.toPlainNat`, `CLUint8.toPlainNat` | Lean `Nat` | Proofs and justified structural/framework boundaries |
| `CLInt.toPlainInt` | Lean `Int` | Proofs and justified framework boundaries |
| `CLUint64.toCLInt`, `CLUint8.toCLInt` | `CLInt` | Python `int(x)` |
| `CLInt.toCLUint64?` | `Checked CLUint64` | Checked unsigned cast from a signed spec integer |
| `CLUint64.ofNat?`, `ofInt?`, `ofCLInt?` | `Checked CLUint64` | Range-checked construction |
| `CLUint8.ofNat?` | `Checked CLUint8` | Range-checked 8-bit construction |
| `CLUint64.ofNatLT` | `CLUint64` | Caller supplies the range proof |
| `CLUint64.trustedOfUInt64`, `CLUint8.trustedOfUInt8` | Respective checked-width value, with no `Checked` result | Exact raw-word bridge after validation, codec conversion, or proved-total internal operation |
| `CLInt.len`, generic `Spec.len` | `CLInt` | Spec-facing collection length |
| `getAt` | `Except IndexError α` | Pure raising collection read |
| `setAt` | `Except IndexError ρ` | Pure raising collection write |
| `sszGetIdx` | Ambient `m α`, with `MonadExcept E m` and `ErrorConv IndexError E` | Raising read lifted into the caller's error channel |

`getAt` remains a live API. The spike's use of that spelling does not make the
current typed-index operation obsolete. The server's string `toNat?` parses input;
it is distinct from a spec-integer conversion.

### Retained raw, historical, and superseded descriptions

| Corpus | Inspected disposition |
|---|---|
| SizzLean manual, architecture, optimisation records, plan, and ledger | Raw codec words, structural indices, cache calculations, and the manual's raw epoch-update example belong to SizzLean. Its checked-consensus-unit paragraph uses EthCLLib's contract. |
| hazmat, LeanRlp, LeanPoseidon, LeanPoseidonProofs, LeanSha256 | FFI arguments, codec bounds, field arithmetic, and hash operations retain their packages' intentional raw arithmetic. The Lean search pass found no false checked-surface reference. |
| SizzLean release counts, benchmark records, and research documents | Existing release, measurement, and research labels identify their historical scope. The audit preserves those measurements. |
| `Spec/Elab` cost note | Explicitly labelled **Historical**, measured before fork-body use. It provides no current performance baseline. |
| EthCLSpecs `PLAN.md` arithmetic design | Explicitly labelled **Superseded**. Current guidance points to the checked contract and framework architecture. |
| `SPEC_ARITHMETIC_LINTING.md` | Spike results remain evidence; linter implementation and activation remain future work. |
| Framework internals and proofs | Raw modulo behind `ValidModulus`, codec conversions, native projections, carry tests, and bounded literals have stated proofs or boundary roles. |
| Fulu/Gloas/Heze data | Raw byte buffers, payload/version sentinels, data-only indices, gas schedules, and comparison-only payload fields retain their labels. Structural counters and fuel remain structural. |
| Pins and bench fixtures | Old wrapping/defaulting forms are labelled counterexamples. Trusted constructors build in-range fixtures. The pins describe the fault that current code raises. |
| Contract forbidden-form tables and coding-style “before” snippets | These are labelled rejected forms or teaching counterexamples. Current “after” snippets use checked binds. Both contributor theorem examples use the current arithmetic and error contract. |

The architecture/records family found no Stage 0/4/5/7/8 cost table to relabel.
Those working measurements remain assigned to Stage 10's rollup.

### Explicit routes outside arithmetic reconciliation

No arithmetic guidance conflict remains open in the collected family findings.
Three non-arithmetic groups remain assigned outside 9.2. They are recorded here so
the Epic Lead can sequence them without losing the original findings.

1. **R1, index and status work, 9.4 (WS-103).** `PLAN.md` still labels all phases
   pending. Root README and `CLAUDE.md` reading lists omit the arithmetic contract.
   `CLAUDE.md` omits LeanRlp from its package list. `docs/monorepo-arch.md` understates
   the document set. SizzLean's plan/README carry old C-shim paths, its architecture
   omits Heze from the container list, and SizzLean/hazmat carry old fork ranges.
   The Gloas proof index reaches `KeepsUncached` transitively. Generated coverage
   blocks stay owned by `proof-coverage-update`. These are the reported link/status
   observations; 9.4 must check their current disposition before editing.
2. **R2, non-arithmetic prose, Epic Lead.** The family hand-offs explicitly left
   historical wording outside arithmetic scope. Reported Fulu sites are the
   alpha.12 and `aed053b` notes in `ForkChoice`, old whole-field prose in `Balances`,
   the dataclass note in `Blocks`, movement prose in the `Tests` root, and wording
   in `Forms`. Gloas sites are version comparisons in `slashValidator`, fork-choice
   helpers, operations, withdrawals, and interfaces, including the old “Phase 4”
   label. Heze sites are version comparisons in constants, inclusion-list
   containers, fork choice, and signing. Root coding style §6 retains deposit-scan
   history. The "ride" wording that X13 fixed at the eight WS-100 sites remains
   outside them in `EthCLLib/Tests/CLAuthoring.lean:250`, `EthCLLib/Tests/TierMerge.lean:12`,
   `EthCLLib/Tests/ForkScoping.lean:25`, `EthCLLib/Proofs/KeepsUncached.lean:612`,
   `EthCLSpecs/Forms.lean:28`, `EthCLSpecs/Fulu/Transition.lean:122`,
   `EthCLSpecs/Gloas/Upgrade.lean:86`, `EthCLSpecs/Heze/Upgrade.lean:93`,
   `EthCLSpecs/Heze/Fork.lean:12`, `EthCLSpecs/Gloas/ForkChoice.lean:872`, and
   `EthCLSpecs/Heze/ForkChoice.lean:392`. These passages
   need a separate current-state style pass. Their exact sites are recorded in the
   source hand-offs for 9.1a, 9.1d1, 9.1d2, 9.1d3, and 9.1d4.
3. **R3, tracker IDs in the committed record, Epic Lead.** The source table above
   holds Multica comment UUIDs, and the command list below opens with
   `git merge epic/WS-92`. A reader on GitHub cannot resolve the branch name or the
   UUIDs. `WS-` issue IDs already appear in the package documents, so those are
   existing practice; the comment UUIDs are new to the repository. Keeping the
   hand-off IDs as the audit's source of truth and replacing them with stable
   in-tree labels are both defensible. This policy choice is for the Epic Lead.

### Commands and evidence

Each family re-ran `just lint`, `just check-citations`, and `just check-constants`.
The Lean families also report the affected library and runner builds and an
unchanged proof baseline. The 9.1d4 coder reported its builds pending; its review
thread records successful `ethcl-test` and `build-cli` completion. Task 9.3 verifies
the full integrated tree, including coverage; see "Integrated verification sweep
(9.3)" below.

The source hand-offs record targeted searches for raw `UInt64`/`UInt8` guidance,
`UInt64.ofNat`, `.val`, trusted constructors, unbounded intermediates, wrapping,
error classes, conversion names, temporary retypes, and unbound arithmetic examples.
They separate comment matches from executable internals. Remaining matches have
the dispositions above. The consolidation checks the routed sites and shared
guidance; it does not repeat the family audits.

Commands for the consolidation, from the repository root:

```bash
git merge epic/WS-92
git grep -n -E 'toPlainNat|toPlainInt|toCLInt|toCLUint64\?|ofNat\?|ofInt\?|ofCLInt\?' -- packages/EthCLLib/EthCLLib/Spec
git grep -n -E '424-435|382-406|400-406|4515-4517|remerkleable|checkedSub' -- packages/EthCLSpecs/EthCLSpecs/Fulu packages/EthCLLib/EthCLLib/Spec/Errors.lean
git grep -n -E 'processDeposit|unconditional|missing-timeliness' -- packages/SizzLean/docs/PLAN.md packages/SizzLean/docs/PROOF_LEDGER.md packages/EthCLSpecs/docs/PROOF_LEDGER.md packages/EthCLSpecs/docs/IMPLEMENTATION_NOTES.md
git grep -n 'TEMPORARY CROSSING' -- '*.lean'
just ethcl-test
just build-cli
just lint
just check-citations
just check-constants
just proof-coverage-check
git diff --check
```

The expected empty `TEMPORARY CROSSING` search exits 1. Descriptions of removed
deposit entry points in SizzLean now explain scope. Remaining raw helper names
describe labelled framework internals or the audit findings themselves.

Family evidence uses 677 test jobs, 628 runner jobs, 194 citations in nine files,
166 constants, and 87 proof claims. The constants retain two untabled and three
tier-only advisories. Relative to Stage 8.5, the three 9.5a–9.5c pin modules add
three jobs; 9.5c removes two ledger citations; 9.5d removes
`maxEffectiveBalanceElectra`. The runner and proof counts stay unchanged.
The documentation consolidation adds no vector evidence; task 9.3 owns the smoke
confirmation and Stage 10 owns the final full matrix.

Consolidation results on the source tree plus the 9.2 edits:

| Command or comparison | Result |
|---|---|
| `just ethcl-test` | Passed, 677 jobs |
| `just build-cli` | Passed, 628 jobs |
| `just lint` | Passed |
| `just check-citations` | Passed, 194 citations in nine files |
| `just check-constants` | Passed, 166 constants; two untabled and three tier-only advisories |
| `just proof-coverage-check` | Passed, 87 claims |
| Targeted searches above | Inspected; stale source/library spans are absent from the routed Fulu sites. Raw helper matches are labelled internals. Scope descriptions and audit rows explain the remaining deposit/history matches. |
| `TEMPORARY CROSSING` search over Lean files | Empty |
| Lexical comparison against `40d5e58` | All 19 changed Lean files have identical non-comment text and line counts. No cited Lean span moves. |
| Baselines and generated README blocks | Byte-identical to the source tree |
| `git diff --check` | Passed |

The build reused copied local Lake caches and gitignored native vendor trees.
Lake rebuilt modules whose source hashes changed. No formula, signature, theorem
statement, or characterization tag changes in this consolidation.

### Integrated verification sweep (9.3)

Task 9.3 (WS-102) re-runs the build and project gates on the integrated
`epic/WS-92` tree at `5ff4e967`. The sweep
checks the documentation edits of 9.1a through 9.2 and the code edits of 9.5a
through 9.5d together. It re-runs the targeted searches and inspects every
remaining match. No new conflict surfaced, so no reconciliation edit is needed;
every remaining match falls under a disposition in the sections above.

| Command | Result |
|---|---|
| `just ethcl-test` | Passed, 677 jobs |
| `lake build EthCLSpecsBench` | Passed, 672 jobs |
| `just build-cli` | Passed, 628 jobs |
| `just lint` | Passed |
| `just check-citations` | Passed, 194 citations in nine files |
| `just check-constants` | Passed, 166 constants against 244 upstream names; two untabled and three tier-only advisories |
| `just proof-coverage-update` | Empty diff |
| `just proof-coverage-check` | Passed, 87 claims |
| `just ethcl-pyspec-smoke` | Passed; Fulu 155 passed / 46 skipped, Gloas 207 / 52, Heze 209 / 52 |
| `git grep 'TEMPORARY CROSSING' -- '*.lean'` | Empty (exit 1) |
| `git diff --check` on the 9.3 edits | Clean |

Differences from the Stage 8.5 reference, each with its cause:

- `ethcl-test` 674 to 677 jobs: the three pin modules of 9.5a, 9.5b, and 9.5c.
- `check-citations` 196 to 194 citations: 9.5c removes the two removed-`processDeposit` ledger citations.
- `check-constants` 167 to 166 constants: 9.5d removes `maxEffectiveBalanceElectra`.
- `build-cli` 628 jobs, `proof-coverage` 87 claims, and the smoke counts are unchanged.

Targeted searches re-run over the integrated tree:

| Search | Matches | Disposition |
|---|---:|---|
| Raw `UInt64` / `UInt8` in documents | 92 | Data-only byte vectors, contract comparison tables, audit rows, the temporary plan, and other-package raw code. No current spec-arithmetic guidance. |
| Unbounded / wrapping wording in documents | 74 | Contract rejected-form tables, labelled historical and superseded passages, and this audit record. |
| `UInt64.ofNat` and `.val` in Lean | 769 | Codec conversion after a range check, structural projections, and labelled framework internals. |
| Trusted constructors (`trustedOfUInt64`, `trustedOfUInt8`, `ofNatLT`) in Lean | 184 | Bridge after validation or a preset proof; the docstrings state the caller obligation. |
| Obsolete conversion names (`getAt`, `toNat?`) in Lean | 126 | `getAt` is the live typed-index read and `toNat?` is the server input parse, both matching the conversion table above. |
| `spike` in Lean and documents | 52 | Module names, the deferred linter document, and labelled historical or superseded passages. |
| Error-class wording (`IndexError`, `AssertionError`, `SSZValueError`, `outOfBounds`) in documents | 78 | Current contract descriptions and audit rows. |
| Arithmetic examples that omit binds in documents | 12 | The labelled rejected form at `SPEC_ARITHMETIC.md:308`, the bound-dividend total route at `SPEC_ARITHMETIC.md:264`, list concatenation, and intentionally raw LeanPoseidon and SizzLean examples. No current guidance teaches an unbound checked computation. |

The search commands, run from the repository root on `5ff4e967`:

```bash
git grep -n -E 'UInt64|UInt8' -- '*.md'
git grep -n -i -E 'unbounded|wrapping|overflow' -- '*.md'
git grep -n -E 'UInt64\.ofNat|\.val\b' -- '*.lean'
git grep -n -E 'trustedOfUInt64|trustedOfUInt8|ofNatLT' -- '*.lean'
git grep -n -E '\bgetAt\b|\btoNat\?' -- '*.lean'
git grep -n -i -E 'spike' -- '*.lean' '*.md'
git grep -n -E 'IndexError|AssertionError|SSZValueError|outOfBounds' -- '*.md'
git grep -n -E 'let [A-Za-z_][A-Za-z0-9_]* := .*[+*/]|let [A-Za-z_][A-Za-z0-9_]* := .* - ' -- '*.md'
```

The counts are matching lines.

The routed spans resolve at their documented sites: `context.py:451-462`,
`fork_choice.py:383-387`, `fulu/minimal.py:4515-4518`, and the `add_block` span
`323-426`. The verification cross-references this record and adds no finding of
its own. The builds reused copied local Lake caches and the gitignored native
vendor trees.
