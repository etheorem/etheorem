# EthCLSpecs: Implementation Notes

The as-built companion to the four design documents in this directory
(`SPEC_AUTHORING_MODEL.md`, `SPECS_ARCHITECTURE.md`, `FRAMEWORK_ARCHITECTURE.md`, and
the glossary). Those four are the design of record. This file records how
`EthCLSpecs` / `EthCLLib` realize them: the current architecture, the places the code
deviates from a doc (with the reason), and the spec-faithfulness decisions worth
knowing. Everything here describes the tree as it stands against the
`v1.7.0-alpha.11` pin.

## Scope and conformance

Three forks, **Fulu**, **Gloas**, and **Heze**, against the `consensus-spec-tests` minimal and
mainnet archives at `v1.7.0-alpha.11` (the latest release with cut vectors; it is
flagged pre-release, so the harness pins the tag explicitly rather than reading `gh
release latest`). The full in-scope suite is green at both presets for all three
forks, `--subset=0`, zero failures and zero `xfail`:

| | minimal | mainnet |
|---|---|---|
| Fulu  | **5188 passed** | **847 passed** |
| Gloas | **6573 passed** | **1034 passed** |
| Heze  | **6770 passed** | **997 passed** |

Fulu's collected formats: `epoch_processing`, `operations` (including the standalone
`execution_payload`), `rewards`, `sanity/blocks`, `sanity/slots`, `finality`,
`random`, `fork_choice` (including the PeerDAS data-availability `on_block` cases and
`get_proposer_head`). Gloas adds `fork`, `transition`, and the full ePBS
`fork_choice`. `DISCREPANCIES.md` records no open vector discrepancy: every vector the
implemented formats reach matches by root or rejects faithfully. Deliberate divergences
from the spec *text* that no vector observes are catalogued per fork in this file.

**Out of scope** (deselected in `walk_cases`, not collected):

- **Fulu `fork` / `transition`** (Electra→Fulu): the upgrade and the pre-fork Electra
  blocks both need a complete Electra parent fork the library never builds. The
  **Gloas** `fork` / `transition` (Fulu→Gloas) and the **Heze** ones (Gloas→Heze)
  are in scope and green.
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
function whose verdict belongs to an external execution client routes through a
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
questions: is the index _load-bearing_ (data-derived and not otherwise bounded), has a
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
  balances / participation share a length; the input is well-formed). `getWeight`,
  `computeCommittee`, and the builder-registry queries keep this shape. Making it reject
  means either an `Except` return, when the index is genuinely untrusted (the first case
  above), or the proof-carrying form once the length invariants are proved (`FUTURE_WORK.md`).

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
driver's pass / expected-rejection / out-of-scope / bug-smell buckets.

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
conversions, `vget`, `vecSliceEq` (fixed-window byte-slice equality), `vmodGet` /
`umodIdx` (ring-buffer read / write index), `sszDrop` / `sszOfArray`, `bitGet` / `bitSet`,
and `hasFlag` / `addFlag`. The cap-clamping append moved to SizzLean (`SSZList.push`,
with `sszAppend` / `appendState` on top), so the old `sszPush` is gone. `Spec.State`
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
harness then reports a returned error by its constructor (a `.todo` as out-of-scope, any
other as a bug-smell test failure). The `valid` flag on the standalone `attestation` /
`attester_slashing` steps matters for the `validate_on_attestation` vectors, where the wire
`valid: false` marks an attestation `on_attestation` is meant to reject.

`on_block` reads the current head before inserting the block and applies the proposer
boost only when the block is timely, no boost is already set, and the block shares the
head's dependent root (`get_dependent_root`, gated by `MIN_SEED_LOOKAHEAD`), the v1.7
rule.

The linear DAG walks route through fuel-bounded combinators (§12). `getAncestor` and the
`getHead` descent read `store.blocks` as they go, so they thread the store monad through
`fuelLoop`. The one tree walk, `filterBlockTree`, recurses over every child inside a fold,
which a linear combinator cannot express, so it keeps a local fuel-bounded `where` helper.
The totality the doc wants is met either way.

The fork-choice weight path still runs on raw `UInt64` where the pyspec's `uint64` ops
raise, and it is deferred as one piece because it rests on one root: `getTotalBalance`
(`phase0/beacon-chain.md:1130-1140`), whose `sum(...)` accumulates in `Gwei` and raises,
while this fold wraps. `committeeWeight` is `getTotalActiveBalance / SLOTS_PER_EPOCH`,
`calculateCommitteeFraction` and `getProposerScore` are its products, and `getWeight`'s
proposer-boost add takes one operand from them, so checking any of those while the total
underneath still wraps would only move the wrong number around.

The conversion is larger than the fork-choice layer. `getTotalBalance` and
`getTotalActiveBalance` are pure `forkdef`s with 15 call sites across epoch processing,
rewards, registry updates, the transition spine, and fork choice; making them throwing
propagates upward through every pure caller (§7.1's rule, one layer over). The remaining
independent site is `getAttestationScore`'s own balance fold, which sums
`state.validators[i].effective_balance` directly and could be checked on its own; it stays
with the rest so the weight path converts in one go rather than half-guarded. Reaching any
of them takes a total active balance within a factor of the `uint64` bound, which no
preset's validator set approaches.

The reference catches different exceptions per step kind, so what satisfies a
`valid: false` step varies too. `expect_assertion_error` (`context.py:424-435`) catches
`IndexError` for the attestation, attester-slashing, envelope, and PTC-message steps.
`add_block` catches `AssertionError` and `BlockNotFoundException` alone
(`fork_choice.py:389`). `FcStepKind` carries that table, and `checkStepValidity`
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

- **`process_pending_deposits` resets `deposit_balance_to_consume` by stop reason.** An
  eth1-bridge / not-finalized / per-epoch-limit stop resets it to zero; a churn-limit
  stop carries `available_for_processing − processed_amount` forward. `ppdLoop` returns
  the `churnLimitReached` flag so the caller writes the right value.
- **`apply_pending_deposit` is signature-gated.** A new pubkey joins the registry only
  when `is_valid_deposit_signature` passes (the proof-of-possession the deposit contract
  does not check). The domain is fixed (`compute_domain(DOMAIN_DEPOSIT)`, genesis fork
  version, zero `genesis_validators_root`), so the check is one `[CryptoBackend].verify`.
- **`initiate_validator_exit` bounds the withdrawable epoch.** It asserts `exit_epoch +
MIN_VALIDATOR_WITHDRAWABILITY_DELAY < 2^64` before the write, so an over-range case
  rejects faithfully (matching the pyspec's `uint64` serialization `ValueError`) instead
  of wrapping silently on Lean's `UInt64`. Valid exits never approach the bound. Gloas
  inherits the substep with no Gloas-side change.
- **`process_execution_payload` takes the execution engine as valid.** It checks
  parent-hash / prev-randao / timestamp consistency and caches the header;
  `verify_and_notify_new_payload` is the consumer's responsibility, which is valid for
  `sanity/blocks`. The timestamp is `compute_time_at_slot(state, state.slot)`, the
  millisecond form every other clock site in the tree reads, and the standalone
  `operations/execution_payload` format threads the
  test's `execution.yaml` engine verdict via `CaseMeta.executionValid` to model an
  engine rejection. The blob-parameter bound is enforced where the operation format
  supplies it. The skip is safe for the in-scope corpus by audit, not just by
  assumption: every invalid `sanity/blocks` / `finality` / `random` case (82, across
  both presets and both forks) rejects through a consensus `assert` the in-block
  pipeline models, signatures, blob-count limits, payload-attestation checks, the
  execution-requests root, slot / parent consistency, duplicate operations, the state
  root, so none reaches a clean run that an engine verdict alone would have rejected.
  An invalid block that depended on the engine verdict would run clean and surface as a
  `likelyBug` "expected a rejection but ran clean", not a silent pass.

`CryptoBackend.aggregatePubkeys` exists because `get_next_sync_committee` needs BLS
pubkey aggregation (the `ffi` / `verifyOff` backends delegate to
`LeanHazmat.Bls.ethAggregatePubkeys`; the `symbolic` backend returns a zero point).

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
`builderRegistryLimit` / `builderPendingWithdrawalsLimit` / `maxPayloadAttestations` /
the builder-payment threshold and builder prefixes and domains (universal); and
`gloasForkVersion` / `churnLimitQuotientGloas` / `consolidationChurnLimitQuotient` /
`maxPerEpochActivationChurnLimitGloas` / `minBuilderWithdrawabilityDelay` (config).

`upgradeToGloas` copies the carried-over fields, initializes the ePBS fields, builds the
PTC window from the Fulu pre-state's committees (`initialize_ptc_window` / `compute_ptc`,
called on the boxed Fulu state since the committee helpers are Fulu's), and onboards
builders from the pending-deposit queue (`onboard_builders_from_pending_deposits`). It
takes `GLOAS_FORK_VERSION` as a parameter and sets `fork := {previous :=
pre.fork.current, current := GLOAS_FORK_VERSION, epoch := currentEpoch}`.

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

`Gloas.Operations` inherits the handlers EIP-7732 leaves unchanged (`attester_slashing`,
`bls_to_execution_change`, `withdrawal_request`, `consolidation_request`,
`sync_aggregate`) verbatim. The ePBS-modified handlers are Gloas `forkdef`s:
`process_proposer_slashing` (Fulu's logic plus the builder-payment cleanup),
`process_voluntary_exit` and `process_deposit_request` (each fronted by a builder-index
branch over the builder registry). The builder-registry helpers (`is_builder_index`,
`is_active_builder`, `get_pending_balance_to_withdraw_for_builder`,
`initiate_builder_exit`, `apply_deposit_for_builder`, `add_builder_to_registry`,
`get_index_for_new_builder`, and the rest) land here and feed
`onboard_builders_from_pending_deposits`. The payload-aware `process_attestation` (the
`data.index < 2` payload bit and the same-slot builder-payment weight accounting), the
new `process_payload_attestation`, the bid (`process_execution_payload_bid`),
`process_parent_execution_payload`, and the PTC read helpers complete the surface. The
builder-aware `process_withdrawals` is the four-phase sweep (builder queue, pending
partials, builder sweep, validator sweep) with the running-list cap that composes across
phases. `Gloas/Transition.lean` reshapes `process_block` (drop
`process_execution_payload`, prepend `process_parent_execution_payload`, add
`process_execution_payload_bid`, payload-free `process_withdrawals`, the in-body
`process_payload_attestation`s), `process_slot` (clear the next slot's
payload-availability bit), and `process_epoch` (builder-pending-payments and
`process_ptc_window` last). The `transition` format folds pre-fork Fulu blocks, applies
`upgradeToGloas` plus onboarding at the boundary, then folds post-fork Gloas blocks.

## Heze diff

EIP-7805 changes no state-transition substep, so Heze inherits the Gloas spine whole
and the diff is confined to the fork-choice inclusion-list layer. FOCIL ships no
behavioral conformance vector at the alpha.11 pin, so the divergences below are anchored
to the pinned spec text and the `EthCLSpecs/Heze/ForkChoice.lean` pins.

- **`is_inclusion_list_satisfied`** (`heze/fork-choice.md:54-62`) defers its verdict to
  `ExecutionEngine.is_inclusion_list_satisfied`, an Engine-API call against an external
  execution client. This harness has no execution layer, so the call goes through the
  `[ExecutionEngine]` typeclass (the Engine seam above), whose default instance answers
  the constant `true`. That default is the execution-layer trust boundary of the FOCIL
  gate. No conformance vector reaches the discriminating `false` branch.

- **The `InclusionListStore` rides inside the fork-choice `Store` as a field.** The
  spec keeps it as a process-lifetime singleton reached through
  `get_inclusion_list_store()` (`heze/inclusion-list.md:28-38`), and this framework has no
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

## Harness

`pyspec_server` is a long-lived, crash-tolerant loop (a malformed request reports failed
and the loop continues), one per `pytest-xdist` worker via the `conftest.py` session
fixture (re-spawn on death). `harness.py` does acquisition / walk / snappy / request
encoding; `test_pyspec.py` is the reject-faithfulness verdict. The server emits one
tab-separated line per case, so two detail sources that could embed a newline and
desync the worker are flattened at the chokepoint: `EthCLLib.Spec.sanitizeDescr` takes
the first trimmed line of an `assert` descriptor, and `CaseResult.render` flattens any
newline / tab in the detail to a space (the detail is diagnostic only). The
`ServerClient` drains non-protocol lines (lake / startup stdout) and retries once on a
desynced or dead server, so the parallel run is deterministic.

## Genesis

`SPECS_ARCHITECTURE.md` §10.1 marks `genesis` in scope and §6.1 names
`initializeBeaconStateFromEth1` / `isValidGenesisState`. The pytest corpus carries no
`genesis` vectors for Fulu, Gloas, or Heze at the `v1.7.0-alpha.11` pin, so there is nothing to
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

- **`Proofs/BuilderIndex.lean`** establishes three `bv_decide` theorems over
  `isBuilderIndex`, `toBuilderIndex`, and `convertBuilderIndexToValidatorIndex`,
  proving the builder-index flag round-trip and tagging properties.

- **`Proofs/GetPtc.lean`** proves `getPtc`'s `else`-branch offset into
  `ptcWindow` stays in range for its two guarded call sites:
  `getPtcElseOffset_lt_next_slot` under `process_payload_attestation`'s guarantee
  (`data.slot + 1 == state.slot`), and `getPtcElseOffset_lt_same_slot` under
  the fork-choice replay callers' exact-equality guarantee (`slot ==
  curSlot`). Both via `UInt64`/`Nat` bridging lemmas and `omega`, no mathlib.

- **`Proofs/BuilderPendingPayments.lean`** proves `processBuilderPendingPayments`'s
  local before/after behavior for one call: the withdrawals loop reduces to a
  bounded `SSZList.push` fold over the qualifying previous-epoch payments' withdrawals,
  in slot order, and the payment window shifts down by `SLOTS_PER_EPOCH`. A
  capacity-guarded corollary derives the full, unclamped append under an explicit
  headroom hypothesis. It does not prove protocol-wide exactly-once settlement or say
  anything about `settleBuilderPayment` / `processProposerSlashing`, the other paths
  that clear a `BuilderPendingPayment`.

- **`Proofs/CanBuilderCoverBid.lean`** characterizes `canBuilderCoverBid`'s
  `Bool` result exactly: `canBuilderCoverBid_iff` states the guard in the
  implementation's own `UInt64` `builderBalance` / `minBalance` terms;
  `canBuilderCoverBid_iff_toNat_add_le` restates it over `Nat` as a single
  non-wrapping addition-fits-in-balance fact. Both hold unconditionally under
  total/default indexing semantics, including fallback behavior for an
  out-of-range `builderIndex`.

- **`Proofs/InitializePtcWindow.lean`** establishes three `simp`-closed theorems
  over `initializePtcWindow`: its two index regions (the empty first-epoch
  placeholder and the remainder computed via `computePtcFromFulu`), plus a
  `default` corollary for the first region.

- **`Proofs/InitiateBuilderExit.lean`** gives the whole-transition
  `initiateBuilderExit_run_eq` equation and projects it onto the builder registry
  as one unconditional `SSZList.set!`. The in-range and out-of-range theorems read
  that projection through `SizzLean.Proofs.SSZListSet`, so the range split happens
  at the read rather than in a second transition proof. It also proves that the
  withdrawability-delay addition does not wrap for the shipped minimal and
  mainnet configurations.

- **`Proofs/Run.lean`** names `GloasRun`, the `EStateM StateTransitionError State`
  the Gloas proofs pin their `forkdef` bodies to. `StateTransition` is a parameter
  of a fork body, so every run theorem has to fix it; this fixes it once.

- **`Proofs/IsValidIndexedPayloadAttestation.lean`** proves a two-layer,
  backend-generic characterization of `isValidIndexedPayloadAttestation`. Layer 1
  mirrors the implementation's literal validation gates, `validators[i.toNat]!`
  included. Layer 2 restates them semantically and binds the in-range proof in an
  `∃`, so its pubkey array reads the registry through `Array.attach` and no
  panicking index survives into the public statement. No mathlib.

- **`Proofs/ProcessOperations.lean`** places its public declarations in
  `EthCLSpecs.Proofs.Gloas`. It characterizes Gloas `processOperations` at
  `GloasRun`; handlers and later failure postconditions remain opaque.

- **`Proofs/UpdateCheckpoints.lean`** rewrites Gloas's `updateCheckpoints` as a
  single record update, which doubles as the frame condition that no other Store
  field moves. On top of it sit unchanged-or-advances characterizations for the
  justified and finalized checkpoints, plus monotonicity corollaries proving that
  neither recorded epoch decreases. The proofs use ordinary case analysis and
  core `UInt64` ordering lemmas. Their theorems live in `EthCLSpecs.Proofs.Gloas`
  rather than the flat `EthCLSpecs.Proofs`, since Fulu declares the same function.

- **`CONSENSUS_PROOF_CANDIDATES.md`** tracks candidate consensus proof targets.
