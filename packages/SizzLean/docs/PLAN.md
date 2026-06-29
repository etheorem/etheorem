# SizzLean: Implementation Plan

This document sequences the work that
[`ARCHITECTURE.md`](ARCHITECTURE.md) describes, the SizzLean
library's plan. Each stage has a goal, the concrete
deliverables it ships, an acceptance criterion (one observable
that says the stage is done), and notes on dependencies,
parallelism, and risk.

The sibling subpackages (`LeanSha256`, `EthCLLib`, `EthCLSpecs`)
appear only where SizzLean's stages need them, `LeanSha256` as the
pure-Lean SHA-256 reference SizzLean's `Hasher.Sha256Spec`
instance bridges to, `EthCLLib` / `EthCLSpecs` as the downstream
consumers whose consensus containers validate SizzLean's user
surface. Their own plans (if they grow distinct staging) live
under each subpackage's own docs.

**Note on paths.** The plan was written and incrementally amended
across multiple iterations. Per-stage file-path references in the
"Deliverables" lists describe what the stage *originally produced*
under the pre-monorepo layout; many of those files have since
moved to `packages/SizzLean/SizzLean/...` paths (or, for some
Eth-side stages, to `packages/EthCLLib/...` and
`packages/EthCLSpecs/...`). The deliverables themselves landed;
the paths drifted. ARCHITECTURE.md §12 carries the canonical
current layout.

The sequencing matches §14 of ARCHITECTURE.md: Phase 1 lays down
the spec totality plus proof scaffolding (narrow first cut on
`BasicSupported`); Phase 2 ships the user-facing typeclass +
deriving + FFI hash; Phase 3 instantiates the consensus types and
validates against `ethereum/consensus-spec-tests`; Phase 4 is
deferred hardening and performance, including the cached
Merkle-tree layer, with no fixed order among its stages; Phase 5
is the closing formal-verification effort (widen the three central
theorems to all of `Supported`). The principle through phases 3–5
is "validate first, then build": empirical conformance grounds
both the performance work in Phase 4 and the proof work in Phase 5.
Stages within a phase generally serialise except where called out.

No time estimates, these depend on developer capacity and how much of
the toolchain (Lake `extern_lib` for FFI, `bv_decide`, `Aesop`)  needs
discovery vs. is already familiar.

---

## Stage 0: Project bootstrap

**Goal.** Establish the build, lint, and CI baseline that every later
stage assumes.

**Deliverables.**
- `lakefile.toml` left declarative; no `lakefile.lean`.
- A project-wide `set_option autoImplicit false` discipline (per
  CLAUDE.md): each new file opens with this option, so missed implicits
  are caught at elaboration time rather than papered over.
- CI (`.github/workflows/lean_action_ci.yml`) runs `lake build` on the
  pinned toolchain, already present; verify and tighten if needed.
- Empty `SizzLean/Basic.lean` deleted or repurposed once Stage 1 lands.
- README skeleton points at ARCHITECTURE.md and PLAN.md.

**Acceptance.** `lake build` succeeds on a clean checkout; CI is green.

**Notes.** No external dependencies yet. Reach for `batteries` only when
a specific stage needs a list/array utility that core doesn't ship.
Don't pre-import.

---

## Phase 1: Spec foundation

Layer 1 totality (`serialize`, `deserialize`, `hashTreeRoot`) plus the
proof *scaffolding*: the `@[ssz_simp]` set, the `Supported`
predicate that names the implemented arms honestly, and narrow
first-cut theorems on `.bool` to prove the scaffolding works
end-to-end. **Complete coverage of the three central theorems is
deferred to Stage 18 (Phase 5 closing)**, after the empirical
pyspec suite (Phase 3) has validated that the implementation is
actually correct on the pyspec consensus-specs test vectors.
Proving a wrong implementation right is wasted work; we earn the
right to invest in the universal proofs by passing the tests first.

The cost of this reordering: until Stage 18 lands, `SSZ.roundtrip`
is gated by `BasicSupported r.shape` and widens one constructor at
a time. User types whose shape isn't yet covered still get total
serialize/deserialize and pass conformance. They just don't yet
get the verified-by-inheritance corollary.

### Stage 1: `Hasher` abstraction (class only, no instances)

**Goal.** Declare the abstract hash interface that Layer 1 and Layer 4
parameterise over. No SHA-256 implementation yet. Phase 2 brings the
FFI shim in.

**Deliverables.**
- `SizzLean/Hasher.lean`: `class Hasher (H : Type)` with `hash` and
  `combine` methods returning a 32-byte `ByteArray`.
- Module docstring framing the class as the library consumed by Spec
  and Tree, with a forward pointer to ARCHITECTURE.md §9.

**Acceptance.** `import SizzLean.Hasher` compiles; `variable [Hasher H]`
is usable in downstream files.

**Risk.** Low. Pure class declaration; no implementation work.

### Stage 2: Layer 1 Spec: `SSZType` + `interp` + constants

**Goal.** Reflect the SSZ grammar as Lean data and define what each
shape's values look like.

**Deliverables.**
- `packages/SizzLean/SizzLean/Spec/Type.lean`: `inductive SSZType` covering the seven
  SSZ shapes mainline beacon-chain types actually use: `uintN`, `bool`,
  `vector`, `list`, `bitvector`, `bitlist`, `container`. `deriving
  Hashable`.
  - **Intentionally omitted** (no consensus type from `phase0`
    through `gloas` uses any of these): `union`, `progContainer` /
    `stableContainer` (EIP-7495), `progList` / `progBitlist` (EIP-7916),
    `compatUnion` (EIP-8016). See the `Spec/Type.lean` docstring for
    the rationale. Re-adding any of them is a constructor-plus-arms
    job if/when a fork actually adopts one.
- `packages/SizzLean/SizzLean/Spec/Interp.lean`: `def SSZType.interp : SSZType → Type`.
- `packages/SizzLean/SizzLean/Spec/Constants.lean`: `BYTES_PER_CHUNK`,
  `BYTES_PER_LENGTH_OFFSET`, `MAX_LENGTH`.
- Per-file `/-! … -/` module docstrings naming the consensus-specs SSZ
  section each implements.

**Acceptance.** A handful of `#guard` checks: `interp (.uintN 64) = UInt64`,
`interp (.bool) = Bool`, etc., compile and pass.

**Risk.** Low. Mostly transcription from the spec; the only judgement
calls are how to encode containers (`HList`) and bounded lists
(`{ xs // xs.size ≤ cap }`).

### Stage 3: Layer 1 Spec: `serialize` + `deserialize`

**Goal.** Total recursive encode and decode functions over `SSZType`.

**Deliverables.**
- `packages/SizzLean/SizzLean/Spec/Serialize.lean`: `def serialize : (s : SSZType) → s.interp → ByteArray`.
- `packages/SizzLean/SizzLean/Spec/Deserialize.lean`: `def deserialize : (s : SSZType) → ByteArray → Except SSZError (s.interp × Nat)`.
- Termination via `decreasing_by` + `List.sizeOf_lt_of_mem` for the
  `container` / `union` cases.
- A handful of `example` blocks demonstrating known wire-format vectors
  via `decide` or `#guard`.

**Acceptance.** `lake build` succeeds; the example blocks pass; for at
least three small concrete shapes, `deserialize s (serialize s x) = .ok (x, _)`
holds by `decide` or `native_decide`.

**Risk.** Medium. Offset arithmetic for variable-sized container fields
is fiddly; getting the empty-`List` and empty-`Bitlist` edge cases right
matters (consensus-specs is explicit and precedent implementations have
fork-causing bugs here).

### Stage 4: Layer 1 Spec: `hashTreeRoot`

**Goal.** Total Merkleization function, parameterised by the abstract
hasher.

**Deliverables.**
- `packages/SizzLean/SizzLean/Spec/HashTreeRoot.lean`: `def hashTreeRoot [Hasher H] : (s : SSZType) → s.interp → ByteArray`.
- Mix-in handling for `list` (`mix_in_length`) and `bitlist`.
- `def ZERO_HASHES_SPEC : Vector ByteArray 65` defined abstractly over
  `[Hasher H]`, used by the spec; the cache layer will materialise
  concrete `ZERO_HASHES` values in Stage 12.

**Acceptance.** `lake build` succeeds. No `#eval` of an actual root
yet (no `Hasher` instance until Stage 9), but type-checking confirms
the function is total.

**Risk.** Medium. Chunk packing for basic-type lists and the
trailing-delimiter-bit treatment in `bitlist` Merkleization both have
to match the spec exactly.

### Stage 5: Layer 2: proof scaffolding + roundtrip first cut

**Goal.** Stand up the proof infrastructure: the `@[ssz_simp]` set,
the `SSZType.Supported` predicate (carves out implemented arms), and a
narrower `BasicSupported` predicate that grows constructor by
constructor. Then close `decode_encode` for one concrete shape
end-to-end as a smoke test. Universal coverage across `Supported`
is Stage 18.

**Deliverables.**
- `packages/SizzLean/SizzLean/Proofs/Simp.lean` + `SimpAttrs.lean`: declares the
  `@[ssz_simp]` simp set and tags spec equations.
- `packages/SizzLean/SizzLean/Spec/Supported.lean`: `SSZType.Supported` /
  `SupportedBounded` predicates carving out the (non-deferred) arms
  of `serialize` / `deserialize`, so theorems can be stated against
  them honestly without paper-overing the gaps.
- `packages/SizzLean/SizzLean/Proofs/Roundtrip.lean`: `BasicSupported` predicate
  (starts with `.bool`) and `theorem decode_encode : ∀ s, BasicSupported s → ∀ x, deserialize s (serialize s x) = .ok (x, _)`.
- Tactic vocabulary: `simp [ssz_simp]`, `unfold`, `cases`, `decide`.

**Acceptance.** Theorem closed for `BasicSupported` (≥ 1 constructor)
with no `sorry`, no `native_decide` on the proof path. CI runs the proof.

**Risk.** Low for the first cut. The scaffolding is straightforward,
the `.bool` arm closes by `cases` + `unfold` + `rfl`. The high-risk
work is Stage 18's universal coverage; Phase 3 conformance must land
first so the proof effort targets a known-correct implementation.

### Stage 6: Layer 2: non-malleability + size bound first cuts

**Goal.** Mirror Stage 5's narrowing on the other two central
theorems so all three travel together: each new constructor added to
`BasicSupported` extends roundtrip, injectivity, and size bound at
once.

**Deliverables.**
- `packages/SizzLean/SizzLean/Spec/MaxByteLength.lean`: schema-derived static upper
  bound `maxByteLength : SSZType → Nat`.
- `packages/SizzLean/SizzLean/Proofs/Injective.lean`:
  `theorem serialize_injective : ∀ s, BasicSupported s → ∀ x y, serialize s x = serialize s y → x = y`.
  Direct corollary of `decode_encode` plus `Except.ok.inj`.
- `packages/SizzLean/SizzLean/Proofs/SizeBound.lean`:
  `theorem encode_size_le_max : ∀ s, BasicSupported s → ∀ x, (serialize s x).size ≤ s.maxByteLength`.
  Independent induction; closes by `cases` + `decide` for the
  `.bool` arm.

**Acceptance.** All three central theorems closed for `BasicSupported`
with no `sorry`; CI green.

**Risk.** Low. `serialize_injective` is three lines; the size bound
is mechanical. Widening to full `Supported` / `SupportedBounded` is
Stage 18's job.

**Phase 1 exit gate.** Layer 1 spec functions total; proof
infrastructure (simp set, `Supported` predicates, `BasicSupported`
dispatch) in place; the three central theorems closed for
`BasicSupported` (≥ 1 constructor) without `sorry`, `native_decide`,
or unverified axioms beyond Lean's standard ones. The library has
its *scaffolded* correctness story; complete coverage lands in
Stage 18, after Phase 3 conformance grounds the proof effort.

---

## Phase 2: User surface

Lands the user-facing API: `SSZRepr` typeclass + `deriving SSZRepr`
handler + Day-1 FFI SHA-256. After this phase the library has a
complete library for writing user types and a real `Hasher`
instance, enough to run `ssz_generic` pyspec against the
spec functions in Phase 3.

The cached Merkle-tree work (`Tree`, `TreeBacked`) that originally
lived here as the "production-primitives track" has moved to
Phase 4. It's a *performance* layer, asserted equivalent to the
spec rather than load-bearing for correctness, so it earns its
keep after empirical conformance validates the spec it sits on
top of. Same "validate first, then build" principle the proof
work in Stage 18 follows.

### Stage 7: `SSZRepr` typeclass + library instances

**Goal.** Land the user-facing typeclass and the leaf instances the
deriving handler will recurse on.

**Deliverables.**
- `packages/SizzLean/SizzLean/Repr/Class.lean`: `class SSZRepr T` with `shape`,
  `toRepr`, `fromRepr`, `to_from`, `from_to` fields; thin wrappers
  `SSZ.serialize` / `SSZ.deserialize` / `SSZ.hashTreeRoot`; the
  `SSZ.roundtrip` per-user-type corollary.
- `packages/SizzLean/SizzLean/Repr/Instances.lean`: `SSZRepr` instances for `UInt8/16/32/64`,
  `Bool`, `BitVec n`, `Vector α n`, `SSZ.List α n`, `Bitvector n`,
  `Bitlist n`, sigma-typed unions. Plus the `SSZList` / `Bitlist`
  element surface (`get!` / `set!` / `size` / `toArray` / `toList`
  / `foldl` / `map` / `any` / `all` / `findIdx?` / `contains`, a
  `ForIn` instance, and a faithful `GetElem` with validity
  `i < xs.size`), so `xs[i]!`, `xs[i]?`, and `xs.size` work
  uniformly across `Vector` and `SSZList` in `sszUpdate`
  projections and in spec bodies, with no `.val` projection.

**Acceptance.** A hand-written `instance : SSZRepr Foo` for a small
example structure compiles, and an `example : deserialize (serialize x) = .ok x`
closes via `SSZ.roundtrip`. The roundtrip corollary is gated by
`BasicSupported r.shape` until Stage 18 widens it, so the example
structure must have a `BasicSupported`-compatible shape (e.g. a
container of `Bool`s at first). The gate loosens automatically as
Stage 18's proof set grows.

**Risk.** Low to medium. The iso laws (`to_from`, `from_to`) for the
library instances need to discharge cleanly. Usually `rfl` or `simp`
closes them, but composite types may need a small lemma per shape.

### Stage 8: `deriving SSZRepr` handler

**Goal.** Make the user-surface ergonomic: vanilla `structure ...
deriving SSZRepr` produces the instance with no manual work.

**Deliverables.**
- `packages/SizzLean/SizzLean/Repr/Deriving.lean`: `registerDerivingHandler ``SSZRepr`
  that walks `getStructureFields`, looks up `SSZRepr.shape` per field
  via `synthInstance?`, assembles the matching `SSZType.container`,
  emits the iso plus `rfl` proofs.
- Module docstring walks a first-time reader through the Lean
  metaprogramming idioms (per CLAUDE.md's literate-by-default).
- An `example` block deriving `SSZRepr` for a small test structure and
  closing the round-trip via the corollary.

**Acceptance.** `structure Foo where ... deriving SSZRepr` works for at
least one composite of two primitives.

**Risk.** Medium. Lean 4 deriving handlers are well-trodden but
unforgiving; expect to study `src/Lean/Elab/Deriving/Repr.lean` and
`FromToJson.lean` before writing.

### Stage 9: FFI SHA-256 (`@[extern] opaque`)

**Goal.** Land the Day-1 SHA-256 implementation: opaque to the kernel,
backed by a C shim, validated empirically against NIST CAVP vectors.

**Deliverables.**
- `SizzLean/FFI/Sha256.lean`: `@[extern "lean_ssz_sha256_combine"] opaque sha256Combine` plus `instance : Hasher Sha256`.
- Lake `extern_lib` block in `lakefile.toml` shipping the C shim.
- A small C shim (`packages/SizzLean/csrc/sha256_shim.c` or similar) wrapping
  OpenSSL/BoringSSL/`gohashtree`. Pluggable behind one symbol name.
- `packages/SizzLean/SizzLeanTests/Sha256Vectors.lean` (small file) running NIST
  CAVP test vectors through `native_decide` in CI.

**Acceptance.** `#eval sha256Combine ⟨…⟩ ⟨…⟩` returns the expected
32 bytes for known test inputs; the NIST vectors pass in CI.

**Risk.** Medium. Lake's `extern_lib` + C-build integration is the
fiddly part. `argumentcomputer/Blake3.lean` is the canonical template
to crib from; `tydeu/lean4-alloy` is available if inline-C blocks
become useful.

**Notes.** This is the only stage that introduces a non-Lean toolchain
dependency (a C compiler in CI). Document the requirement explicitly in
the README.

**Phase 2 exit gate.** Users can write `structure Foo deriving SSZRepr`
and get total `SSZ.serialize` / `SSZ.deserialize` / `SSZ.hashTreeRoot`
through Layer 1's spec functions, plus a working `Hasher Sha256`
instance via the FFI shim. Verified-by-corollary roundtrip is
available for `BasicSupported`-compatible shapes (currently `.bool`
and `.container [.bool, .bool]`); full coverage arrives with
Stage 18. `hashTreeRoot` is uncached and slow; the cache layer
lands in Phase 4. The library is functionally complete as a
library; the Ethereum-types instantiation and the empirical
pyspec suite come next.

---

## Phase 3: Application + empirical validation

Phase 3 is where the library earns its right to invest in complete
formal verification: passing the pyspec `ethereum/consensus-spec-tests`
release vectors empirically validates that the spec functions
implement SSZ correctly. Without this, Stage 18's proof effort risks
proving a wrong implementation right, a far more expensive failure
mode than a missing proof.

Note that Stage 11's `ssz_generic` runner only needs Layer 1 spec
functions plus a concrete `Hasher`, so the type-agnostic part can land
as soon as Stage 9 (FFI SHA-256) is done, earlier than Stage 10 if
convenient. The per-fork part depends on Stage 10's Eth types.

### Stage 10: Eth primitives + composite types

**Goal.** Demonstrate the library works at production scale by
instantiating the consensus-spec types.

**Deliverables.**
- `SizzLean/Eth/Primitives.lean`: `Slot`, `Epoch`, `ValidatorIndex`,
  `Root`, `Bytes32`, `Gwei`, `BLSPubkey` (each a thin wrapper over
  `UInt64`, `BitVec 256`, or `ByteArray`).
- `SizzLean/Eth/BeaconBlock.lean`, `Validator.lean`, `BeaconState.lean`,
  `ExecutionPayload.lean`: composite consensus types as plain
  structures with `deriving SSZRepr`.
- An `example` block per file showing round-trip for a hand-constructed
  value.

**Acceptance.** Every type derives `SSZRepr` cleanly; CI green.

**Risk.** Low. If `deriving SSZRepr` (Stage 8) works, this is
mechanical.

### Stage 11: Pyspec suite (`ssz_generic` + per-fork tests)

**Goal.** Validate every encode / decode / HTR path against the
pyspec test vectors from `ethereum/consensus-spec-tests` releases.
Passing this stage is the gating signal for Stage 18: it is what
makes the complete-proof investment well-targeted rather than
speculative.

**Deliverables.**
- `packages/SizzLean/SizzLeanTests/SSZGeneric.lean`: runner that consumes the
  type-agnostic `ssz_generic` vectors (`uints`, `basic_vector`,
  `bitlist`, `bitvector`, `containers`, …). Depends on Stage 9
  (FFI SHA-256) only; can land before Stage 10.
- `packages/SizzLean/SizzLeanTests/PerFork.lean` (or similar): per-fork
  composite-type runner for at least one fork (Phase 0 → Capella is
  reasonable starting scope). Depends on Stage 10's Eth types.
- CI integration via `native_decide` or a Lean-native runner.

**Acceptance (two parts).**
- **14a: Generic.** All `ssz_generic` vectors pass in CI. *This is
  the gate for Stage 18.*
- **14b: Per-fork.** At least one fork's per-type pyspec tests
  pass in CI.

**Risk.** Medium. The test-fixture format is well-documented but
voluminous; expect plumbing work to read the YAML/SSZ vector files
into Lean.

**Notes.** This is also where the FFI SHA-256 assertion (Stage 9) gets
its strongest empirical backing. Every Merkle root in the pyspec
suite indirectly checks the C shim.

**Phase 3 exit gate.** Library passes upstream consensus-specs test
vectors. SizzLean is publishable as a working SSZ implementation at
this point; the empirical conformance gives us the confidence that
the spec functions are correct, the foundation Stage 18's complete
formal verification builds on.

---

## Phase 4: Production primitives + deferred hardening

Performance and hardening work, all gated on Phase 3 having
established that the spec functions match the consensus-spec test
vectors. Stages 12–14 (the cached Merkle-tree layer) lived in
Phase 2 originally; they moved here for the same reason Stage 18
lives in Phase 5. They're a *performance* layer asserted equivalent
to the spec, so we validate the spec first and then optimise on
top of a known-correct library. Stage 13 in particular is the
single highest-risk implementation file in the project (ARCHITECTURE.md
§6.2); deferring it past empirical validation gives the property
test a known-good reference oracle.

Phase 4's structure now has *one explicit dependency chain* and
several independent satellites:

* **Cache backbone (Stages 12 → 13 → 14a → 14b → 14c → 14d)**: must
  serialise. `Node` is the library; `setAt` works on it; `TreeBacked`
  is the user-facing scaffold (14a); `Node.ofShape` makes the cache
  *useful* (14b); cached `setField` / `setIndex` (14c) is the
  load-bearing operation; **`sszUpdate t with f := v, g := w`
  syntax (14d)** ships the ergonomic surface plus a per-statement
  batched walker (`setManyAt`). This whole chain lands before any
  perf work because the perf optimisations in Stage 17 all assume
  both an interior-populated tree *and* a batched multi-update
  primitive to extend cross-statement.
* **TCB tightness (Stage 15).** Pure-Lean `Sha256Spec` + `@[csimp]`.
  Independent of the cache chain; sequenced *after* the cache work
  so it can be timeboxed against measured cost rather than blocking
  cache progress.
* **Perf optimisations (Stage 17a–e).** Five independent
  benchmark-driven efforts. Each presupposes Stages 12–14c are
  complete; otherwise there is no tree shape for them to act on.

Stage 16 (the `profile%` macro for EIP-7495) is no longer in the
active plan. See its section below for the rationale.

### Stage 12: Tree layer core (`Node`, `ZERO_HASHES`, `merkleRootWithCache`)

**Goal.** Build the persistent binary Merkle tree with per-node hash
caching that production `hash_tree_root` will use.

**Deliverables.**
- `SizzLean/MerkleTree/Node.lean`: `inductive Node` with `leaf` and
  `pair … (Option ByteArray)`; `Node.cached` accessor.
- `SizzLean/MerkleTree/Zero.lean`: `def ZERO_HASHES : Vector ByteArray 65`
  computed at module load via the recurrence
  `ZERO_HASHES[d+1] = sha256Combine (ZERO_HASHES[d]) (ZERO_HASHES[d])`;
  `def zeroLeaf`.
- `SizzLean/MerkleTree/Merkle.lean`: `Node.merkleRootWithCache` returning
  `(ByteArray × Node)` with cache-fill on the walked spine; `Node.ofLeaves`
  for building balanced trees from leaf-hash arrays. Parameterised by
  `[Hasher H]`.

**Acceptance.** Roots of small hand-built trees match the spec
`hashTreeRoot` of the equivalent SSZ value. With Phase 3 conformance
landed, the spec functions are a known-good reference oracle.

**Risk.** Low to medium. Structural recursion on `Node` is clean.

### Stage 13: `Tree.setAt` (gindex updates) + property tests

**Goal.** The highest-risk file in the project (per ARCHITECTURE.md
§6.2): structural-sharing update at a generalized index, with cache
invalidation only on the spine.

**Deliverables.**
- `SizzLean/MerkleTree/SetAt.lean`: `Node.setAt : Node → (g : Nat) → Node → Node`
  recursing on an explicit `List Bool` of gindex bits (no `partial def`).
- A property test in `packages/SizzLean/SizzLeanTests/SetAtRandom.lean` (or
  similar): for a random `Node` and a random gindex, `setAt`'s root
  equals the slow `merkleize ∘ asLeafArray` reference *and* matches
  the spec `hashTreeRoot` of the equivalent SSZ value.
- The slow reference is implemented in the same file for clarity.

**Acceptance.** Property test passes for hundreds of randomly generated
trees-and-gindexes via `native_decide` (or a Lean-native randomized
runner).

**Risk.** **Highest implementation risk in the project.** Gindex
arithmetic was Nimbus's February-2025 mainnet-fork failure mode.
The structural-recursion-on-bits formulation is the mitigation; the
property test against the spec's `hashTreeRoot` (validated against
upstream vectors in Phase 3) is the safety net.

### Stage 14: `TreeBacked` types

The user-facing tree-backed type. Split into three sub-stages
because "make `hash_tree_root` cached and incremental" actually
requires (a) the type contract, (b) a tree whose interior mirrors
the SSZ shape, and (c) operations that exploit (b). Sub-stages
serialise: 14a is the contract floor, 14b is what makes the cache
*useful*, 14c is what users actually call.

#### Stage 14a: `TreeBacked` scaffold + acceptance contract

**Goal.** Land the structure, the smart-constructor pattern, and the
acceptance-test contract.

**Deliverables.**
- `SizzLean/TreeBacked/Core.lean`: `structure TreeBacked T [SSZRepr T]
  where view : T; tree : Node`; `def ofValue` (currently builds a
  single-leaf `Node` carrying the canonical spec root); `def
  hashTreeRootCached`.
- `packages/SizzLean/SizzLeanTests/TreeBackedCoherence.lean`: property test
  `t.hashTreeRootCached = SSZ.hashTreeRoot t.view` on `Validator`
  (zero + realistic) and `BeaconBlockHeader`.

**Acceptance.** Property test passes; the type compiles and reads
cleanly; `ofValue` round-trips the canonical root.

**Risk.** Low. This is the scaffolding stage, a deliberately
degenerate `ofValue` so the contract is exercised without committing
to the deep-tree shape yet.

**Honest limitation.** With `ofValue v` collapsing the value into a
one-leaf tree, the cache slot has nothing to short-circuit; any
mutation forces a fresh `SSZ.hashTreeRoot` call. This is sufficient
to *prove the contract*, insufficient to demonstrate cache benefit.
Stage 14b lands the real cache shape.

#### Stage 14b: Deep-tree construction via `Node.ofShape`

**Goal.** Replace the placeholder `ofValue` with a real
SSZ-shape-driven tree builder, so `TreeBacked` actually exercises
its cache.

**Deliverables.**
- `SizzLean/MerkleTree/Build.lean`: `Node.ofShape (H : Type) [Hasher H] :
  (s : SSZType) → s.interp → Node`, mutually recursive with
  `Node.subtreesForFields` (containers) and `Node.subtreesForList`
  (vector / list composite elements). Per-arm logic:
  - **Basic types** (`uintN`, `bool`) → `.leaf (padToChunk
    (serializeBytes …))`.
  - **`bitvector` / `bitlist`** → chunkify the packed bytes; for
    `bitlist`, mix in the count root.
  - **`vector t n` / `list t cap`** with basic `t` → chunkify the
    flat serialisation, balance to `chunkDepth`.
  - **`vector t n` / `list t cap`** with composite `t` → per-element
    sub-trees, balanced to depth `chunkDepth n`. `list` adds
    `mixInLength`.
  - **`container fs`** → per-field sub-trees as leaves of a depth
    `chunkDepth fs.length` balanced tree.
- `SizzLean/TreeBacked/Core.lean`: rewrite `ofValue` to call
  `Node.ofShape r.shape (r.toRepr v)`.
- `packages/SizzLean/SizzLeanTests/TreeBackedCoherence.lean`: extend the
  property test to cover composite types whose interior structure
  the deep tree exercises (e.g. `Fork`, `Checkpoint`,
  `SignedBeaconBlockHeader`).

**Acceptance.** The existing coherence examples still pass; the
new composite examples pass; and an additional
`hashTreeRootCached` of a deep `Node` (post-`ofShape`) matches the
spec root for a `BeaconBlockBody` instance (preset-fixed).

**Risk.** Medium-high. This is essentially porting the spec's
`hashTreeRoot` body to build trees instead of computing roots.
It is substantial code volume (~200–400 lines mutual block), and the
match between spec and tree-layer outputs has to be byte-identical
across every constructor.

**Notes.** Stage 14b is the work that makes the rest of Phase 4's
perf optimisations (Stages 17a–e) meaningful: deferred-update
overlays, batched hashing, hash-consing, and serialized-form caches
all assume a tree whose leaves correspond to addressable fields.

#### Stage 14c: `TreeBacked` operations

**Goal.** Provide the cached-fast-path operations users actually
call: `setField` (containers), `setIndex` (vectors / lists),
`append` / `length` (lists), and a `hashTreeRoot` that takes
advantage of cached pair slots.

**Deliverables.**
- `SizzLean/TreeBacked/Container.lean`: `setField` for one
  illustrative container per fork-family (e.g. `Validator`,
  `BeaconBlockHeader`). The user picks the field; the operation
  builds the new sub-tree via `Node.ofShape`, computes the field's
  gindex, calls `Node.setAt`, and updates `view`.
- `SizzLean/TreeBacked/Vector.lean`, `TreeBacked/List.lean`:
  `setIndex`, `append`, `length` analogues.
- A property test:
  `∀ v g newField, (TreeBacked.ofValue v |>.setField g newField).
   hashTreeRootCached = SSZ.hashTreeRoot (v with field-at-g := newField)`
  across a small batch (deterministic PRNG, similar shape to the
  Stage 13 `SetAtRandom` test).

**Acceptance.** The property test passes for ≥1 illustrative
container and ≥1 vector/list type. End-to-end smoke run unchanged.

**Risk.** Medium. Per-operation correctness reduces to (a) Stage
14b's `Node.ofShape` correctness, (b) Stage 13's `setAt` correctness,
and (c) a per-shape gindex computation that's straightforward but
worth a unit test of its own (e.g. "field `k` of an N-field
container is at gindex `2^(chunkDepth N) + k`").

#### Stage 14d: Auto-generated setters + `treeUpdate` syntax

**Goal.** Eliminate the per-field boilerplate from Stage 14c and
ship a user-facing `treeUpdate t with f₁ := v₁, f₂ := v₂, …` syntax
that handles **flat, multi-field, and nested-path** updates in one
batched walk. Without this, users have to write a `Fork.setEpoch`-
style wrapper for every (container, field) pair they care about,
hundreds of declarations across Phase 0 → Fulu, and chained
single-field updates re-walk the shared spine, losing the cache
benefit on the most common workload (multi-field `BeaconState`
mutations during state transition).

**Deliverables.**

* `SizzLean/MerkleTree/SetAt.lean`: extend with `Node.setManyAt :
  Node → List (List Bool × Node) → Node`. Walks the tree once;
  partitions writes by their first bit; recurses into each side
  with the matching sublist. Allocates one new `pair` per spine
  level crossed by *any* write, regardless of how many writes
  share the prefix.
* `SizzLean/TreeBacked/MultiSetter.lean`: the `sszUpdate t with
  …` / `treeUpdate t with …` term-elaborated syntax. Parses each
  `dotted-path := value` clause, walks the structure-field
  reflection at expansion time to compose path bits across nesting
  levels, and emits a single `Node.setManyAt` call plus a `let`-
  chained view-update expression. `CachedSSZ H T` is added as an
  `abbrev` over `TreeBacked H T` so the user surface can drop the
  word "tree" entirely; both type names accept either elaborator.
  `H` comes first in the parameter order so the typical workload
  ("fix one hasher across many content types") partial-applies
  cleanly: `abbrev Sha256Cached (T : Type) [SSZRepr T] :=
  CachedSSZ Sha256 T`.
  The hasher `H` is part of the *type*, pinned once at
  `TreeBacked.ofValue` time, then inferred by every downstream
  `sszUpdate` / `hashTreeRootCached` call. Mixing hashers within a
  single cached value is a type error, not a silent root mismatch.
* `SizzLean/TreeBacked/Container.lean`: *retired entirely* once
  `sszUpdate` grew vector-index syntax (`vec[i] := v`). The
  hand-written `Fork.setEpoch` and `HistoricalBatch.Minimal.
  setBlockRoot` examples it used to host are both subsumed by
  `sszUpdate t with epoch := e` and
  `sszUpdate t with blockRoots[i] := r` respectively.

  An earlier draft of this stage proposed a `derive_tree_setters T`
  command macro that emitted one `T.set<Field>` `def` per
  structure field; it was dropped. The named setters were a strict
  subset of `sszUpdate`'s capability, and chaining them for
  multi-field updates is actively *worse* than the single-
  `sszUpdate` call (every chained call re-walks the spine and
  clears the cache on every off-target sibling, exactly the
  failure mode `setManyAt` was built to avoid). Users wanting
  first-class function values can write
  `fun t v => sszUpdate t with f := v` at the use site.
* `packages/SizzLean/SizzLeanTests/TreeBackedSetField.lean`: extend the
  property test with:
  - A flat multi-field case: `treeUpdate fork with
    previousVersion := pv, currentVersion := cv, epoch := e` on
    `Fork`, checked against the same triple-`with` on the plain
    struct. ~50 PRNG cases.
  - A nested-path case: `treeUpdate state with fork.epoch := e,
    eth1DepositIndex := i` on a minimal-preset `BeaconState`,
    checked against the equivalent nested-`with` on the plain
    struct. ~20 PRNG cases (each iteration randomises a small
    `BeaconState`; bigger budgets bloat `native_decide`).
  - An allocation-counting `#eval` (not gated, just informational)
    showing the spine-sharing win on a 5-update batched call vs
    a 5-update chain. Useful for the PR description; not a hard
    acceptance gate.

**Acceptance.** All existing 14a/14b/14c tests still pass. The new
flat-multi-field and nested-path tests pass via `native_decide`.
Manually verified: a deliberate bit-list reversal in the macro's
path composer is caught by the nested-path test on the first
iteration (root mismatch). The `Container.lean` swap-out preserves
the existing setter behavior. Stage 14c's property test should
still pass against the macro-generated setters with zero changes
to the test file.

**Risk.** Medium-low for `setManyAt` (small recursion, structural);
medium-high for the macro because `Lean.Meta.getStructureFields` +
dotted-path walking has many small edge cases (field renames,
private fields, instance-projection vs constructor-projection
distinctions). Mitigations: (a) the macro tests its expansion via
`#guard_msgs` / `set_option trace.Elab.macros true` rather than
trusting the output blindly; (b) the property tests are randomised
and run hundreds of cases, so any expansion bug surfaces as a root
mismatch.

**Notes.** This stage ships *only* per-statement batching.
Multiple writes inside a single `treeUpdate ... with ...` get
spine-sharing. Cross-statement batching (accumulating writes across
many `let mut t := …; treeUpdate t with f := v` statements into
one commit) is Stage 17a's job; the deferred-update overlay
generalises `setManyAt` from "all writes known at one expansion"
to "all writes known at scope exit".

**Basic-packed indexing: Sub-F (planned, not built).**
`sszUpdate t with vec[i] := v` works for *composite-element*
`Vector` / `SSZList` (`Vector Root N`, `SSZList Validator N`,
etc.). It is rejected at expansion time for *basic-packed*
elements (`Vector UInt64 n`, `SSZList Gwei n`, `Vector UInt8 n`),
because updating one element in a packed chunk requires reading
the neighbouring elements from the view and re-encoding the whole
32-byte chunk, a chunk-rebuild path the current macro doesn't
emit.

Today's workaround: whole-vector / whole-list replacement (works,
correct, but O(cap) merkleization rather than O(log cap)):

```lean
sszUpdate state with balances := state.view.balances.set! i newBal
```

Fine for one-off updates; impractical for state-transition loops
that touch many basic-packed elements per slot (validator balance
updates are the leading use case). Sub-F would extend `walkPath`'s
index arm with a basic-packed branch: at the element segment,
compute `chunkIdx = i / elementsPerChunk`, read the
`elementsPerChunk - 1` neighbours from the view, encode all
`elementsPerChunk` values into a 32-byte chunk (handling
length-padding for lists), wrap as `.leaf`, splice. Effort: ~half a
day for vectors, ~one day total including lists. Gated on a
measured need (i.e. a state-transition function showing
quadratic-in-N balance-update cost in profiling).

**Public-surface aliases.** The internal `TreeBacked T` /
`treeUpdate` spellings have user-facing twins `CachedSSZ T` /
`sszUpdate` that read as a value-level abstraction without
mentioning the Merkle tree. `CachedSSZ` is an `abbrev` over
`TreeBacked` (definitionally the same type) and `sszUpdate` shares
the `treeUpdate` elaborator (the same emitted `setManyAt` call,
the same compile-time gindex literals). The split is documentary:
library-internal code that touches gindex paths or the
`setManyAt` walker keeps the tree-aware names; external API
documentation uses the SSZ-flavoured names. A one-clause example
exercising both aliases at every reachable name slot lives in
`packages/SizzLean/SizzLeanTests/TreeBackedSetField.lean`
(`runAliasCases`).

### Stage 14e: `SSZ.Box` union + curated public surface: **shipped**

**Goal.** Let one function body serve both runtime and proof
callers without forcing the author to duplicate the source
between `CachedSSZ`-typed and `UncachedSSZ`-typed shapes, and
trim the library's user-facing surface to a small audited set.

**Shipped.**

* **`SSZ.Box H T`**: closed inductive (`.cached CachedSSZ H T`,
  `.uncached UncachedSSZ H T`) in `Cache/Box.lean`. Spec
  functions take `(s : SSZ.Box H T)` and use `s.view` /
  `s.hashTreeRoot` / `sszUpdate s with …` uniformly; the macro
  detects the box type and emits a two-arm match that dispatches
  to the per-flavour update path each constructor needs.

* **Four user-facing smart constructors**, all returning
  `SSZ.Box`:

  | | Sha256-pinned | Hasher-explicit |
  |---|---|---|
  | cached | `SSZ.FastBox v` | `SSZ.CachedBox H v` |
  | uncached | `SSZ.PureBox v` | `SSZ.UncachedBox H v` |

  All four substitute at a single call site. The lower-level
  `Box.ofCached` / `Box.ofPure` were demoted to `private`.
  User code reaches the type only through these four entry
  points.

* **One-flavour aliases.** `CachedSSZ.ofValue` and
  `CachedSSZ.hashTreeRoot` ship in `Cache/TreeBacked.lean` so the
  cached-only specialisation path (production code with batched
  updates between root reads) reads symmetrically with the
  `UncachedSSZ.*` side, never naming the internal `TreeBacked`
  spelling or the `Cached`-suffixed `hashTreeRootCached`.

* **Read-side macro `sszGet`.** Read companion to `sszUpdate` in
  `Cache/Update.lean`. Same dotted-and-indexed path syntax
  (`sszGet b a.b[i].c`); expands purely syntactically to
  `b.view.a.b[i].c`. Closes the last user-surface gap that
  required typing `.view` directly: a read and a write of the
  same field now differ only by the keyword and the `:= value`
  clause. The macro is invisible to Lean's kernel. `rfl` /
  `decide` / `simp` proofs about reads close exactly as if the
  projection chain were spelled out by hand, so it adds no
  proof-side complexity. `.view` survives as a lower-level
  escape hatch (useful when feeding the unwrapped value into a
  spec lemma that takes plain `T`) but is no longer the
  documented everyday read path.

* **`UncachedSSZ` demoted.** No genuine user-facing role beyond
  serving as the proof-arm payload of `SSZ.Box`: anyone reaching
  for it standalone has a simpler path (plain `T` plus Lean's
  built-in `{ x with f := v }` plus `SSZ.hashTreeRoot Sha256 x`).
  Documented inline with a prominent warning block; removed from
  the umbrella's curated re-export list; remains importable by
  qualified path so `Cache/Box.lean`'s `.uncached` constructor
  resolves.

* **Curated umbrella.** `SizzLean.lean` was pruned from 30 to
  11 re-exports, all user-facing: `Repr/{Class,Instances,Deriving}`,
  `Spec/SSZError`, `Hasher/{Class,Sha256,Sha256Spec,Sha256Equiv}`,
  `Cache/{TreeBacked,Box,Update}`. Internal modules
  (`Spec/{Type,Interp,Serialize,Deserialize,HashTreeRoot,…}`,
  `Proofs/*`, `Cache/{Uncached,MerkleTree/*}`) remain reachable
  by qualified path, `LeanEthCS`'s deriving handler still
  imports `Spec/Serialize` etc. directly, but are no longer
  presented as part of the user mental model.

* **Test-fixture move.** `SizzLean/Repr/Examples.lean` (the
  `Pair` / `DPair` SSZRepr acceptance fixtures) moved to
  `SizzLeanTests/ReprExamples.lean` so test structures no longer
  ride along on every `import SizzLean`.

* **Other `private` annotations.** `PathStep` and `elabSszUpdate`
  in `Cache/Update.lean` (the macro's internal AST and term
  elaborator, registered via the `@[term_elab]` attribute, so
  `private` doesn't break the macro's wiring). The grep showed
  most "internal-looking" Spec helpers (`zero32`, `padToChunk`,
  `chunkDepth`, `bitsToNatLE`, `ZERO_HASHES_SPEC`, …) are used
  cross-file by the Merkle-tree code or by LeanEthCS, so
  `private` (file-scoped) isn't applicable there without a bigger
  `Internal/` refactor.

* **User manual.** `packages/SizzLean/MANUAL.md` documents the
  full user-facing surface: the "one body, two flavours" pattern
  via `SSZ.Box`, the field types, the spec functions, the
  hashers, the tactic-by-goal-shape table for hash-involving
  proofs, the test recipes, and a complete API reference
  organised by interface (creating containers / boxed interface /
  plain interface / miscellaneous).

**Acceptance.** `lake build SizzLean SizzLeanTests LeanEthCS
eth_ssz_vector_runner` is green; the four `bumpEpoch`-on-`SSZ.Box`
flavour examples in `SizzLeanTests/TreeBackedSetField.lean` close
under `rfl` / `native_decide`; LeanEthCS still imports the
qualified-path internal modules it needs (`Spec/Serialize`,
`Repr/Deriving`, etc.) without change.

### Stage 11.1: Pyspec harness modernisation: **shipped**

**Goal.** The Stage 11 harness spawned `eth_ssz_vector_runner`
once per case via `subprocess.run`. At ~100 ms of Lean-runtime
startup per case × tens of thousands of cases (the
`ssz_static_full` minimal-preset sweep), wall-clock time was
dominated by spawn overhead. This stage attacks that *without*
changing the dispatch algorithm or trust commitments.

**Shipped.**

* **Batch mode in the CLI.** `eth_ssz_vector_runner batch` reads
  tab-separated request lines from stdin and writes
  tab-separated response lines to stdout, one round-trip per
  case, flushed after each. Wire format documented in
  `LeanEthCS/Cli/Main.lean`. The argv-mode subcommands (`check`,
  `root`, `ssz_generic_check`, `ssz_generic_invalid`) stay as
  the per-invocation form for ad-hoc debugging.

* **Python harness restructure.** `scripts/run_conformance.py`
  spawns the CLI once for the whole sweep via a `BatchRunner`
  context manager and pumps requests through it synchronously.
  Each case still: decompresses to a tmpfile, writes one request
  line, reads one response, unlinks the tmpfile, advances the
  progress bar. The per-case Python loop looks identical to the
  argv version; only the spawn cost moved out.

* **Live progress.** `tqdm`-driven progress bar (per-case rate +
  ETA) drawn to stderr; TTY-aware (live single-line repaint on a
  terminal, 30-second-mininterval on captured logs to keep CI
  output scrollable).

* **Per-fork explicit inheritance in LeanEthCS.** Each post-
  Phase-0 fork now ships a code-generated `Inherited.lean` that
  re-exports the consensus-spec containers it inherits unchanged
  (grouped by source fork) via `abbrev`. The dispatcher in
  `LeanEthCS/Cli/Main.lean` then references every container as
  `LeanEthCS.Forks.<thisFork>.<Container>` uniformly. No
  inheritance heuristic lives in the per-fork match arms, and the
  per-fork `Inherited.lean` files are a hand-readable ledger of
  each fork's lineage.

* **Tests/ rename.** Both `SizzLeanTests/` (was `Tests/` under
  `packages/SizzLean/`) and `LeanSha256Tests/` (was `Tests/`
  under `packages/LeanSha256/`) now carry package-prefixed
  `lean_lib` names. Lean's module namespace is flat across the
  whole build graph, so two separate `lean_lib Tests` declarations
  with `Tests.*` modules collided in the umbrella build; the
  package-prefixed names disambiguate.

**Acceptance.** `just official-ssz-vector-tests` (56-case sample)
goes from ~26 s to under half a second (~156 cases/sec vs
~2.16). `just official-ssz-vector-tests-static` (634-case
all-forks sample) from minutes to ~47 s. The `hash_tree_root`
algorithm is unchanged. The same `SSZ.serialize` /
`SSZ.hashTreeRoot Sha256` flow runs per case; only the per-case
process spawn was eliminated.

### Stage 15: Pure-Lean `Sha256Spec` + empirical FFI equivalence: **shipped**

**Status.** `Sha256Spec` lands as a kernel-reducible Lean SHA-256
implementation; empirical equivalence with the FFI is gated by a
185-case `native_decide` property test. The formal `@[csimp]`
proof is *deferred* per the analysis below.

**Deliverables shipped.**
- `LeanSha256.lean`: **standalone pure-Lean SHA-256** library
  (own `lean_lib` target, no SSZ coupling). Contains: FIPS 180-4
  §4.2.2 constants (`kConstants`, `h0Constants`); round functions
  (`ch`, `maj`, `bigSigma0/1`, `smallSigma0/1`); `messageSchedule`;
  `compressBlock`; `pad` (Merkle–Damgård); top-level `hash` and
  `combine`. Three in-file `native_decide` examples lock the spec
  against NIST §B vectors directly (empty, `"abc"`, 56-byte §B.2).
  Structural FIPS-shape lemmas: `ch_eq_fips`, `maj_eq_fips`,
  `bigSigma0/1_eq_fips`, `smallSigma0/1_eq_fips` (round functions
  match FIPS §4.1.2 forms, by `rfl`); `kConstants_size = 64` /
  `h0Constants_size = 8` plus first/last entry values (by `decide`);
  `messageSchedule_size = 64`; `compressBlock_size = 8`;
  `pad_size_multiple_of_64`; `packState_size = state.size * 4`;
  `hash_size_eq_32` and `combine_size_eq_32`. All kernel-checked
  via structural induction / `Array.foldl_induction`. Anyone
  wanting a verified Lean SHA-256 reference imports `LeanSha256`
  directly, no SSZ machinery in the dependency graph.
- `packages/SizzLean/SizzLean/Hasher/Sha256Spec.lean`: thin bridge: declares the
  `Sha256Spec` phantom tag and a single `Hasher Sha256Spec`
  instance whose methods delegate to `LeanSha256.hash` /
  `LeanSha256.combine`. About 15 lines of substance.
- `packages/SizzLean/SizzLeanTests/Sha256Equivalence.lean`: empirical
  FFI ↔ spec equivalence: 5 NIST vectors run through both
  implementations + 100 random `combine` pairs (32+32 bytes) + 80
  random `hash` inputs (10 each at lengths 0, 32, 55, 56, 64, 96,
  128, 256, covering the single-block/multi-block padding boundary).
  All 185 cases close via `native_decide`.
- `packages/LeanSha256/LeanSha256/Nist.lean` (auto-generated by
  `scripts/gen_sha256_cavp.py`): the full NIST CAVP byte-oriented
  test suite for the *spec*: 65 ShortMsg cases (Len 0–512 bits) +
  64 LongMsg cases (Len 520–51200 bits = up to 6400 bytes), each
  a `native_decide` assertion `LeanSha256.hash msg = md`. Lives in
  the `LeanSha256` library next to the implementation it validates,
  so building `LeanSha256` runs the full NIST gate. FFI ≡ NIST
  follows by transitivity (spec ≡ NIST here + FFI ≡ spec via
  `Sha256Equivalence.lean`). The .rsp files (CAVS 11.0) are
  committed under `packages/LeanSha256/cavp/` so the build stays hermetic. Monte
  Carlo (`SHA256Monte.rsp`), the chained 100×1000-hash test,
  is deferred; it would dominate the build cost without adding
  qualitatively new coverage.

**Library split (Phase 4 hygiene).** Empirical / property-test
gates moved from `packages/SizzLean/SizzLeanTests/` to a *separate*
`lean_lib SizzLeanTests` at namespace `Tests.*`.
Default `lake build` builds only the library proper (the
in-file NIST §B gates in `Hasher/Sha256Spec.lean` plus structural
lemmas stay there, they're load-bearing for the spec's
correctness at definition time). `lake build SizzLeanTests`
runs the full empirical suite (CAVP, randomised property tests,
`TreeBacked` coherence sweeps). Lets day-to-day iteration stay
fast without losing the gates.

**Deliverable deferred: formal `@[csimp]` proof.** The PLAN-as-
originally-stated proof
`@[csimp] theorem ffiSha256_eq_spec : sha256Combine = Sha256Spec.combine`
is not achievable as a strict kernel-checked equality without
changing the FFI declaration. `sha256Combine` is `@[extern] opaque`.
The kernel cannot reduce it, so extensional equality across
arbitrary inputs has no proof path other than:

* introducing an axiom (just renames the trust assumption, no
  net TCB win); or
* re-declaring `sha256Combine` as `@[extern] def` with the spec
  as body (in which case the equality becomes `rfl` and the
  `@[csimp]` rewrite reverses direction, kernel sees spec,
  runtime uses FFI via the `@[extern]` swap, which is itself a
  trust-class entry in the TCB per ARCHITECTURE.md §11 line 908).

Either path keeps a single trust line item; neither produces the
strong "kernel-checked equality" PLAN-as-originally-stated hoped
for. The empirical equivalence track captures the same trust
assumption explicitly and validates it on 185 inputs across the
input-class space. Status: deferred indefinitely (the formal-proof
budget gives more value spent on Stage 18 universal theorems per
the original timebox rationale).

**Acceptance gates met.**
- `packages/SizzLean/SizzLean/Hasher/Sha256Spec.lean` builds; three NIST `native_decide`
  examples close.
- `packages/SizzLean/SizzLeanTests/Sha256Equivalence.lean` builds; all 185
  FFI-vs-spec assertions close.
- Existing `SizzLeanTests/Sha256Vectors.lean` (FFI-only) still passes;
  no FFI behaviour changes.
- The default `Hasher Sha256` instance still routes through the FFI.
  `Sha256Spec` is opt-in via `Hasher Sha256Spec` for callers that
  want the kernel-reducible path.

**TCB framing.** The FFI assertion stays in the TCB list (this was
the documented fallback). Its *framing* tightens: the trust
assumption is now "FFI implements `Sha256Spec`'s semantics, validated
on N+ NIST + randomised inputs" rather than the bare "FFI implements
NIST SHA-256". The spec itself is Lean-kernel-checkable, which means
any downstream caller that wants a non-FFI hash path now has one
without a new trust assumption.

### Stage 16: `profile%` macro for EIP-7495: **not planned**

**Status.** Removed from the active plan. The `profile%` macro
existed to support `ProgressiveContainer(active_fields=[…])`
declarations from EIP-7495. As of consensus-spec-tests v1.5.0 *and*
the current consensus-specs `dev` head, **no fork from `phase0`
through `gloas` uses any EIP-7495 / EIP-7916 / EIP-8016 SSZ form**:

* Every container is a plain `Container`.
* No `Union`, `ProgressiveContainer`, `StableContainer`, `Profile`,
  `ProgressiveList`, `ProgressiveBitlist`, or `CompatibleUnion`
  appears in beacon-chain.md for any mainline fork.
* The matching constructors were removed from `SSZType` itself
  (see `Spec/Type.lean`'s docstring) so that the universal proofs
  in Stage 18 have a smaller surface.

If a future fork adopts `ProgressiveContainer` (e.g. a
forward-compatible `BeaconBlockBody` revision), the right move is:

1. Re-add the `progContainer` constructor to `SSZType` and its
   per-spec-function arms (`serialize`, `deserialize`, `hashTreeRoot`,
   `MaxByteLength`, `Supported`).
2. *Then* land the `profile%` macro front-end so users can declare
   such types ergonomically.

Designing the macro speculatively against an imagined consumer was
the wrong order of operations; deleting the slot until needed keeps
the implementation surface, conformance scope, and proof obligations
all minimal.

### Stage 17: Performance optimisations

Five independent perf efforts, split into sub-stages because each
has a different prerequisite, blast radius, and risk profile. Each
is benchmarked-driven. *Do not start one unless a measurement
says it's the next bottleneck.* The ordering below is the *default*
sequence (highest-impact-first per Lighthouse Milhouse and
ChainSafe), but the user can re-order based on actual profiling.

**Shared acceptance gate.** Each sub-stage's deliverable lands with
a microbenchmark in `bench/` showing the before/after numbers. The
phase-wide target is parity with fastssz on encode/decode and with
gohashtree on cached `hash_tree_root` (per ARCHITECTURE.md §2), but
no individual sub-stage carries that as its gate. Each closes when
its specific optimisation lands with a measured improvement.

**Prerequisites.** All five sub-stages assume Stage 14b/14c are
complete (a real deep tree with cached interior nodes). Without
14b, there's no tree shape for the optimisations to act on. See
the gating discussion in `Phase 4` above.

**Scope invariant: Stage 17 must not complicate the pure /
proof path.** The whole point of `SSZ.PureBox` / `UncachedSSZ`
/ plain `T` operating through `SSZ.hashTreeRoot Sha256Spec` is
that proofs about state-transition functions reduce in the Lean
kernel with no cache invariant to thread through, no FFI to
trust, and no opacity to hide behind `native_decide`. Every
optimisation below preserves that property:

* **17a, 17c, 17e** touch `TreeBacked` directly (the cached
  representation). `UncachedSSZ` has no spine to defer, no
  `Node` allocations to intern, and no serialised-form slot to
  cache, so these never reach the proof path by construction.
* **17b** plumbs a new FFI primitive used by the cache's root
  walker. It sits behind the `Hasher Sha256` instance or as an
  `@[implemented_by]` swap on `merkleRootWithCache`, not as a
  change to the abstract `Hasher` typeclass. Proof code that
  reaches for `Sha256Spec` (the pure-Lean instance) doesn't see
  the batched primitive at all.
* **17d** adds `@[specialize]` attributes to deriving-handler
  output. `@[specialize]` is a recommendation to the compiler;
  Lean's kernel still sees the unspecialised definition for
  proof reduction. `rfl` / `decide` close identically before and
  after, so the attribute is invisible on the proof path.

Concretely: a theorem about `bumpEpoch (SSZ.PureBox f0) 42`
closes by `rfl` today and must still close by `rfl` after any
or all of 17a–e land. New TCB items added by 17b stay scoped to
the cached root path; the spec-side path remains
kernel-checkable end-to-end with the same trust footprint it has
at the end of Stage 15.

#### Stage 17a: Pending-overlay with closure-based read-from-view: **shipped**

**Goal.** Accumulate pending mutations in an ordered map keyed by
gindex; commit them in one downward walk so a batch of `setField`
calls becomes one spine update per affected sub-tree instead of N
independent ones. The single largest performance lever per the
lodestar/Milhouse benchmarks.

The shipped design uses `PendingWrite T = T → Option Node`
closures rather than snapshotted sub-trees:

* Each `sszUpdate` clause emits a closure that, at commit time,
  projects the relevant sub-value out of the **current** `view`
  and builds the matching sub-tree via `Node.ofShape`.
* Closures returning `none` are dropped at commit. This mirrors
  `Array.set!`'s no-op semantics on out-of-bounds index writes.
* Reading the value from `view` at commit (rather than capturing
  at insert time) is what keeps overlapping parent/child writes
  mutually consistent: a parent's closure naturally sees every
  later child override via the shared `view`.

Together with `Node.commitAndHash` (Stage 17e), a fused commit
+ root walk that allocates each touched spine cell once with its
root computed inline, the invariant **"no `Node`-shaped work
happens until `hashTreeRoot` walks the tree"** holds.

**Deliverables.**
- `SizzLean/Cache/TreeBacked.lean`: `def PendingWrite T := T → Option Node`,
  `pending : Std.TreeMap Nat (PendingWrite T)` field on
  `TreeBacked`, plus `addPending` / `addPendingMany` /
  `hashTreeRootCached` (consults `pending` first; survivors feed
  `Node.commitAndHash`).
- `SizzLean/Cache/Update.lean`: cached `sszUpdate` emission emits
  the `T → Option Node` closure; index steps get a bounds check
  that short-circuits to `none` when the runtime index is out of
  range.
- `SizzLean/Repr/Instances.lean`: a faithful `GetElem (SSZList α cap)
  Nat α` instance (validity `i < xs.size`) plus the `.size` /
  `.toArray` / `.foldl` / `.map` / … element surface, so `xs[i]!`,
  `xs[i]?`, and `xs.size` work uniformly across `Vector` and
  `SSZList` inside the projection chain and in spec bodies.
- Regression tests covering the bug classes the design closes:
  - `SizzLeanTests/PendingPrefixConflict.lean`: parent/child
    gindex prefix relations (5 cases).
  - `SizzLeanTests/PendingListShrink.lean`: list-shrink + stale
    index writes (8 cases, including a non-zero-`Inhabited` element
    case that surfaces the bounds-check requirement).
  - `SizzLeanTests/WidthsAndLists.lean`: 32 cases covering basic
    widths (Bool, UInt8/16/32/64, BitVec 128/256) × list-size
    changes (empty / one / grow / cap-full / shrink).

#### Stage 17b: Batched SHA-256

This sub-stage now splits into three pieces of work tracked
separately. The split is structural: the FFI primitive shipped
in 17b.0; the SIMD shim (17b.1) is what makes the primitive
actually fast; the rank-frontier batched walker (17b.2) is what
exposes the win through the user interface.

##### Stage 17b.0: FFI primitive + Lean wrapper + axiom: **shipped**

**What's in the library.** `csrc/sha256_batch.c` (scalar EVP
loop), `SizzLean/Hasher/Sha256Batch.lean` (`@[extern] opaque
sha256BatchCombine : @& Array ByteArray → @& Array ByteArray →
Array ByteArray`), named axiom `sha256BatchCombine_eq_spec`,
empirical-equivalence test in `SizzLeanTests/Sha256BatchEquivalence.lean`
(7 cases including empty / single / 8-pair). The Lean-side FFI
surface is final. 17b.1 and 17b.2 swap implementations behind
it without changing the signature.

**Measured result.** Scalar-EVP batched ≈ scalar-EVP loop (~40
µs / 128 pairs), within noise. The shared-`EVP_MD_CTX`
amortisation we ship saves ~10 ns / pair; the compression
itself is ~300 ns / pair. The math doesn't move until the
compression itself is vectorised. **That's 17b.1's job.**

##### Stage 17b.1: Cross-platform SIMD shim: **not done**

**Goal.** Replace the scalar EVP loop in `csrc/sha256_batch.c`
with a per-architecture dispatch that uses real SIMD/hardware
SHA where available. Single shim, one library per architecture:

* **x86_64 (Intel + AMD)**: link **Intel ISA-L** (BSD-3-Clause,
  Intel-maintained, ships in Debian/Ubuntu / RHEL / Alpine as
  `libisal-crypto-dev`). Its `sha256_mb` API hashes 4 (SSE) / 8
  (AVX2) / 16 (AVX-512) buffers in parallel, auto-dispatched
  via CPUID at runtime. Works identically on AMD CPUs that
  support the same SIMD ISA (Zen 1+ for AVX2, Zen 4+ for
  AVX-512).
* **ARM64 (Apple Silicon, AWS Graviton, ARM servers)**: fall
  back to **OpenSSL** (already in our link line). OpenSSL's
  EVP path uses ARMv8 SHA-Ext on supported CPUs (every Apple
  M-series chip, Graviton 3+, etc.). Each single-pair hash is
  already ~30–50 ns. The "batched" path on ARM is a tight loop
  over fast single-pair calls; the function-call amortisation
  is the win, ~1.5×, not the 8–16× of x86 SIMD.
* **Fallback** (older ARM without SHA-Ext, RISC-V, etc.):
  OpenSSL EVP loop. Same code path as the ARM64 case.

**File layout** (no new Lean files; just C + lakefile):

```c
// csrc/sha256_batch.c
#if defined(__x86_64__) || defined(_M_X64)
  #include <isa-l_crypto/sha256_mb.h>
  // ISA-L multi-buffer impl: submit N pairs to the ctx manager,
  // flush, collect digests
#else
  // OpenSSL EVP loop — hardware-SHA on ARMv8 SHA-Ext CPUs
#endif
```

`lakefile.lean`: conditionally append `-lisal_crypto` to
`moreLinkArgs` when the target triple starts with `x86_64`.

**Measured-after target** (per the existing
`Sha256BatchEquivalence` fixture, 128 pairs):

| Architecture | Expected `sha256BatchCombine` (128 pairs) | Speedup over scalar |
|---|---|---|
| x86_64 with AVX-512 | ~3 µs | ~13× |
| x86_64 with AVX2 | ~5 µs | ~8× |
| x86_64 with SSE4.2 + SHA-NI | ~10 µs | ~4× |
| ARM64 with ARMv8 SHA-Ext | ~25–30 µs | ~1.5× (amortisation only) |
| ARM64 / other without hardware SHA | ~40 µs | 1× (no change) |

**Risk.** Low–medium. ISA-L is mature; the failure modes are
build-system (linking on macOS-arm64 where ISA-L isn't
available, handled by the `#if`-arch dispatch).

**Trust footprint.** No change. The named axiom
`sha256BatchCombine_eq_spec` continues to assert pointwise
agreement with the pure-Lean reference; the equivalence test
re-runs identically.

##### Stage 17b.2: Rank-frontier batched walker in Lean: **not done; depends on 17b.1**

**Goal.** Feed the now-fast batched primitive from the cache's
root walk. The walk batches every sibling pair that becomes ready
at the same moment, wherever it sits in the tree, and issues one
`sha256BatchCombine` per group. Geometric "one batch per tree
level" is the special case for a single perfect binary tree;
SizzLean's trees are not always that shape, so the walker batches
by *readiness rank* instead.

**Readiness is already in the node type.** The `pair`'s
`Option ByteArray` cache slot is both the dirty bit (`none` =
needs recompute) and the readiness flag (`some` = computed,
`Node.cached` reads it in O(1)). A `pair l r none` is ready the
moment both children are `some`. `setManyAt` confines the `none`
cells to the touched spines, so the walk descends only the dirty
region and prunes resolved branches in O(1) via `Node.rootOf`.
Rank is the height of a pair's tallest unresolved input
(`rank = 1 + max` over children, cached children counting 0), so
pairs of equal rank are mutually independent and form one batch.
Rank equals geometric level on a perfect tree, and merges ready
pairs across subtrees of differing heights on a heterogeneous or
sparsely-dirtied one, which packs the SIMD lanes fuller.

**Deliverable.**
- `SizzLean/Cache/MerkleTree/MerkleBatch.lean`: a
  `commitAndHash`-shaped walk in three phases. (1) One post-order
  descent that hashes nothing and records each `pair _ _ none` as
  `(id, leftSource, rightSource, rank)`, sources being either a
  cached digest or another pair's id, bucketed by rank. (2) Flush
  rank `0, 1, …, maxRank`, one `sha256BatchCombine` per bucket,
  writing digests into an id-indexed results array. (3) Rebuild
  the tree, threading roots back into the `none` slots. Wired as
  the cached-Box path's default walk (or `@[implemented_by]` on
  `merkleRootWithCache` when the signatures match).

After this lands, the scenarios bench's `S1`/`S3`/`S4`/`S6`
ValidatorSet rows should drop on x86 with AVX-512 (approx 3–5×
faster cached column), modestly on ARM (~1.5×).

**Risk.** Medium. Schedule-collect and rebuild are mechanical on
an immutable tree (results route through the id-indexed array
since slots cannot be flipped in place mid-wave). The design
lever is batch fullness: rank bucketing already merges across
subtrees, leaving only the small-tree top ranks underfilled. A
lane-width threshold hashes sub-`N` ranks with scalar `combine`
and reserves `sha256BatchCombine` for the wide ranks; 17b.1 owns
where that threshold sits, 17b.2 owns producing buckets big
enough to clear it. Reference: `gohashtree`'s `HashChunks` shape.

**Dependency on 17b.1.** Without the SIMD shim, integrating
this delivers zero measurable improvement on the scenarios
bench (the bench data on the scalar shim confirmed this: FFI
batched ≈ FFI scalar at ~40 µs / 128 pairs). 17b.2 is only
worth doing once 17b.1 ships.

**Dependency on Stage 15.** The batched primitive needs a
parallel `@[csimp]` proof (or stays in the TCB behind its own
assertion). The honest answer is the latter. The batched
primitive is a performance shim, not part of the verified
core. Same Stage 15 follow-up as the scalar axioms.

#### Stage 17c: Hash-consing (bounded-LRU): **library primitive shipped; not on user interface**

**Goal.** Dedupe identical populated subtrees across the tree (and
across multiple `TreeBacked` values) via a weak `HashMap (Hash32)
Node`, complementing `ZERO_HASHES`'s zero-subtree deduplication.

**Deliverables (shipped as library primitives, not wired into the cached path).**
- `SizzLean/MerkleTree/HashCons.lean`: per-thread bounded-LRU
  cache; `Node.mkPair : Node → Node → Option ByteArray → Node`
  smart constructor that interns identical subtrees.
- *(Not yet)* `Node.merkleRootWithCache` calling `Node.mkPair`
  at cache-fill sites. Integration is gated on workload evidence.

**Default-OFF when integrated.** When this is eventually wired
into the default cached path (i.e. into `box.hashTreeRoot`'s
`merkleRootWithCache` walk so the user no longer has to know
about consing), the **default configuration must keep consing
off**, with an explicit `Box`-construction opt-in for workloads
that benefit (multi-tree archival, gossip aggregation across
many similar blocks). Reason: the standing micro-bench on the
scenarios fixture set showed consing slowed the typical
ValidatorSet root by ~9× per call (cache-lookup overhead per
pair × no inter-tree subtree redundancy in the workload).
Defaulting it on would regress every non-archival scenario; the
inversion-of-control fix is opt-in at `SSZ.FastBox` construction,
e.g. `SSZ.FastBox v (consing := true)`, so a `SSZ.FastBox v`
call retains the current (consing-off) behaviour.

**Risk.** Medium. Lean's runtime reference-counting interacts with
weak references non-trivially; getting the lifecycle right needs
care. The default-OFF stance lowers the cost of getting this
imperfect on first integration. Pathological workloads can be
moved off the opt-in flag without affecting everyone else.

#### Stage 17d: Profiling-guided `@[specialize]`: **shipped**

**Goal.** Monomorphize the `SSZType`-driven generic interpreter at
the concrete consensus types that dominate the profile. Each
specialization removes one level of dispatch overhead.

**Deliverables.**
- `@[specialize]` annotations on the generic functions surfaced by
  the deriving handler (in `packages/SizzLean/SizzLean/Repr/Deriving.lean`).
- Hot-path consensus types (`Validator`, `BeaconBlockHeader`,
  `BeaconState`'s per-fork variants) get `@[specialize]
  serialize`-style hints.
- A microbenchmark showing the specialization win on at least one
  type.

**Risk.** Low. `@[specialize]` is a recommendation to the compiler;
worst case it's ignored.

#### Stage 17e: Fused commit walk + pre-cached builders: **shipped**

**Goal.** Eliminate the two-walk commit pattern (apply pending
writes, then walk to fill cache slots) by fusing both into a
single spine walk; and make `Node.ofShape`'s builders produce
pre-cached pairs so a subsequent root read can short-circuit at
the top in O(1).

**Deliverables.**
- `SizzLean/Cache/MerkleTree/SetAt.lean`: `Node.commitAndHash`:
  one walk over the touched spine, each cell allocated once with
  its root computed inline. Replaces the two-pass
  `setManyAt` → `merkleRootWithCache` sequence at commit time.
- `SizzLean/Cache/MerkleTree/Build.lean`: `Node.ofSubtrees`,
  `Node.mixInLength` embed `(some root)` in the parent pair at
  construction (root computed via `Node.rootOf` on the children,
  which is O(1) when the child is already cached).
- `SizzLean/Cache/MerkleTree/Zero.lean`: `Node.ofLeaves` mirrors
  the same pre-cached-pair pattern.
- `Node.rootOf` (in `Zero.lean`): cheap root lookup used by the
  pre-cached builders; O(1) on cached pairs, recursive on
  uncached.

**Risk.** Low. The fusion changes allocation patterns but is
behaviourally equivalent, verified by the existing
`TreeBackedCoherence` and `PendingOverlayCoherence` test suites
plus a fresh `WidthsAndLists` coverage net.

---

## Phase 5: Complete formal verification

The closing phase. Widens the three central theorems from the
Stage 5–6 first cut (`BasicSupported`) to full coverage over
`SSZType.Supported` / `SupportedBounded`, landing the publishable
non-malleability artefact described in ARCHITECTURE.md §4.

Positioned last on purpose. Phase 3 conformance establishes the
implementation is correct against the spec; Phase 4 ships the
performance layer; only then does Phase 5 invest in the
research-grade Lean proof effort. Proving a wrong implementation
correct is the most expensive failure mode in this project, so
conformance pays the empirical-validation tax first.

### Stage 18: Complete the three central theorems: **in progress**

**Goal.** Close the publishable correctness story: `decode_encode`,
`serialize_injective`, and `encode_size_le_max` universally over all
implemented arms (i.e. `SSZType.Supported` /
`SSZType.SupportedBounded`, defined in `Spec/Supported.lean`).
Replaces the Stage 5–6 first-cut theorems on `BasicSupported`.

**Current coverage (shipped).**

| Arm | Status | Proof file |
|---|---|---|
| `.uintN 8 / 16 / 32 / 64` | ✅ | `Proofs/UInt.lean` |
| `.bool` | ✅ | `Proofs/Bool.lean` |
| `.vector t n` (general, `0 < n`, fixed-size `t`) | ✅ | `Proofs/VectorFixed.lean` |
| `.list t cap` (general, fixed-size `t`, `0 < t.fixedByteSize`) | ✅ | `Proofs/ListFixed.lean` |
| `.container fs` (general, `BasicSupportedFieldsFixed fs`) | ✅ | `Proofs/ContainerFixed.lean` (helpers) + `Proofs/Roundtrip.lean` (mutual block) |
| `.bitvector n` (`0 < n`) | ⏸ deferred | needs `packBitsLE` / `unpackBitsLEAux` inverse |
| `.bitlist cap` | ⏸ deferred | needs bit-packing inverse + `msbPos` delimiter recovery |
| mixed-field `.container` (≥1 variable-size field) | ⏸ outside `Supported` | needs `Supported` extension first |

Shared prerequisite shipped: `Proofs/SerializeSize.lean`, the
`size_serialize_eq_fixedByteSize` mutual proof over
`(BasicSupported, BasicSupportedFieldsFixed)`. This is *the*
prerequisite the composite arms recurse through and is reused by
the three theorems' composite-arm dispatch.

**Remaining deliverables.**
- `packages/SizzLean/SizzLean/Proofs/BitPack.lean` (planned):
  `packBitsLE` / `unpackBitsLEAux` inverse lemma. The per-byte
  inverse `byteToBits (bitsToByte [b₀..b₇] 0 0) = [b₀..b₇]` closes
  via 256-case `cases <;> decide` in ~2 s; the full byte-stream
  inverse is ~200–400 lines due to the 8-bit-vs-1-byte recursion
  mismatch.
- `packages/SizzLean/SizzLean/Proofs/BitVector.lean` (planned):
  `.bitvector n` arm; depends on BitPack.
- `packages/SizzLean/SizzLean/Proofs/BitList.lean` (planned):
  `.bitlist cap` arm with `msbPos` delimiter recovery; depends
  on BitPack.
- Spec-layer extension for mixed-field containers (out of scope
  for Stage 18 as currently scoped; it would require a new
  `containerVar` constructor on `Supported` plus offset-table
  invariants).
- The `SSZ.roundtrip` user-surface corollary loses its
  `BasicSupported r.shape` precondition once the bit-level arms
  close (mixed-field containers are blocked one layer deeper, on
  the `Supported` predicate itself).

**Final acceptance.** Three theorems closed universally over
`Supported` / `SupportedBounded` with no `sorry`, no `native_decide`
on the proof path. The current shipping cut closes everything
*except* `bitvector`, `bitlist`, and mixed-field containers;
`decode_encode`'s axiom footprint is exactly three
`_native.bv_decide.ax_*` axioms (from the multi-byte `uintN`
arms) plus the standard kernel axioms, and `encode_size_le_max`
adds none. Note that the bv_decide axioms are a documented
deviation from the original Stage 18 acceptance and could be
removed by replacing `bv_decide` with hand-written `BitVec`
proofs (substantially more code).

**Risk.** Lowered from the original "highest in project" since
the composite arms (general `vector` / `list` / `container`) are
now shipped without the predicted research-grade difficulty.
The mutual-block trick on `(BasicSupported,
BasicSupportedFieldsFixed)` resolved the closure-termination
issue cleanly. Remaining risk concentrates in `bitlist`
(`msbPos` delimiter recovery is genuinely intricate) and in any
future mixed-field-container work.

**Notes.** Each arm's arrival extends `SSZ.roundtrip`
automatically; downstream Eth-types instances pick up the wider
corollary without rework. The README's
[Proof coverage](../README.md#proof-coverage) section carries
the per-constructor table users see.

---

## Cross-cutting concerns (apply to every stage)

- **Literate by default** (CLAUDE.md). Every new `*.lean` file opens
  with a `/-! … -/` module docstring framing it for both
  Lean-fluent and SSZ-fluent readers; every public declaration carries
  a `/--` *why*-docstring; each user-facing API gets an `example` block.
- **No `sorry` in committed code.** A `TODO` plus a tracking note is
  acceptable for a single-commit work-in-progress; CI should reject
  `sorry` on `main`.
- **`set_option autoImplicit false` per file.**
- **Strict structural recursion.** No `partial def` unless termination
  genuinely cannot be shown; prefer `termination_by` + `decreasing_by`.
- **No committed `#eval` / `#check` / `#print`.** Use
  `example : … := by …` or `#guard` for build-time assertions.

## Status snapshot

| Phase | Stages | Status |
| --- | --- | --- |
| 0: Bootstrap | Stage 0 | complete |
| 1: Spec foundation | Stages 1–6 | complete (proof scaffolding lands here; the `BasicSupported` predicate has since widened, see the Stage 18 row) |
| 2: User surface | Stages 7–9 | complete |
| 3: Application + empirical validation | Stages 10–11, **11.1** | **complete.** `ssz_generic`: **1865/1865 cases pass**. `ssz_static` (minimal preset, full `--all` sweep): **38991/38991 cases pass** across all seven mainline forks (`phase0`, `altair`, `bellatrix`, `capella`, `deneb`, `electra`, `fulu`), zero failures, zero skipped. Conformance pinned at consensus-spec-tests **v1.6.0-beta.0** in `scripts/run_conformance.py` so the Fulu / Gloas containers track the post-v1.5.0 main-branch spec (Fulu BeaconState is now its own struct with `proposer_lookahead`; Gloas BeaconState is its own struct with the nine EIP-7732 ePBS fields). Preset duplication is eliminated by the `ssz_struct_for_presets` macro (`packages/LeanEthCS/LeanEthCS/PresetStruct.lean`); preset-sensitive containers are written once with `@@CONST` / `@%TypeName` placeholders and emitted twice (`.Minimal` / `.Mainnet`). Mainnet validated at `--limit 2` across all forks (1641/1641); mainnet `--all` is a `workflow_dispatch` button. CLI dispatch uses the `<preset>/<fork>:<type>` identifier scheme (legacy `<fork>:<type>` defaults to minimal). **CI integration**: `.github/workflows/lean_action_ci.yml` runs the conformance script at `--limit 1` on every push/PR. **Stage 11.1, harness modernisation:** `eth_ssz_vector_runner batch` mode (one process spawn per sweep, tab-separated request/response over stdin/stdout, ~70× speedup on `ssz_generic`); `tqdm` progress bar; per-fork explicit `Inherited.lean` re-exports in LeanEthCS killing the inheritance heuristic in the dispatcher; Tests/ rename to package-prefixed `SizzLeanTests/` / `LeanSha256Tests/` for umbrella-build namespace disambiguation. EIP-7441 (Whisk) deferred per scope; EIP-7732 (ePBS) Gloas containers tracked (BeaconState shape implemented; supporting types `Builder`, `BuilderPendingPayment`, `BuilderPendingWithdrawal`, and `ExecutionPayloadBid` ship in `Forks/Gloas/`). |
| 4: Production primitives + deferred hardening | Stages 12, 13, 14a–d, **14e**, 15, 17a–e (Stage 16 dropped, see note) | **Cache backbone + ergonomic surface + Sha256Spec green: 14a–e + 15 in.** Stage 12: three hand-built trees match `Spec.SSZType.hashTreeRoot` via `native_decide`. Stage 13: 200-case randomized property test (`gindexBits` on `List Bool` so the Nimbus Feb-2025 gindex bug class is unrepresentable). Stage 14a: `TreeBacked` scaffold. Stage 14b: `Node.ofShape` produces interior-populated trees byte-identical to the spec; coherence verified on 8 composite types. Stage 14c: cached `setField` operations; property tests pass for 100 + 30 mutations. Stage 14d: `Node.setManyAt` batched walker (100-case property test on disjoint distinct paths) plus `sszUpdate t with f := v, g.h := w, vec[i] := x` term-elaborated syntax (50-case flat-multi + 20-case nested-path + 30-case vector-index + 30-case alias-coverage gates). Index syntax handles both `Vector` and `SSZList` with composite element types; the list path emits the `[false]` mix-in-length prefix automatically. `TreeBacked H T` / `CachedSSZ H T` pin the hasher in the *type*, picked once at `TreeBacked.ofValue` time, then inferred by every downstream `sszUpdate` / `hashTreeRootCached` call; mixing hashers within one cached value is a type error. Two exploratory pieces were tried and removed: a `derive_tree_setters` macro and `TreeBacked/Container.lean` (hand-written setters obsoleted by `sszUpdate`'s index syntax). **Stage 14e, `SSZ.Box` union + curated public surface:** closed inductive over the two cache flavours with four smart constructors (`SSZ.FastBox` / `SSZ.PureBox` Sha256-pinned, `SSZ.CachedBox` / `SSZ.UncachedBox` hasher-explicit); `sszUpdate` extended with two-arm box dispatch; read-side `sszGet b a.b[i].c` macro mirrors `sszUpdate`'s path syntax and expands to `b.view.a.b[i].c` so user code never types `.view`; `CachedSSZ.ofValue` / `.hashTreeRoot` user-facing aliases. Stage 15: pure-Lean `Sha256Spec` ships as a kernel-reducible Lean SHA-256 implementation, validated empirically against the FFI on 185 cases (5 NIST + 100 random combine + 80 random hash). **Stage 17a (pending overlay):** `pending : Std.TreeMap Nat (PendingWrite T)` where `PendingWrite T = T → Option Node` is a closure that reads the current `view` at commit time and returns `none` for view-side no-op writes (OOB index updates). Cross-statement batching is automatic and free; closure-based read-from-view keeps overlapping parent/child writes mutually consistent. **Stage 17b:** batched SHA-256 FFI primitive (`sha256BatchCombine`) shipped with named axiom and equivalence tests; scalar inner loop in `csrc/sha256_batch.c` for now (AVX-512 swap is 17b.1 follow-up, keeps the FFI surface identical). **Stage 17c:** bounded-LRU hash-consing primitive (`Node.mkPair`) shipped opt-in; default cached path bypasses it. **Stage 17d:** `@[specialize]` on the three `SSZ.serialize/deserialize/hashTreeRoot` surfaces. **Stage 17e:** `Node.commitAndHash` fuses commit + root walk into a single spine walk; `Node.ofShape`'s builders (`ofLeaves`, `ofSubtrees`, `mixInLength`) pre-fill `(some root)` cache slots at construction so `merkleRootWithCache` on a fresh subtree short-circuits in O(1) at the top. **Bench (`packages/SizzLean/SizzLeanBench/`, run via `just bench`):** seven scenarios S1–S7 across small (`Validator` / `ValidatorSet16`), large (`ValidatorSet256`), and realistic (`SizzLeanBench.Fulu.BeaconState`, mainnet preset, ~1024 validators) fixtures. Headline rows: **S6 BlockProcessingLarge** ~2.4× cached vs pure; **S7 FuluStateTransition** ~2.0× cached vs pure. S7's Fulu types live in `SizzLeanBench/Fulu.lean` as a bench-local reference copy so `SizzLeanBench` doesn't need a LeanEthCS dependency (`LeanEthCS` already depends on `SizzLean`, so the reverse would close a cycle). |
| 5: Complete formal verification | Stage 18 | **in progress.** `BasicSupported` now covers `uintN 8 / 16 / 32 / 64`, `bool`, general `vector` / `list` over fixed-size elements, and general `container` over fixed-size fields (recursively). Shared prereq `Proofs/SerializeSize.lean` lands the `size_serialize_eq_fixedByteSize` mutual proof. Per-arm proofs split across `Proofs/{UInt,Bool,VectorFixed,ListFixed,ContainerFixed,FixedElems,Roundtrip,SizeBound}.lean`; `decode_encode`'s axiom footprint is three `_native.bv_decide.ax_*` (uintN16/32/64), `encode_size_le_max`'s is zero non-standard axioms. Open arms: `bitvector`, `bitlist` (need `packBitsLE` / `unpackBitsLEAux` inverse). Mixed-field containers remain outside `SSZType.Supported` itself, separate spec-layer work. See the Stage 18 section above and the README's *Proof coverage* table. |
