# Building a verified SSZ library in Lean 4

**Build the SSZ library as a deeply-embedded "universe of descriptions" plus a small `SSZRepr` typeclass derived per user type, prove roundtrip and non-malleability once on the universe, and FFI only SHA-256 to a verified C primitive.** This architecture gives you formal correctness for free on every consensus type (BeaconState, BeaconBlock, ProgressiveContainer profiles) without per-type proofs, while keeping a viable production performance trajectory within 2–5× of fastssz on encode/decode and at parity on cached `hash_tree_root`. The closest existing artefact in the wild is **ConsenSys's `eth2.0-dafny`** (TACAS '22), which already proved `deserialise ∘ serialise = id` for the Phase-0 SSZ subset; the closest Lean-shaped methodology is **Microsoft Research's EverParse/LowParse**, whose three-layer (spec / functional / low-level) architecture and non-malleability theorem statement should be lifted essentially verbatim. **No public Lean 4 SSZ library exists today**, including in the EF, PSE, and Verified-zkEVM orgs, so this is greenfield work, but the surrounding Lean 4 ecosystem (`Lean.Json`'s deriving handler, `lean4-json-schema`'s proof-carrying derivations, `bv_decide`, `BitVec`, `tydeu/lean4-alloy`, `argumentcomputer/Blake3.lean`) supplies every primitive you need.

The rest of this report is organised as the user requested: a precise SSZ spec recap, the Lean 4 deriving toolbox, three concrete design approaches with code, the verification strategy, the production/FFI angle, a prior-art catalogue, and a final recommendation.

## 1. The SSZ spec, made formalization-ready

SSZ has six basic shapes that drive every formalization choice: **`uintN` (8/16/32/64/128/256, little-endian)**, **`boolean` (1 byte, only `0x00`/`0x01`)**, the four composites **`Vector[T,N]`**, **`List[T,N]`**, **`Bitvector[N]`**, **`Bitlist[N]`**, plus **`Container`** and **`Union[T0,…]`**. Variability is recursive: a `Container` is variable-size iff any field is, a `Vector[T,N]` iff `T` is, while `List`, `Bitlist`, and `Union` are always variable. Constants `BYTES_PER_CHUNK = 32` and `BYTES_PER_LENGTH_OFFSET = 4` govern the entire wire format.

The serialisation algorithm for any composite is a single procedure: split children into a fixed region and a variable region, replace each variable child with a **little-endian `uint32` offset** into the variable region, and concatenate. The first variable child's offset value equals the size of the fixed region; every subsequent offset is monotonically non-decreasing. Total serialised size must be `< 2^32`. **Bitlist** alone has a wrinkle: the trailing delimiter bit at position `len(value)` marks the end and is stripped during Merkleization. Empty edge cases matter for verification: an empty `List[T,N]` of variable T is `b""`, not a 4-byte offset; an empty `Bitlist` is `0x01`, not empty.

Merkleization is a separate fold. Basic types and small fixed-width children pack into 32-byte chunks (`pack`); composites use each child's `hash_tree_root` as a leaf. Then `merkleize(chunks, limit)` pads to `next_pow_of_two(limit)` zero-chunks and folds with SHA-256 pairwise. **Lists, Bitlists, and Unions add a top-level mix-in**: `mix_in_length` for List/Bitlist (hash of root concatenated with the 32-byte little-endian length), `mix_in_selector` for Union (selector right-padded to 32 bytes). The implementation almost universally uses a precomputed `ZERO_HASHES[d]` table (depth typically ≤ 64 for `validators: List[Validator, 2**40]`).

### Recent additions matter and the EIP-7495 dual identity is a trap

**EIP-7495 was renamed in 2025 from "StableContainer" to "ProgressiveContainer", and the wire format changed.** The current EIP-7495 `ProgressiveContainer(active_fields=[1,0,1,…])` serializes *identically* to a regular Container (`active_fields` is a type-level constant, not on the wire) and merkleizes via the **progressive Merkle tree** of EIP-7916 (shelves of size 1, 4, 16, 64, …, giving stable generalized indices independent of total length). The **legacy** "StableContainer[N]" form, still used by EIP-6493 (SSZ transactions), EIP-6404, EIP-6466, and shipping in `protolambda/remerkleable`, `paulmillr/micro-eth-signer`, and Lodestar, prepends a `Bitvector[N]` of active fields on the wire and uses `merkleize_with_limit=N` plus `mix_in_active_fields`. **A formalization must encode both as separate `SSZType` constructors**; whichever flavour the consensus and execution forks pick, a verifier needs both. EIP-7916 adds `ProgressiveList[T]` and `ProgressiveBitlist`; EIP-8016 adds `CompatibleUnion({selector: T})` with selectors restricted to `1..127`.

Among reference implementations, **`protolambda/remerkleable` is the spec-cited oracle** and the cleanest model: it represents every value as a typed view over a persistent binary Merkle tree of `Node`s, automatically caching `hash_tree_root` per node and forking the tree on mutation. **`ralexstokes/ssz_rs` is the cleanest typeclass-shaped model** for Lean 4 because its `Serialize`/`Deserialize`/`HashTreeRoot`/`Sized` trait split maps directly onto a Lean `class SSZ`. **`ferranbt/fastssz` is the production performance benchmark** but uses Go codegen, which is the wrong template for a verified Lean library. **Use the `ssz_generic` test vectors in `consensus-spec-tests`** as your conformance oracle; `lambdaclass/libssz` already validates against 62,489 of these and is the cleanest unverified Rust reference.

## 2. Lean 4's deriving toolbox in technical detail

Lean 4 exposes a single, simple registration API in `src/Lean/Elab/Deriving/Basic.lean`:

```lean
def DerivingHandler := Array Name → CommandElabM Bool
def registerDerivingHandler (className : Name) (handler : DerivingHandler) : IO Unit
```

A handler receives the names of all inductives in a `mutual` block (or all types listed in `deriving instance Foo for A, B`), returns `true` if it claims the class, and is expected to call `elabCommand` to inject generated `instance` syntax into the environment. Multiple handlers may register for the same class; they are tried newest-first until one returns `true`.

The supporting library at `Lean.Elab.Deriving.Util` provides the entire scaffolding:

- **`mkContext "ssz" name : TermElabM Context`** discovers the mutual group, picks fresh aux-function names, and decides whether the recursion needs `partial`.
- **`mkHeader ``SSZ 1 indVal : TermElabM Header`** builds the auxiliary function's signature with implicit type parameters, instance-implicit constraints (`[SSZ α]`), and the value argument.
- **`mkLocalInstanceLetDecls`** materialises `let inst : SSZ Other := ⟨serOther⟩` so mutual recursion type-checks via instance synthesis instead of direct calls. This is the pattern `FromToJson` uses and the right one to copy for SSZ.
- **`mkInstanceCmds`** emits the final `instance : SSZ T := ⟨serT, deserT, htrT⟩` syntax.

The canonical study-template is **`src/Lean/Elab/Deriving/Repr.lean`** (137 lines, fully verified). It demonstrates exactly the dispatch you need for SSZ: walk each constructor's fields with `forallTelescopeReducing ctorInfo.type`, skip type-level and proof-level fields with `if ← isType x <||> isProof x then ...`, recurse on same-type fields by calling the local aux function, and defer to the field's own typeclass instance for everything else. **`Lean.Elab.Deriving.FromToJson` is the secondary template** because it shows the encode+decode pair pattern: each pair member has its own header builder and body builder, both registered as separate handlers for `ToJson` and `FromJson`. SSZ has three operations (serialize, deserialize, hashTreeRoot) and should follow the FromToJson layout: three body builders, three mutual blocks of aux functions, one combined `instance` command at the end.

For type introspection, `Lean.Meta` provides `getConstInfoInduct`, `getConstInfoCtor`, `getStructureInfo?`, and `getStructureFields`, and `Lean.Expr.isAppOf`, `getAppArgs`, `whnf` let you recognise `Vector α n`, `Subtype p`, or `BitVec n` in field types and dispatch accordingly. **`synthInstance? (mkAppN (mkConst ``SSZ) #[τ])`** lets the handler check whether a field type already has an SSZ instance and emit a precise error otherwise.

The community ecosystem has fewer examples than you might hope. **Mathlib's `deriving Fintype` and `deriving ToExpr`** are the most sophisticated existing handlers and demonstrate universe polymorphism and dependent indices. **`predictablemachines/lean4-json-schema`** (announced 2025) is the closest analogue to what you want for SSZ: its handler emits both a `HasJSONSchema` instance *and* a compile-time proof `ValidatesAgainstSchema`. **No CBOR, msgpack, or protobuf deriving with proofs exists in the Lean 4 ecosystem as of May 2026**. `zygi/lean-protoc-plugin` ships unproven `ProtoSerialize`/`ProtoDeserialize` typeclasses and is the closest binary precedent.

For ergonomics on subtype-style SSZ types, prefer the structure form over the bare subtype:

```lean
structure SSZ.List (α : Type) (capacity : Nat) where
  data  : List α
  bound : data.length ≤ capacity
```

This makes `getStructureFields` work, lets the deriving handler skip `bound` automatically (it's a `Prop`), and supports `match xs with | ⟨[a,b,c], _⟩ => ...`. Add `instance : GetElem (SSZ.List α n) Nat α (fun xs i => i < xs.data.length)` for `xs[i]` syntax, plus a `ssz![1,2,3]` macro that elaborates to `⟨[1,2,3], by decide⟩` for ergonomic literals. Lean core's `Vector α n` (since 4.10+) is already a structure with a proof field and indexing instance and should be reused directly for SSZ vectors.

## 3. Three concrete design sketches

The three approaches stand in a layered relationship. **A and B are alternative implementation strategies**: A generates per-type imperative encoder/decoder code with the same effect as fastssz's `sszgen`; B reflects the SSZ grammar as data and writes a single generic interpreter, with user types connecting via a typeclass instance. **C is purely syntactic sugar on top of B**, a macro-level surface syntax for cases where vanilla Lean `structure` declarations don't carry enough information. Under the hood, C lowers to B. Approach B alone, without any C macro, is already a complete, ergonomic user-facing design; C is an optional extension for EIP-7495 ProgressiveContainer profiles and similar features that don't fit cleanly into Lean structures.

### Approach A: a `deriving SSZ` handler emitting per-type code

Define the typeclass once:

```lean
class SSZ (α : Type) where
  serialize    : α → ByteArray
  deserialize  : ByteArray → Except SSZError (α × Nat)
  hashTreeRoot : α → ByteArray  -- 32 bytes
  isFixedSize  : Bool
  fixedSize?   : Option Nat
```

The handler walks each structure's fields, partitions them into fixed and variable, emits a `serialize` body that builds the fixed region and offset table then concatenates the variable region (a direct translation of the SSZ algorithm), and emits a symmetric `deserialize` that parses offsets and reconstructs fields. Following Repr's template the skeleton is:

```lean
def deriveSSZ (declNames : Array Name) : CommandElabM Bool := do
  if !(← declNames.allM isInductive) then return false
  for n in declNames do
    let cmds ← liftTermElabM <| mkSSZCmds n
    cmds.forM elabCommand
  return true
initialize registerDerivingHandler ``SSZ deriveSSZ
```

with `mkSSZCmds` building three mutual-block aux functions (`serializeT`, `deserializeT`, `hashTreeRootT`) and one combined instance. **The advantage is monomorphic, branch-free generated code**, comparable to fastssz's `sszgen`. **The disadvantage is verification cost**: each derived instance ships its own `roundtrip` lemma that the handler must either prove via tactics at elaboration time (slow, fragile) or trust (TCB grows with every consensus type). For BeaconState and friends this scales poorly. **Use this approach only as a performance-tuned alternative to Approach B, derived from the same `SSZType` description and proved equivalent.**

### Approach B: a universe of SSZ descriptions (recommended)

Reflect the SSZ grammar into Lean as data:

```lean
inductive SSZType where
  | uintN          : (bits : Nat) → SSZType         -- bits ∈ {8,16,32,64,128,256}
  | bool           :                  SSZType
  | vector         : SSZType → Nat  → SSZType
  | list           : SSZType → Nat  → SSZType
  | bitvector      : Nat            → SSZType
  | bitlist        : Nat            → SSZType
  | container      : List SSZType   → SSZType
  | union          : List SSZType   → SSZType
  | progContainer  : List Bool → List SSZType → SSZType        -- EIP-7495 current
  | stableContainer: Nat → List (Option SSZType) → SSZType     -- EIP-7495 legacy
  | progList       : SSZType        → SSZType                  -- EIP-7916
  | progBitlist    :                  SSZType
  | compatUnion    : List (Nat × SSZType) → SSZType            -- EIP-8016
  deriving DecidableEq

def SSZType.interp : SSZType → Type
  | .uintN 8       => UInt8     | .uintN 16 => UInt16
  | .uintN 32      => UInt32    | .uintN 64 => UInt64
  | .uintN _       => BitVec _
  | .bool          => Bool
  | .vector t n    => Vector t.interp n
  | .list t cap    => { xs : Array t.interp // xs.size ≤ cap }
  | .bitvector n   => BitVec n
  | .bitlist cap   => { bs : Array Bool // bs.size ≤ cap }
  | .container fs  => HList SSZType.interp fs
  | .union opts    => Σ i : Fin opts.length, (opts.get ⟨i, _⟩).interp
  | ...
```

Then `serialize`, `deserialize`, and `hashTreeRoot` are written as one recursion each on `SSZType`, matching the spec pseudocode line-for-line. The well-foundedness obligation in the `container` case is discharged with `List.sizeOf_lt_of_mem` plus `decreasing_by`; this is exactly the pattern Lean's reference manual uses for `Tree.depth` over `List Tree`, and Lean 4.11+'s mutual structural recursion improvements make it routine. User types connect via:

```lean
class SSZRepr (T : Type) where
  shape   : SSZType
  toRepr  : T → shape.interp
  fromRepr: shape.interp → T
  to_from : ∀ r, toRepr (fromRepr r) = r
  from_to : ∀ x, fromRepr (toRepr x) = x
```

The user-facing experience reduces to a single annotation. Declare a normal Lean structure and ask for SSZ:

```lean
structure BeaconBlockHeader where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  bodyRoot      : Root
  deriving SSZRepr

structure Validator where
  pubkey                       : BLSPubkey
  withdrawalCredentials        : Bytes32
  effectiveBalance             : Gwei
  slashed                      : Bool
  activationEligibilityEpoch   : Epoch
  activationEpoch              : Epoch
  exitEpoch                    : Epoch
  withdrawableEpoch            : Epoch
  deriving SSZRepr
```

That is the entire user surface for the common case. No macros, no boilerplate, no manual typeclass instances. The deriving handler is the one piece of metaprogramming Approach B requires: it introspects the structure with `getStructureFields`, looks up `SSZRepr.shape` on each field's type, assembles the matching `SSZType.container [...]` description, and emits the `toRepr`/`fromRepr` isomorphism plus `rfl` proofs of the round-trip laws. The user never writes any of this by hand. `Vector`, `List`, `Bitvector`, `Bitlist`, `BitVec`, `UInt8/16/32/64`, `Bool`, and Sigma-typed unions get library-provided `SSZRepr` instances once and compose through the deriving handler automatically. The handler, far simpler than Approach A's because it only needs to assemble the `shape` and the iso rather than the encoder logic, is the entire metaprogramming budget for the library, in contrast to Approach A's per-type code generation. **The killer property: proving `decode (encode t x) = .ok (x, _)` once on `SSZType` makes the same theorem free for every user type via `simp [r.from_to]`.** Non-malleability follows from `serialize_injective`, also one induction on `SSZType`. This is exactly the architectural dividend EverParse exploits and the same dividend van Geest & Swierstra exploit in their TyDe '17 paper "Generic Packet Descriptions".

The tradeoffs are well-understood. Schema introspection becomes free (`shape : SSZType` is plain data, hashable, comparable, useful for fuzzing against pyssz). Adding new SSZ features (StableContainer, ProgressiveList, CompatibleUnion) requires only a new constructor, an `interp` clause, a serialize/deserialize/HTR case, and a new induction case in the roundtrip proof, leaving **existing user types untouched**. The performance concern, runtime traversal of the description tree, is real but mitigable via Lean's `@[inline]`/`@[reducible]` annotations plus the LCNF specializer; for a *concrete* `shape`, Lean 4 reduces away the `match` on `SSZType` at compile time, analogous to F\*'s partial evaluation in LowParse.

### Approach C: optional macro front-end on top of B

Approach C is one possible surface syntax that lowers to B, rather than a competing design. For the standard SSZ types (Container, Vector, List, Bitvector, Bitlist, Union), Approach B's `structure ... deriving SSZRepr` covers ~90% of the surface area cleanly and a macro adds nothing over it. The macro earns its keep only where Lean's `structure` keyword cannot carry the information SSZ requires, which in practice means **EIP-7495 ProgressiveContainer profiles and the legacy StableContainer**: those have features (active-fields bitvectors, profile inheritance, per-field optionality markers, manually-pinned generalized indices) that don't map onto vanilla Lean structures.

A `profile%` macro for the EIP-7495 case:

```lean
profile% SignedTransaction extends Transaction where
  signature : Signature                    -- new in this profile
  inactive_in_profile := [.amount]         -- 'amount' field marked inactive
```

This declaration carries an active-fields `Bitvector[N]` constant, a parent-profile reference, and per-field active/inactive markers. The macro lowers to a Lean `structure` plus a hand-emitted `SSZRepr` instance whose `shape` is `SSZType.progContainer activeFields fieldShapes` rather than the plain `container` constructor that `deriving` would produce.

Other realistic uses for a custom macro layer: explicit selector values for `CompatibleUnion` (EIP-8016) where selectors must be in `1..127`, custom merkleization limit overrides, or hash-tree-root attribute hooks. **None of these are needed for the Phase 0 / Altair / Bellatrix / Capella / Deneb / Electra type set**: every type in that lineage fits in a vanilla Lean structure. C is a Phase-2 addition, layered on top of a complete B implementation, not a Day-1 design choice.

The mental model: B is the library (inductive `SSZType`, `interp`, the `SSZRepr` typeclass, the deriving handler, and the once-and-done round-trip proofs); C is one of several possible front-ends, by far the least urgent for the formal-verification-first goal.

## 4. Formal verification: prove once, instantiate everywhere

The verification strategy follows directly from Approach B. Three central theorems anchor the library:

**Roundtrip.** `∀ (t : SSZType) (x : ⟦t⟧), deserialize t (serialize t x) = .ok (x, (serialize t x).size)`, proved by induction on `t`. The `uintN` and `bool` cases close with `bv_decide`/`decide`; `vector`, `list`, `bitvector`, `bitlist` close with `simp` plus `omega` on offset arithmetic; the `container` case is the hardest and uses `List.sizeOf_lt_of_mem` for the recursive call into `decode` on each field, plus a small algebraic lemma about offset-table reconstruction.

**Injectivity / non-malleability.** `∀ (t : SSZType) (x y : ⟦t⟧), serialize t x = serialize t y → x = y`, a direct corollary of roundtrip via `decode_encode` plus `Option.some.inj`. This is the property EverParse and EverCBOR ship as a first-class theorem; SSZ guarantees it by construction (canonical little-endian, monotonic offsets, minimal bitlist trailing-1, no extra bytes). **Stating and proving this matches the standard the EF should hold itself to.**

**Length bound.** `∀ (t : SSZType) (x : ⟦t⟧), (serialize t x).size ≤ t.maxByteLength`, by induction on `t`, with `omega` for arithmetic and `decide` for closed cases.

Per-user-type roundtrip is then a one-line corollary:

```lean
theorem SSZRepr.roundtrip [r : SSZRepr T] (a : T) :
    deserialize (serialize a) = .ok (a, _) := by
  simp [serialize, deserialize, decode_encode, r.to_from]
```

The relevant Lean 4 tactics are `simp` (with a tagged `ssz_simp` set on every `serialize`/`deserialize` equation), `omega` for `Nat` / `Int` arithmetic on offsets and lengths, **`bv_decide`** (built-in since 4.12, reduces `BitVec` goals to SAT via CaDiCaL) for endianness and bit-packing lemmas, `induction` on `SSZType`, `split` to peel apart the nested `match` in `decode`, and `Aesop` with a `@[aesop safe]` rule set on the SSZ lemmas for trivial cases. Reserve `native_decide` for the test-vector regression suite, since every invocation adds a `Lean.ofReduceBool` axiom (in Lean 4.29+ each call gets its own named axiom rather than a blanket `trustCompiler`), so it is unsafe for the trusted core.

The closest existing prior art is **ConsenSys's `eth2.0-dafny`** (TACAS '22, Cassez/Fuller/Asgaonkar) which proved exactly the involution lemma `deserialise(serialise(o)) = o` for the Phase-0 SSZ subset in Dafny, plus a Merkleization correctness proof. **The Lean 4 effort can lift their proof structure essentially verbatim**, replacing Dafny's `assume` with Lean's `decreasing_by`. Beyond Dafny, the methodology cousins are **EverParse / LowParse / EverCBOR** (verified zero-copy parsers with non-malleability; PulseParse arXiv:2505.17335 is the 2025 separation-logic refinement), **Narcissus** (Coq's tactic-derived correct-by-construction encoder/decoder pairs, ICFP '19), **Ye & Delaware's Verified Protocol Buffer Compiler** (CPP '20, built on Narcissus), and **van Geest & Swierstra's "Generic Packet Descriptions"** (Agda, TyDe '17, almost the exact universe-of-descriptions architecture proposed here). **Vest** (USENIX Security '25) ships F\*-verified parsers extracting to Rust and is the most recent comparable artefact. Runtime Verification's K-framework Beacon Chain spec and KEVM are tangential, since they verify state-transition logic and EVM bytecode, not SSZ. RV's earlier deposit-contract work *did* verify SSZ Merkleization of `DepositData`. **No F\* or Coq formalisation of full SSZ exists**; a Lean 4 effort would be the first.

## 5. Performance and FFI: where pure Lean ends and C begins

Lean 4's runtime representation determines where you can stay pure and where you cannot. **`ByteArray` is the right primary type for SSZ buffers**, a contiguous `lean_sarray_object` mutated in place when the refcount is one, giving amortised O(1) `push`/`set` and no per-byte boxing. **`Array UInt32` is wrong**: generic `Array α` heap-allocates a boxed `lean_object*` per element unless `α` is `UInt8`/`Float`/`USize`, which have specialised scalar arrays. **`BitVec n` is unboxed for `n ≤ 63` (it's a `Fin (2^n)` over a tagged `Nat`) but a heap GMP bignum for `n ≥ 64`**, so a `BitVec 256` hash allocates per use; for runtime hashes prefer `ByteArray` of size 32 while the *spec* may use `BitVec 256`. **`UInt8/16/32/64` map to native `uintN_t` and stay unboxed** in compiled code; `Nat` is GMP but tagged for small values.

SHA-256 is the unavoidable FFI boundary. **No production-quality pure-Lean SHA-256 exists**: the only published Lean 4 hash library, `gdncc/Cryptography`, covers SHA-3 and notes elaborator limits on loop unrolling (IACR ePrint 2024/1880). For Merkleization-bound workloads (BeaconState root involves hashing tens of MB of leaves and the entire log₂ tree above), a pure-Lean SHA would be **10–100× slower than fastssz**. The standard pattern is `@[extern]` against a C shim:

```lean
@[extern "lean_ssz_sha256"]
opaque sha256 (input : @& ByteArray) : ByteArray

@[extern "lean_ssz_sha256_pairs"]
opaque sha256Pairs (leaves : @& ByteArray) : ByteArray  -- batched, gohashtree-style
```

The `@&` borrowed annotation avoids per-call refcount inc/dec on the input. The C shim wraps `OpenSSL SHA256()` (or BoringSSL, or the AArch64/AVX-accelerated `gohashtree` algorithm), is shipped via Lake's `extern_lib` + `target ... .o` + `buildStaticLib`, and can optionally be embedded directly using **`tydeu/lean4-alloy`**'s in-source C blocks. Lean's existing **`argumentcomputer/Blake3.lean`** is the canonical template for the lakefile and `lean.h` glue.

Every `@[extern]` adds to the trusted computing base (an axiom `Lean.trustCompiler`, or per-decl axioms in 4.29+). To keep the TCB minimal, define a pure-Lean `sha256Spec` used in proofs and tests, plus the FFI `sha256`, with a `theorem sha256_eq_spec` left as an explicit assumption checked against NIST test vectors via `native_decide`. **This is the same compromise HACL\* and BoringSSL's verified portions make**: the pure spec carries the proofs; the fast impl is asserted equivalent and validated empirically.

The two-level refinement architecture extends naturally beyond SHA. Define a slow-but-obvious `encodeUint64Spec` that builds an 8-byte `ByteArray` via `div`/`mod` on `Nat`, then use `@[implemented_by]` to swap in a fast version for runtime, with `theorem encodeUint64_eq_spec : encodeUint64 = encodeUint64Spec := rfl` as a check. **Reserve `@[implemented_by]` and `@[extern]` for SHA-256 and a small set of bulk-memcpy primitives**; keep the SSZ encode/decode logic itself in pure Lean so proofs cover the executed code.

For the Merkleization data structure, **steal remerkleable's tree-with-cached-hash design**: each `Node` carries an `Option ByteArray` cache of its `hash_tree_root`, mutations produce new nodes sharing structure with the old, and the cache is populated lazily. This is the single most important production optimisation. Recomputing `hash_tree_root(BeaconState)` from scratch hashes ~41 MB; with caching, only the path from changed leaves to root.

Realistic performance expectations: with FFI SHA and careful `ByteArray` use, **Lean 4 should land within 2–5× of fastssz on encode/decode and roughly at parity on cached `hash_tree_root`**. Without FFI SHA, expect 10–100× slower than fastssz on Merkleization. Lean 4 should comfortably beat remerkleable, which Loerakker explicitly designed for clarity over performance.

## 6. Prior art, in priority order

**No public Lean 4 SSZ implementation exists** (May 2026). Searches across `github.com/leanEthereum`, `github.com/privacy-scaling-explorations`, `github.com/ethereum`, `github.com/Verified-zkEVM`, and broad GitHub queries return zero results. The name "Lean Ethereum" is a deliberate trap: it refers to the EF's Beam Chain post-quantum redesign, **not Lean the prover**. The Beam Chain ecosystem (`leanEthereum/leanSpec` Python, `leanEthereum/leanSig` Rust, `geanlabs/gean` Go, `Pier-Two/lantern` C, `blockblaz/zeam` Zig with `ssz.zig`, `lambdaclass/libssz` Rust, `ChainSafe/ssz-z` Zig) is reimplementing SSZ in conventional languages, often with Poseidon2 swap-in for hashing, none target Lean 4.

The shortlist of **must-read prior art**, in priority order:

1. **`leanEthereum/leanSpec`** (Python, 476 commits, very active): the reference Lean Consensus spec. Pin a commit, generate fixtures with `uv run fill --clean --fork=devnet`, mirror the type structure under `src/lean_spec/subspecs/`. *This is the spec your Lean library must conform to.*
2. **ConsenSys `eth2.0-dafny`** (TACAS '22 paper at `franck44.github.io/publications/papers/eth2-tacas-22.pdf`): proved `deserialise ∘ serialise = id` and Merkleization correctness for Phase-0 SSZ. *The closest published formal-verification work on SSZ specifically*; their experience report scopes a Lean 4 effort. See `wiki/ssz-notes.md` and `wiki/merkleise-notes.md`.
3. **EverParse / LowParse / EverCBOR** (`github.com/project-everest/everparse`): Microsoft Research's verified parser+serializer combinator library. Pioneered the spec-functional-low-level three-layer architecture and the non-malleability theorem. The 2025 PulseParse paper (arXiv:2505.17335) is the latest separation-logic refinement.
4. **Narcissus** (Coq, ICFP '19, arXiv:1803.04870): tactic-derived correct-by-construction encoder/decoder pairs from binary-format specs. The pattern your Lean deriving handler should embody.
5. **`lambdaclass/libssz`** (Rust): modern, fast, zkVM-friendly, validated against 62,489 `ssz_generic` test cases including ProgressiveContainer/ProgressiveList. *The cleanest unverified reference*; learn the trait split, derive macro shape, and conformance suite from it.

Secondary references worth reading: **`predictablemachines/lean4-json-schema`** (the only published Lean 4 deriving handler that emits a compile-time correctness proof), **van Geest & Swierstra's TyDe '17 paper** (Agda generic packet descriptions, architectural twin of the proposed SSZ universe), **Ye & Delaware's Verified Protocol Buffer Compiler** (CPP '20), **`Lean.Json`'s `deriving FromJson, ToJson`** (the canonical Lean core deriving template), and the **`ssz_generic` test vectors** in `ethereum/consensus-spec-tests`.

The authoritative documents on SSZ semantics for formalisation are the spec at `ethereum.github.io/consensus-specs/ssz/simple-serialize/`, EIP-7495 (current ProgressiveContainer text and the legacy StableContainer text via earlier commits), EIP-7916 (ProgressiveList), EIP-7688 (forward-compat consensus migration), EIP-6493 (SSZ transactions, Profile usage), EIP-8016 (CompatibleUnion), Cayman Nava's HackMD note "EIP-7495 Notes for CL", and Etan Kissling's `pureth.guide` overview. Etan Kissling is the principal author of the SSZ-for-everything cluster and the contact for any spec ambiguity.

## 7. Recommended structure and plan

Build the library in five vertical layers, in this order, with each layer a separate Lean file or directory:

**Layer 1, Spec.** `inductive SSZType` with all twelve constructors (basic, vector, list, bitvector, bitlist, container, union, progContainer, stableContainer, progList, progBitlist, compatUnion). `def SSZType.interp : SSZType → Type` using `BitVec`, `Vector`, refinement subtypes for length-bounded containers, and `HList` for container fields. Total `serialize`, `deserialize`, `hashTreeRoot` by recursion on `SSZType`, with `decreasing_by` discharging the nested-list obligations. This is the formal specification, the trusted ground truth, and the basis for all proofs.

**Layer 2, Proofs.** `theorem decode_encode`, `theorem serialize_injective`, `theorem encode_size_le_max`, all by induction on `SSZType` with the tactic vocabulary above. One proof file per theorem; tag every `serialize` and `deserialize` equation with `@[ssz_simp]` so the inductive cases close uniformly. Aim for under 1 KLOC across all three theorems, since the universe approach makes them tractable.

**Layer 3, User-facing typeclass and deriving.** `class SSZRepr (T : Type)` with `shape`, `toRepr`, `fromRepr`, `to_from`, `from_to`. Deriving handler `deriving SSZRepr` modelled on `Lean.Json` and `idris2-elab-util/Generics.Derive`, emitting the iso plus `rfl` proofs of the laws for structural cases. **The user-facing surface for this layer is just Lean's normal `structure ... deriving SSZRepr` syntax**, with no custom macros and no boilerplate. `Vector`, `List`, `Bitvector`, `Bitlist`, `BitVec`, primitive uints, and `Bool` ship as library-provided `SSZRepr` instances and compose through the handler. Per-user-type roundtrip is a one-line corollary; users never see `SSZType` unless they want to. *Optional Phase-2 addition:* a `profile%` macro on top of this layer (the "Approach C" front-end) for EIP-7495 ProgressiveContainer profiles where active-fields bitvectors and profile inheritance need explicit syntax. Defer this until ProgressiveContainer is actually in scope.

**Layer 4, Production primitives.** `@[extern]` SHA-256 (single + batched) backed by an OpenSSL/BoringSSL/gohashtree C shim, shipped through Lake. A `Tree` data structure with cached `hash_tree_root` per node and structural sharing on mutation, modelled on `protolambda/remerkleable`. Optional `@[implemented_by]`-swapped fast variants for hot encode paths, each with a pure-Lean spec definition and a stated equivalence theorem, proved where feasible, axiomatised where not, validated against `ssz_generic` test vectors via `native_decide`.

**Layer 5, Eth types.** `BeaconBlockHeader`, `Checkpoint`, `Validator`, `BeaconState`, `ExecutionPayload` as plain Lean structures with `deriving SSZRepr` (the Approach B user surface from Layer 3). EIP-6493 `BasicTransaction`/`BlobTransaction` profiles via the optional `profile%` macro, only if EIP-7495 is in scope. Conformance test suite consuming the `ssz_generic` and per-fork `consensus-spec-tests` vectors.

**Sequence the work formal-verification-first**: Layers 1 and 2 must be complete and proved before Layer 3 ships, because the entire value proposition of the architecture is that user types inherit correctness from the proved generic interpreter. Once Layer 2 is closed, Layer 3 onward becomes routine engineering. Layer 4's FFI work can begin in parallel with Layer 3 and is independent of the verification frontier. The C shim is opaque to the kernel and its trust assumption is explicit and bounded.

**Two strategic considerations to lock in before writing code.** First, **commit early to supporting both EIP-7495 wire formats** (current ProgressiveContainer and legacy StableContainer) as separate `SSZType` constructors; whichever the consensus and execution layers ship, you'll need both for the next 18 months and the universe approach makes each one a one-evening addition. Second, **make the hash function a typeclass parameter from day one** (`class Hasher H` with `hash : ByteArray → H`) so you can swap SHA-256 for Poseidon2 when Beam Chain lands without rewriting the Merkle layer; Zeam's `ssz.zig` already does this and Beam Chain's Lean Consensus is moving in this direction.

The single highest-value action available to a protocol engineer in your position is **stating, proving, and publishing the non-malleability theorem for SSZ as a Lean 4 artefact**: `∀ b₁ b₂ a, deserialize b₁ = .ok a → deserialize b₂ = .ok a → b₁ = b₂` (restricted to canonical bytes). It is the property the SSZ spec implicitly asserts but no implementation has ever proved, it is the property the EF needs to defend against ambiguity-based attacks (cf. the lessons from Bitcoin's malleability), and it falls out as a corollary of `serialize_injective` and `decode_encode` once the Layer 2 work is done. **Aim that artefact at a USENIX Security or CCS submission**; the EverParse/EverCBOR/Vest line shows the venue actively rewards such results, and shipping it gives the Lean 4 SSZ library the credibility to become the reference formal model alongside `eth2.0-dafny`.
