# Proof ledger

## Purpose

The forward half of proof coverage for the SSZ library.
[`proof-coverage.baseline`](proof-coverage.baseline) records what is proved;
the baseline shows twenty green cells. This file records what we intend
to prove, what each landed theorem does and does not establish, and why
every row that is not green is not: unstarted, partly landed, or out of
scope for a stated reason.

**Scope.** The proofs cover the pure path, the `PureBox` /
`UncachedBox` world whose `hashTreeRoot` reruns `SSZType.hashTreeRoot`
on every call. The cache layer (`CachedSSZ`, `FastBox`) is the
execution path: the evaluation gates in `SizzLeanTests` and the
`ssz_static` sweep check it, and its landed theorems below are the
seed of a future cached-path equivalence theorem. No further work
targets the `cache ×` rows.

The fork bodies keep the same pair of files under
[`../../EthCLSpecs/docs/`](../../EthCLSpecs/docs/PROOF_LEDGER.md). One design
difference separates the two ledgers. A fork-body row is a spec function,
because a `forkdef` is the unit a theorem characterizes. An SSZ row is a matrix
cell, a `(property, fragment)` pair, because `decode_encode` is one theorem
whose coverage grows one gating-predicate constructor at a time. Rows that the
matrix does not grade, the trust base, the predicate links, the generalized
index, and the Merkle branch, carry a slug of their own in the same
`a × b` form.

## The columns

| Column | What it holds |
| --- | --- |
| Cell | The `property × fragment` pair, matching the slugs the baseline records. Rows outside the matrix carry their own slug in the same form. |
| Arms | The gating-predicate constructors the cell needs. A landed arm is written plain; an open one carries `(open)`. |
| Location | A line span into `packages/SizzLean/SizzLean/`, `Dir/File.lean:start-end`, for the definition the row is about. |
| Property | The theorem the row asks for, and what a landed theorem does and does not establish. |
| Status | `proposed`, `in progress`, `proved`, or `out of scope`. |
| Tracking | The pull request that landed or is landing the proof, and the module holding it. |

A row stays here for its whole life. It opens as `proposed`, and the pull
request that discharges it flips the status and bumps the baseline in the same
diff.

`in progress` covers a theorem being written and one that is partly landed
alike. A partly landed row carries the shape `Landed: … Open: …` in its
Property cell.

`out of scope` carries its reason in the Property cell. Two reasons recur
below: the claim is false as stated, so no proof can exist, or the claim rests
on a cryptographic assumption, which the library records as a named axiom
rather than proves.

## The fragments

The coverage script classifies a gating-predicate constructor by the end of its
name. The four fragments and the arms they hold:

| Fragment | Slug | Arms |
| --- | --- | --- |
| Basic arms | `basic-arms` | `uintN8`, `uintN16`, `uintN32`, `uintN64`, `uintN128`, `uintN256`, `bool` |
| Bit shapes | `bit-shapes` | `bitvector`, `bitlist` |
| Fixed-elem composites | `fixed-composites` | `vectorFixed`, `listFixed`, `containerFixed` |
| Variable-size composites | `variable-composites` | `vectorVar`, `listVar`, `containerVar` |

`SSZType.BasicSupported` (`Spec/BasicSupported.lean:110-186`),
`SSZType.Supported` (`Spec/Supported.lean:67-120`), and
`SSZType.SupportedBounded` (`Spec/Supported.lean:161-200`) all carry these
fifteen constructors under these names. A theorem gated by any of them lights
every cell in its row.

## The Location column

Each row cites a line span: start at the declaration's own line, end at the
last non-blank line before the next top-level construct. That is the convention
[`scripts/check_citations.py`](../../../scripts/check_citations.py) enforces
for both ledgers. `just check-citations` reads this file: each row's citation
must name the declaration it cites, and the span must open it. A declaration
that moves is found by name, and `--fix` moves the span to it.

## What the coverage report reads

`just proof-coverage` reads this file's matrix rows. It warns on a `proved`
row whose cell is red and on a green cell with no `proved` row, and never
fails on this file. What it reads decides how a theorem here has to be
stated, so the rule is recorded once:

- The theorem's module sits under `SizzLean/Proofs/`, namespace
  `SizzLean.Proofs`.
- The three serialization rows select their theorem by name:
  `SizzLean.Proofs.decode_encode`, `SizzLean.Proofs.serialize_injective`,
  `SizzLean.Proofs.encode_size_le_max`. A rename empties the row.
- The `hash-tree-root` row selects every theorem whose statement mentions a
  constant named `hashTreeRoot` under `SizzLean.Spec`. The `cached-tree` row
  selects every theorem whose statement mentions one under `SizzLean.Spec` and
  one under `SizzLean.Cache`. `Node.merkleRoot` carries neither name, so a
  theorem stated on it alone lights nothing.
- A cell counts the constructors of the gating predicates the statement
  carries, predicates of type `SSZType → Prop`. A theorem quantified over all
  of `SSZType` with no gating predicate counts zero arms in every cell, so a
  merkleization theorem has to carry `Supported s` or `BasicSupported s` as a
  hypothesis even where the proof does not need it. The docstring says why.

## The trust base today

`#print axioms` on the built package, for the theorems the baseline counts:

| Theorem | Axioms beyond `propext`, `Classical.choice`, `Quot.sound` |
| --- | --- |
| `decode_encode` | none |
| `serialize_injective` | none |
| `encode_size_le_max` | none (`Classical.choice` unused as well) |
| `supported_of_basicSupported` | none |

The package declares three named axioms, `sha256Hash_eq_spec`
(`Hasher/Sha256Equiv.lean:102-102`), `sha256Combine_eq_spec`
(`Hasher/Sha256Equiv.lean:109-109`), and `sha256BatchCombine_eq_spec`
(`Hasher/Sha256Batch.lean:61-62`). No theorem in the proof set uses them: every
row is stated over a generic `[Hasher H]`, and the axioms enter only through
the `Hasher Sha256` instance. That instance now cites two of them. Its
`batchCombine_eq` field, the class law that the batched level agrees with the
pointwise `combine`, is proved from `sha256BatchCombine_eq_spec` and
`sha256Combine_eq_spec` (`Hasher/Sha256.lean`, `batchCombine_eq_of_axioms`).
Instantiating any merkleization row at `Sha256` therefore picks the two axioms
up; a theorem stated at `Sha256` should say so, as the CLAUDE.md rule on the
FFI-equivalence axioms requires. Six
`@[implemented_by]` swaps sit on the cached path: `zeroHashes`
(`Cache/MerkleTree/Zero.lean:126-127`), `zeroHashAt`
(`Cache/MerkleTree/Zero.lean:151-152`), `HashCons.statsSnapshot`
(`Cache/MerkleTree/HashCons.lean:170-170`), `Node.consCell`
(`Cache/MerkleTree/HashCons.lean:227-227`), `Node.consTree`
(`Cache/MerkleTree/HashCons.lean:269-269`), and `Node.consPair`
(`Cache/MerkleTree/HashCons.lean:281-282`). Every `native_decide` in the package
sits in an `example` block, the smoke tests in `Spec/Deserialize.lean`, the
acceptance examples in `Cache/MerkleTree/Merkle.lean`, and one in
`Hasher/Sha256Equiv.lean`, or in a test module. None sits on a proof path.

## Dependencies between rows

- Both merkleization rows rest on the zero-tower row and the naive-tree row
  under *Merkleization groundwork*.
- Every `cached-tree` cell rests on the coherence-invariant row, and that row
  rests on `Node.rootOf` becoming structural. The cells are the seed of the
  future cached-path equivalence theorem; the rows under *Cached tree ≡
  spec* beyond them are out of scope with it.
- The branch-completeness rows rest on the naive-tree row and on the
  generalized-index bridge.
- The two guard-widening rows change the statements of all three central
  theorems and of `SSZ.roundtrip`, so they land as one change each.
- The fork ledger's two `processDeposit` rows rest on the branch-completeness
  rows here.

---

## Serialization: the three central theorems

### Matrix cells

Every cell is green. Each row names the guards the arm carries, since the
guards are what the widening rows below remove.

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `decode_encode × basic-arms` | `uintN8`, `uintN16`, `uintN32`, `uintN64`, `uintN128`, `uintN256`, `bool` | `Proofs/Roundtrip.lean:120-265` | Decoding the encoding of a basic value returns the value and consumes every byte. Every width closes through the `Nat`-digit codec: the wide widths via the inverse `readNatLE_natToLEBytes` (`Proofs/UIntWide.lean:201-214`), the narrow widths via the reader bridges `readUIntNNLE_natToLEBytes` over the same encoder bridge in `Proofs/UInt.lean`. No guard | proved | `46bfd09`, #18; `Proofs/UInt.lean`, `Proofs/UIntWide.lean`, `Proofs/Bool.lean` |
| `decode_encode × bit-shapes` | `bitvector`, `bitlist` | `Proofs/Roundtrip.lean:120-265` | The bit-packing inverse and the `msbPos` delimiter recovery. `bitvector` needs `0 < n`; `bitlist` needs nothing. Every byte identity closes by kernel `decide` over the chunk shapes, so the arms add no axiom | proved | #10, `Proofs/BitPack.lean` |
| `decode_encode × fixed-composites` | `vectorFixed`, `listFixed`, `containerFixed` | `Proofs/Roundtrip.lean:120-265` | Fixed-element collections and all-fixed containers roundtrip under `0 < n` for vectors and `0 < t.fixedByteSize` for lists. The container arm is the mutual partner `decode_encode_containerFixed_aux`. Rests on `size_serialize_eq_fixedByteSize` (`Proofs/SerializeSize.lean:82-167`) | proved | `46bfd09`; `Proofs/VectorFixed.lean`, `Proofs/ListFixed.lean`, `Proofs/ContainerFixed.lean` |
| `decode_encode × variable-composites` | `vectorVar`, `listVar`, `containerVar` | `Proofs/Roundtrip.lean:120-265` | The offset-table codec roundtrips under the value-level `EncodedFits` guard, which keeps every `uint32` offset placeholder below `2^32` without excluding any schema: every element or field inherits the bound from its slot in the buffer. The widening rows below record the shape of the value-level guard | proved | #29, #75; `Proofs/ContainerVar.lean`, `Proofs/CollectionVar.lean`, `Proofs/Roundtrip.lean` |
| `serialize_injective × basic-arms` | as `decode_encode` | `Proofs/Injective.lean:59-77` | Non-malleability: equal encodings imply equal values. A direct corollary of `decode_encode`, so its coverage, guards, and axioms track that theorem exactly. It says nothing about decoder canonicity, which the `ssz_generic` invalid vectors cover empirically | proved | `46bfd09`, `Proofs/Injective.lean` |
| `serialize_injective × bit-shapes` | as `decode_encode` | `Proofs/Injective.lean:59-77` | As above | proved | #10 |
| `serialize_injective × fixed-composites` | as `decode_encode` | `Proofs/Injective.lean:59-77` | As above | proved | `46bfd09` |
| `serialize_injective × variable-composites` | as `decode_encode` | `Proofs/Injective.lean:59-77` | As above, under the same value-level guard | proved | #29, #75 |
| `encode_size_le_max × basic-arms` | as `decode_encode` | `Proofs/SizeBound.lean:46-97` | The encoded size never exceeds `maxByteLength s` (`Spec/MaxByteLength.lean:57-68`). No axiom beyond `propext` and `Quot.sound` | proved | `46bfd09`, #18 |
| `encode_size_le_max × bit-shapes` | as `decode_encode` | `Proofs/SizeBound.lean:46-97` | As above | proved | #10 |
| `encode_size_le_max × fixed-composites` | as `decode_encode` | `Proofs/SizeBound.lean:46-97` | As above, through the mutual partner `encode_size_le_max_containerFields_aux` | proved | `46bfd09` |
| `encode_size_le_max × variable-composites` | as `decode_encode` | `Proofs/SizeBound.lean:46-97` | As above. The three arms receive the `MAX_LENGTH` guard from the constructor and ignore it, so the guard-widening rows do not touch this theorem's statement | proved | #29, #69, #75 |

### Widening the guards

The `variable-composites` cells are green for a universe that excludes the
containers the library exists for. These rows record the change that admits
them.

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `decode_encode × containerVar-value-guard` | `containerVar` | `Proofs/Roundtrip.lean:354-532`, `SSZType.BasicSupported` at `Spec/BasicSupported.lean:110-186` | The constructor carries no schema guard, and `decode_encode` takes `EncodedFits (.container fs) vs` instead. The walker's `h_max` / `h_pf` hypotheses carry the bound down the walk. Nested fields inherit the bound because a field body is an `extract` of the whole buffer. `.container [.uintN 64, .list (.uintN 64) (2^40)]` is `BasicSupported` (witness example in `Spec/BasicSupported.lean`), and `decode_encode` reaches every value the protocol produces | proved | `Proofs/Roundtrip.lean`, `Spec/MaxByteLength.lean` (etheorem#61) |
| `decode_encode × collections-value-guard` | `vectorVar`, `listVar` | `Proofs/CollectionVar.lean:563-629`, `Proofs/CollectionVar.lean:636-760`, `SSZType.BasicSupported` at `Spec/BasicSupported.lean:110-186` | The same relaxation for the two collection arms. Each element inherits its `EncodedFits` from the body region it sits in, which the walker's `bufEnd` bound covers | proved | `Proofs/CollectionVar.lean` (etheorem#77) |
| `serialize_injective × value-guard` | `vectorVar`, `listVar`, `containerVar` | `Proofs/Injective.lean:59-77` | The corollary takes the value hypothesis on `x`; the hypothesis on `y` follows from `serialize s x = serialize s y`, so one bound suffices | proved | `Proofs/Injective.lean` |
| `roundtrip × value-guard` | all | `SSZ.roundtrip` at `Repr/Class.lean:185-194` | `SSZ.roundtrip` stays gated by `BasicSupported r.shape` and takes `EncodedFits r.shape (r.toRepr x)`. The gate keeps the decoder's schema-validity conditions, which the two zero-width side conditions carry | proved | `Repr/Class.lean` |
| `decode_encode × zero-width` | `vectorFixed`, `vectorVar`, `bitvector` with `n = 0`; `listFixed` with `t.fixedByteSize = 0` | `SSZType.BasicSupported` at `Spec/BasicSupported.lean:110-186` | Roundtrip for these shapes is false, so no proof can exist. The decoder rejects a zero-length vector and a zero-length bitvector, which the `ssz_generic` cases `vec_*_0` and `bitvec_0` pin, and a list of zero-width elements cannot recover its count. `Supported` admits them because it is the structural codec predicate | out of scope | |
| `gates × nondegenerate-name` | all | `SSZType.BasicSupported` at `Spec/BasicSupported.lean:110-186` | With the value guards on the theorems, the whole difference between `BasicSupported` and `Supported` is the two zero-width side conditions. The module docstring records that as the predicate's definition: `BasicSupported` is `Supported` plus non-degeneracy, and the ARCHITECTURE and PLAN record the same definition | proved | `Spec/BasicSupported.lean` |

---

## The trust base

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `trust × bv_decide-uintN16` | `uintN16` | `serialize_uintN16_eq_natToLEBytes` at `Proofs/UInt.lean:276`; `readUInt16LE_append_natToLEBytes` at `Proofs/UInt.lean:367` | Discharge the little-endian identity without a SAT certificate. Routed through the `Nat`-digit codec that `Proofs/UInt.lean` proves (`serialize_uintN16_eq_natToLEBytes`, `readUInt16LE_append_natToLEBytes`, `digits16`), so `decode_encode` carries the three standard axioms alone | proved | `Proofs/UInt.lean` |
| `trust × bv_decide-uintN32` | `uintN32` | `serialize_uintN32_eq_natToLEBytes` at `Proofs/UInt.lean:286`; `readUInt32LE_append_natToLEBytes` at `Proofs/UInt.lean:381` | `serialize_uintN32_eq_natToLEBytes`, `readUInt32LE_append_natToLEBytes`, at width 4 | proved | `Proofs/UInt.lean` |
| `trust × bv_decide-uintN64` | `uintN64` | `serialize_uintN64_eq_natToLEBytes` at `Proofs/UInt.lean:304`; `readUInt64LE_append_natToLEBytes` at `Proofs/UInt.lean:398` | `serialize_uintN64_eq_natToLEBytes`, `readUInt64LE_append_natToLEBytes`, at width 8 | proved | `Proofs/UInt.lean` |
| `trust × bv_decide-offset` | `vectorVar`, `listVar`, `containerVar` | `readUInt32LE_uint32LE_append` at `Proofs/ContainerVar.lean:121` | `readUInt32LE_uint32LE_append`, the `uint32` offset bridge the three offset-table arms share. Same route as the narrow widths. With the four rows above closed, `decode_encode` and `serialize_injective` carry only the three standard axioms | proved | `Proofs/ContainerVar.lean` |
| `trust × sha256-ffi` | | `Hasher/Sha256Equiv.lean:102-102`, `Hasher/Sha256Equiv.lean:109-109`, `Hasher/Sha256Batch.lean:61-62` | The FFI hasher computes the same function as `LeanSha256`. Empirical, 185 cases in `SizzLeanTests/Sha256Equivalence.lean` plus the batch suite. A `@[csimp]` proof would need the FFI re-declared as a `def` with the spec as its body, which trades one trust entry for another. No merkleization theorem below depends on these axioms, since every statement is symbolic in `Hasher.combine` | out of scope | |
| `trust × zero-memo` |  | `zeroHashRec` at `Cache/MerkleTree/Zero.lean:84-86`, `zeroHashAt` at `Cache/MerkleTree/Zero.lean:151-152` | The kernel-visible tower is `zeroHashRec`, a total recursion over `Hasher.combine (H := H)` (`Proofs/Merkle/Zero.lean`, `zeroHashRec_eq_spec`), so it agrees with the spec tower for every hasher. The memo read remains the runtime body, substituted via `@[implemented_by]`, with the swap's side condition, that `H`'s combine is SHA-256, written in the docstring. Every `cached-tree` cell rests on this refactor | proved | `Cache/MerkleTree/Zero.lean`, `zeroHashRec` generic, `zeroHashAt` swapped. |

---

## Gating predicates

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `gates × basic-to-supported` | all | `Spec/BasicSupported.lean:229-251` | `BasicSupported s → Supported s`, with the two field-list companions, as a mutual block. The drift guard: a constructor added to one predicate and not the other fails the build | proved | #21, #29, #75; `Spec/BasicSupported.lean` |
| `gates × supportedBounded` | all | `Spec/Supported.lean:238-260`, `Spec/Supported.lean:292-314` | `Supported s ↔ SupportedBounded s`, with the field-list companions, six theorems in two mutual blocks (forward `232-284`, converse `286-338`), one constructor application per arm. Turns the docstring's "extensionally equal" claim into a kernel-checked fact and puts the third predicate under the drift guard. The alternative is deletion; the equivalence is cheaper and keeps the room the docstring reserves for an uncapped arm | proved | `Spec/Supported.lean` |
| `gates × basic-to-bounded` | all | `Spec/BasicSupported.lean:314-316` | `BasicSupported s → SupportedBounded s`, by composing the two rows above. No induction of its own | proved | `Spec/BasicSupported.lean` |

---

## Merkleization groundwork

These rows are prerequisites. None lights a matrix cell on its own, and every
merkleization theorem below rests on them.

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `merkle × public-helpers` |  | `Spec/HashTreeRoot.lean:290-292`, `Spec/HashTreeRoot.lean:168-172`, `Spec/HashTreeRoot.lean:312-314` | `merkleize`, `zeroHashAt`, `combineLayerAt`, `promoteThroughZeros`, `mixInLength`, and the cache side's `zero32` are public under `SizzLean.Spec`, so theorems about them live under `Proofs/`. `merkleizeAt` is the named level-indexed fold behind `merkleize` (`Spec/HashTreeRoot.lean:290-292`), the loop the proofs reason over. A refactor | proved | `Spec/HashTreeRoot.lean`, `merkleizeAt` lifted, helpers public. |
| `merkle × structural-rootOf` | | `Node.rootOf` at `Cache/MerkleTree/Zero.lean:167`, `Node.commitAndHash` at `Cache/MerkleTree/SetAt.lean:236` | `Node.rootOf` and `Node.commitAndHash` are structural on `Node`, so the kernel has unfolding equations for both and the proofs in `Proofs/Merkle/` can case on their arms. `Node.ofLeaves` fills slots through `rootOf`, which is what makes the coherence and builder theorems below possible. A refactor | proved | `Cache/MerkleTree/Zero.lean`, `Cache/MerkleTree/SetAt.lean`: `Node.rootOf` and `Node.commitAndHash` structural. |
| `merkle × naive-tree` |  | `Spec/HashTreeRoot.lean:290-292` | `naiveRoot H (leaves : List ByteArray) (depth : Nat)` is the textbook fold that pads to `2^depth` leaves with zero subtrees built from bare `zero32` leaves (`naiveZero`) and combines pairwise. Proved: `merkleize H chunks depth = naiveRoot H chunks depth` for `chunks.length ≤ 2^depth`. The spec folds breadth-first with level-indexed zero padding, `naiveRoot` splits depth-first, so the induction carries a level offset. The overflow arm of `merkleizeAt`, which returns the first chunk, sits outside the hypothesis. Both merkleization rows and the branch rows reduce to this statement | proved | `Proofs/Merkle/Naive.lean`, `merkleize_eq_naiveRoot`. |
| `merkle × zero-tower` |  | `Spec/HashTreeRoot.lean:168-172`, `zeroHashAt` at `Cache/MerkleTree/Zero.lean:151-152` | Two facts. `Spec.zeroHashAt H d = naiveRoot H [] d`, by induction on `d`. `Cache.zeroHashAt H d = Spec.zeroHashAt H d` at every depth, including past the 100-entry memo, which `zeroHashAt`'s `else` branch continues by the same recurrence. `SizzLeanTests/ZeroHashDepth.lean` pins the join at depth 100 empirically | proved | `Proofs/Merkle/Zero.lean`, `cache_zeroHashAt_eq_spec`, `spec_zeroHashAt_eq_naiveRoot`. |
| `merkle × chunking` |  | `Spec/HashTreeRoot.lean:132-140`, `Spec/HashTreeRoot.lean:100-107`, `Spec/HashTreeRoot.lean:114-118`, `chunkDepth` at `Spec/HashTreeRoot.lean:298-304` | `chunkify b` has `bytesToChunkCount b.size` chunks of 32 bytes each; `padToChunk b` has 32 bytes when `b.size ≤ 32`; `natToChunk n` has 32 bytes; `chunkDepth n` is the least `d` with `n ≤ 2^d` for `1 ≤ n`, and `chunkDepth 0 = 0`. The bookkeeping Dafny proved for its merkleizer, and the side conditions every `naiveRoot` application below needs | proved | `Proofs/Merkle/Chunk.lean`, `length_chunkify`, `size_mem_chunkify`, `size_padToChunk`, `size_natToChunk`, `le_two_pow_chunkDepth`, `chunkDepth_le`. |

---

## Merkleization: the `hash-tree-root` row

The row asks for a theorem about `SSZType.hashTreeRoot`
(`Spec/HashTreeRoot.lean:376`) per fragment. The proposed content is a
characterization: each arm's root is the naive tree over the arm's chunks or
sub-roots, with the mix-in the spec prescribes. Stated with a gating predicate
so the cell lights, per the rule above.

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `hash-tree-root × basic-arms` | `uintN8` … `uintN256`, `bool` | `SSZType.hashTreeRoot` at `Spec/HashTreeRoot.lean:514` | `hashTreeRoot H (.uintN w) x = padToChunk (serialize (.uintN w) x)` for the six widths, and the same for `.bool` (`hashTreeRoot_basic_eq_padToChunk`): the wide widths reach the padded encoding through the digit-codec link `natToChunk_eq_padToChunk_natToLEBytes`, so the `natToChunk` spelling of the arms and the `natToLEBytes` spelling of the encoder meet. Corollary: distinct basic values have distinct roots (`hashTreeRoot_basic_injective`), since the encoding has a fixed width per shape and `padToChunk` is injective among buffers of one width. No hash is applied at a basic leaf, so no cryptographic assumption enters. | proved | `Proofs/Merkle/HashTreeRoot.lean`, `hashTreeRoot_basic_eq_padToChunk` (gated; the per-arm `hashTreeRoot_uintN8` … `hashTreeRoot_bool` feed it); `Proofs/Merkle/OfShape.lean`, `ofShape_root`. |
| `hash-tree-root × bit-shapes` | `bitvector`, `bitlist` | `SSZType.hashTreeRoot` at `Spec/HashTreeRoot.lean:514` | `bitvector`: the root is `naiveRoot` over `chunkify` of the packed bytes at `chunkDepth (bytesToChunkCount ⌈n/8⌉)`. `bitlist`: the body root is over the bits without the delimiter, at the cap-derived depth, and the actual bit count is mixed in. The body bytes equal `packBitsLE` of the bit list, which ties the arm to `Proofs/BitPack.lean` | proved | `Proofs/Merkle/HashTreeRoot.lean`, `hashTreeRoot_bitvector_gated`, `hashTreeRoot_bitlist_gated`; `Proofs/Merkle/OfShape.lean`, `ofShape_root`. |
| `hash-tree-root × fixed-composites` | `vectorFixed`, `listFixed`, `containerFixed` | `SSZType.hashTreeRoot` at `Spec/HashTreeRoot.lean:514`, `SSZType.hashTreeRootFields` at `Spec/HashTreeRoot.lean:474` | The container root is `naiveRoot` over the field roots at `chunkDepth fs.length`, and it depends on the fields only through their roots: equal field roots give an equal container root. A basic-element vector packs its serialization into chunks; a composite-element vector takes element roots. The roots-only fact is what a field-replacement update needs: the new root depends on the replaced field's root alone | proved | `Proofs/Merkle/HashTreeRoot.lean`, `hashTreeRoot_vector_gated`, `hashTreeRoot_container_gated` (the per-arm `hashTreeRoot_vectorFixed`, `hashTreeRoot_listBasic`, `hashTreeRoot_container`, `hashTreeRoot_container_congr` feed them); `Proofs/Merkle/OfShape.lean`, `ofShape_root`. |
| `hash-tree-root × variable-composites` | `vectorVar`, `listVar`, `containerVar` | `SSZType.hashTreeRoot` at `Spec/HashTreeRoot.lean:514`, `SSZType.hashTreeRoot` at `Spec/HashTreeRoot.lean:514` | A list root is `mixInLength` of its body root and its actual length, and `hashTreeRootListComposite H t xs acc = acc.reverse ++ xs.map (hashTreeRoot H t)`, which turns the tail-recursive accumulator back into a map. A composite-element vector or a mixed container merkleizes element or field roots the same way as the fixed case; the variable-size distinction is a serialization fact that merkleization never reads, and the theorem says so | proved | `Proofs/Merkle/HashTreeRoot.lean`, `hashTreeRoot_vector_gated`, `hashTreeRoot_list_gated` (the per-arm `hashTreeRoot_vectorComposite`, `hashTreeRoot_listComposite`, `hashTreeRootListComposite_eq` feed them); `Proofs/Merkle/OfShape.lean`, `ofShape_root`. |

---

## Cached tree ≡ spec: the `cached-tree` row

The contract every cache test asserts by `native_decide`:

```
(CachedSSZ.ofValue H v).hashTreeRoot.1 = SSZ.hashTreeRoot H v
```

`SizzLeanTests/TreeBackedCoherence.lean` checks it on the example containers,
and the `ssz_static` sweep on the consensus containers. The matrix rows below
are proved; the cache layer is the execution path, and the equivalence
theorem that would go beyond the fresh-box case is future work. The final
statement must mention `CachedSSZ.hashTreeRoot`
(`Cache/TreeBacked.lean:438` through its alias at `446`) or
`Box.hashTreeRoot` (`Cache/Box.lean:122-127`). A statement on `Node.merkleRoot`
alone leaves the cell red.

### Prerequisites

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `cache × coherent` | | `Node.merkleRootWithCache` at `Cache/MerkleTree/Merkle.lean:54`, `Node` at `Cache/MerkleTree/Node.lean:70` | Define `Node.root H`, the structural root that ignores every cache slot, and `Node.Coherent H`, which holds when every filled slot equals the `root` of its pair. Prove: `Coherent n → (n.merkleRootWithCache H).1 = n.root H`, the returned tree is `Coherent` with the same `root`, and `Coherent n → n.rootOf H = n.root H`. A cleared slot (`none`) is coherent, so `setAtBits` keeps the invariant along the spine. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work, and this theorem is its seed (`Proofs/Merkle/Coherent.lean`: `merkleRootWithCache_fst`, `merkleRootWithCache_snd_coherent`, `merkleRootWithCache_snd_root`, `rootOf_eq_root`). | out of scope | `Proofs/Merkle/Coherent.lean` |
| `cache × ofLeaves` |  | `Node.ofLeaves` at `Cache/MerkleTree/Zero.lean:195` | `(Node.ofLeaves H ls d).root H = merkleize H ls d` for `ls.length ≤ 2^d`, and the tree is `Coherent`. Rests on `merkle × naive-tree` and `merkle × zero-tower`, since `ofLeaves` pads with `zeroLeaf H d`, whose slot holds `Cache.zeroHashAt H (d + 1)`. `List.splitAt` at `2^d` is the depth-first split the naive tree makes, so the proof is one induction on `d`. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work, and this theorem is its seed (`Proofs/Merkle/Build.lean`: `ofLeaves_root`, `ofLeaves_coherent`). | out of scope | `Proofs/Merkle/Build.lean` |
| `cache × ofSubtrees` |  | `Node.ofSubtrees` at `Cache/MerkleTree/Build.lean:77` | The same statement for `Node.ofSubtrees H subs d`, with `subs.map (·.root H)` as the leaf list and `∀ s ∈ subs, s.Coherent H` as the extra hypothesis. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work, and this theorem is its seed (`Proofs/Merkle/Build.lean`: `ofSubtrees_root`, `ofSubtrees_coherent`). | out of scope | `Proofs/Merkle/Build.lean` |
| `cache × mixInLength` |  | `Node.mixInLength` at `Cache/MerkleTree/Build.lean:105`, `Spec.mixInLength` at `Spec/HashTreeRoot.lean:312` | `(Node.mixInLength H n count).root H = Spec.mixInLength H (n.root H) count`, and coherence is preserved. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work, and this theorem is its seed (`Proofs/Merkle/Build.lean`: `mixInLength_root`, `mixInLength_root_coherent`). | out of scope | `Proofs/Merkle/Build.lean` |

### Matrix cells

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `cached-tree × basic-arms` | `uintN8` … `uintN256`, `bool` | `Node.ofShape` at `Cache/MerkleTree/Build.lean:122` | `(Node.ofShape H s x).root H = SSZType.hashTreeRoot H s x`, and `ofShape` is `Coherent`, for the basic arms. Each arm is one `leaf`, so the proof is `rfl` after unfolding once `hash-tree-root × basic-arms` has aligned the byte spellings. Lifted to `CachedSSZ.ofValue` for a fresh box with no pending writes, `consing := false`: `Thunk.get` of `Thunk.mk` reduces, `pending` is empty, and `merkleRootWithCache` returns `root` by `cache × coherent`. The agreement is gated by `BasicSupported` (see `Proofs/Merkle/OfShape.lean`'s module docstring for why), so the zero-width shapes are outside it. Hash-consing (`consing := true`) is out of scope: optimisation; `SizzLeanTests/HashConsCoherence.lean` stays as the evidence for consing boxes. The cache layer is the execution path, checked by the evaluation gates and the `ssz_static` sweep; this theorem is the seed of a future equivalence theorem | proved | `Proofs/Merkle/OfShape.lean`, `ofShape_root`, `ofShape_coherent`; `Proofs/Merkle/CachedSSZ.lean`, `cachedSSZ_hashTreeRoot_ofValue`, `box_hashTreeRoot_cached`. |
| `cached-tree × bit-shapes` | `bitvector`, `bitlist` | `Node.ofShape` at `Cache/MerkleTree/Build.lean:122` | The same, through `cache × ofLeaves` and `cache × mixInLength`. Both arms build the same byte list the spec chunkifies, so the theorem is an equation between two `merkleize` calls on equal arguments. The agreement is gated by `BasicSupported` (see `Proofs/Merkle/OfShape.lean`'s module docstring for why), so the zero-width shapes are outside it. Hash-consing (`consing := true`) is out of scope: optimisation; `SizzLeanTests/HashConsCoherence.lean` stays as the evidence for consing boxes. The cache layer is the execution path, checked by the evaluation gates and the `ssz_static` sweep; this theorem is the seed of a future equivalence theorem | proved | `Proofs/Merkle/OfShape.lean`, `ofShape_root`, `ofShape_coherent`; `Proofs/Merkle/CachedSSZ.lean`, `cachedSSZ_hashTreeRoot_ofValue`, `box_hashTreeRoot_cached`. |
| `cached-tree × fixed-composites` | `vectorFixed`, `listFixed`, `containerFixed` | `Node.ofShape` at `Cache/MerkleTree/Build.lean:122`, `Node.merkleRootWithCache` at `Cache/MerkleTree/Merkle.lean:54` | The same, through `cache × ofSubtrees`. One mutual theorem block mirrors the builder's mutual block: `ofShape_root`, `subtreesForFields_roots` (equals `hashTreeRootFields`), and `subtreesForListComposite_roots` (equals `hashTreeRootListComposite`, both accumulate in reverse). Every cell in this row and the next lights at once, since the block covers every arm; the split into four rows records what each fragment's arm adds. The agreement is gated by `BasicSupported` (see `Proofs/Merkle/OfShape.lean`'s module docstring for why), so the zero-width shapes are outside it. Hash-consing (`consing := true`) is out of scope: optimisation; `SizzLeanTests/HashConsCoherence.lean` stays as the evidence for consing boxes. The cache layer is the execution path, checked by the evaluation gates and the `ssz_static` sweep; this theorem is the seed of a future equivalence theorem | proved | `Proofs/Merkle/OfShape.lean`, `ofShape_root`, `ofShape_coherent`; `Proofs/Merkle/CachedSSZ.lean`, `cachedSSZ_hashTreeRoot_ofValue`, `box_hashTreeRoot_cached`. |
| `cached-tree × variable-composites` | `vectorVar`, `listVar`, `containerVar` | `Node.ofShape` at `Cache/MerkleTree/Build.lean:122`, `Node.merkleRootWithCache` at `Cache/MerkleTree/Merkle.lean:54` | As above. Both `ofShape` and `hashTreeRoot` dispatch on `isBasicType` rather than on `isFixedSize`, so the variable-size arms need no separate argument. The agreement is gated by `BasicSupported` (see `Proofs/Merkle/OfShape.lean`'s module docstring for why), so the zero-width shapes are outside it. Hash-consing (`consing := true`) is out of scope: optimisation; `SizzLeanTests/HashConsCoherence.lean` stays as the evidence for consing boxes. The cache layer is the execution path, checked by the evaluation gates and the `ssz_static` sweep; this theorem is the seed of a future equivalence theorem | proved | `Proofs/Merkle/OfShape.lean`, `ofShape_root`, `ofShape_coherent`; `Proofs/Merkle/CachedSSZ.lean`, `cachedSSZ_hashTreeRoot_ofValue`, `box_hashTreeRoot_cached`. |

### Updates and the box surface

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `cache × serialize` | all | `TreeBacked.serialize` at `Cache/TreeBacked.lean:372`, `Box.serialize` at `Cache/Box.lean:132` | `t.serialize = SSZ.serialize t.view` and the same for `Box.serialize`, by unfolding. `SizzLeanTests/SerializeCacheCoherence.lean` checks it by evaluation; the theorem is a one-line `rfl` per flavour. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work, and this theorem is its seed (`Proofs/Merkle/CachedSSZ.lean`: `treeBacked_serialize_eq`, `cachedSSZ_serialize_eq`, `box_serialize_eq`). | out of scope | `Proofs/Merkle/CachedSSZ.lean` |
| `cache × setAtBits` | | `Cache/MerkleTree/SetAt.lean:89` | `(n.setAtBits bits m).root H` is `n.root H` with the subtree at `bits` replaced by `m.root H`, and the result is `Coherent` when `n` and `m` are. `Node.subtreeAt` and `Node.replaceAt` are the read and the reference; no hypothesis on the path is needed, since a path that runs past a leaf leaves both trees unchanged. `SizzLeanTests/SetAtRandom.lean` is the empirical half. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work. The update-path proof set is parked out of scope with the equivalence theorem; the gates carry the claim (`SizzLeanTests/SetAtRandom.lean`, `SizzLeanTests/PendingPrefixConflict.lean`). | out of scope | |
| `cache × setManyAt` | | `Cache/MerkleTree/SetAt.lean:171` | `n.setManyAt us` equals the left fold of `setAtBits` over `us` when no path in `us` is a proper prefix of another, the precondition the module docstring states. Under a prefix pair the batch drops the deeper write and the fold does not, so the precondition is part of the statement. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work. The update-path proof set is parked out of scope with the equivalence theorem; the gates carry the claim (`SizzLeanTests/PendingPrefixConflict.lean`). | out of scope | |
| `cache × commitAndHash` | | `Node.commitAndHash` at `Cache/MerkleTree/SetAt.lean:236` | The root half of the fusion claim: `(Node.commitAndHash H false n us).1 = (n.setManyAt us).rootOf H` (`commitAndHash_root_eq`). The full tree equality is false: an untouched child with unfilled slots is reused raw by the fused commit and filled by the cached walk, so the statement is about the root, the value every caller reads. (the `consing := true` path is out of scope: optimisation). Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work. The proof of this row sits in the parked update-path proof set (`mb/parked-merkle-proofs/`), as does the root-contract note in `Cache/MerkleTree/SetAt.lean`'s module docstring; the gates carry the claim | out of scope | |
| `cache × ofShape-field-path` | `containerFixed`, `containerVar`, `vectorFixed`, `vectorVar`, `listFixed`, `listVar` | `Node.ofShape` at `Cache/MerkleTree/Build.lean:122` | Replacing one field: `((Node.ofShape H (.container fs) vs).setAtBits (gindexBits (2^(chunkDepth fs.length) + k)) (Node.ofShape H t v')).root H` equals `SSZType.hashTreeRoot H (.container fs) (vs with field k := v')`. The same for element `i` of a composite-element vector, and for a list with the `[false]` mix-in-length prefix on the path and the length leaf rewritten. A basic-packed element is not a subtree, so the `sszUpdate` macro rebuilds the owning collection; that case is the container lemma applied one level up. These are the lemmas the macro's emitted bit lists are checked against. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work. The update-path proof set is parked out of scope with the equivalence theorem; the gates carry the claim (`SizzLeanTests/TreeBackedSetField.lean`, `SizzLeanTests/PendingOverlayCoherence.lean`). | out of scope | |
| `cache × update-coherence` | all | `CachedSSZ.hashTreeRoot` at `Cache/TreeBacked.lean:438`, `hashTreeRootCached` at `Cache/TreeBacked.lean:329` | For a box `t` with `Coherent` base whose root is `SSZ.hashTreeRoot H t.view`, and a pending write at `g` whose closure returns `Node.ofShape` of the new view's projection at `g`, `(t.addPending g d v').hashTreeRootCached.1 = SSZ.hashTreeRoot H v'`. The macro is a metaprogram, so the theorem is stated over the runtime API with the closure's contract as a hypothesis (`h_cons : t.consing = false` pins it to the pure path; hash-consing is out of scope: optimisation), and per-call-site `example` blocks discharge the contract by `rfl` on the emitted bit list. `SizzLeanTests/TreeBackedSetField.lean` and `PendingOverlayCoherence.lean` are the empirical half. Out of scope: the cache layer is the execution path, checked by the evaluation gates in `SizzLeanTests` and the `ssz_static` sweep; the equivalence theorem is future work. The update-path proof set is parked out of scope with the equivalence theorem; the gates carry the claim (`SizzLeanTests/TreeBackedSetField.lean`, `SizzLeanTests/PendingOverlayCoherence.lean`). | out of scope | |
| `cache × hash-cons` | | `Cache/MerkleTree/HashCons.lean:269-269`, `Cache/MerkleTree/HashCons.lean:281-282` | `Node.consTree n = n` and `Node.consPair l r root = .pair l r (some root)` hold by `rfl`, since the kernel bodies are the identity and the plain allocation. The runtime claim, that a shape-equal cached cell with the same root has the same leaves, rests on collision resistance of the hasher. Hash-consing is out of scope: optimisation; `SizzLeanTests/HashConsCoherence.lean` stays as the evidence for consing boxes, checking the shape rule by evaluation | out of scope | |

---

## Generalized index

`Spec/GeneralizedIndex.lean` models `get_generalized_index(typ, path)`
(`ssz/merkle-proofs.md`) as `SSZType.generalizedIndex`, a fold over a path of
`PathStep`s. The library's index code in `Cache/MerkleTree/SetAt.lean` stays in
bit-path form, and the `sszUpdate` elaborator computes paths per call site; the
rows below tie the two together.

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `gindex × bits-inverse` | | `Cache/MerkleTree/SetAt.lean:54-56`, `Cache/MerkleTree/SetAt.lean:72` | `gindexOfBits (gindexBits g) = g` for `1 ≤ g`, and `gindexBits (gindexOfBits bits) = bits`. `gindexOfBits` sits next to `gindexBits` in `Cache/MerkleTree/SetAt.lean`. Closes the Nimbus-class off-by-one for the round trip the pending map depends on | proved | `Proofs/Merkle/Gindex.lean`, `gindexOfBits_gindexBits`, `gindexBits_gindexOfBits`. |
| `gindex × routeRight-bridge` | | `Cache/MerkleTree/SetAt.lean:54-56` | For `index < 2^depth`, `gindexBits (2^depth + index)` is the list of `index.testBit i` for `i` from `depth - 1` down to `0`. EthCLLib's `routeRight index i` reads the same bit, so its bottom-up branch fold and this top-down path agree. The SizzLean half is the `testBit` statement; the EthCLLib half, which names `routeRight`, lives in `EthCLLib/Proofs/MerkleBranch.lean` because SizzLean does not import EthCLLib | proved | `Proofs/Merkle/Gindex.lean`, `gindexBits_pow_add`; `EthCLLib/Proofs/MerkleBranch.lean`, `routeRight_eq_testBit`. |
| `gindex × get-generalized-index` | all | `Spec/GeneralizedIndex.lean:132-133` | `get_generalized_index(typ, path)` as `SSZType.generalizedIndex`, the spec's left fold: each step multiplies the running index by the block width and adds the slot, with the slot's type as the next type. The fold recurses on the field's or element's own type, `__len__` descends into `uint64`, and a basic-element collection addresses the chunk that packs the element. The decomposition: `gindexBits_generalizedIndex` (`Proofs/Merkle/Gindex.lean`) proves a returned index's `gindexBits` path is `SSZType.pathBits`, the steps' bit paths concatenated outermost step first, and `pathBits_container_field`, `pathBits_vector_elem`, and `pathBits_list_elem` spell the composite cases in the form `walkPath` emits | proved | `Spec/GeneralizedIndex.lean`, `generalizedIndex_field_top`, `generalizedIndex_elem_vector_top`, `generalizedIndex_elem_list_top`, `generalizedIndex_length_top`; `Proofs/Merkle/Gindex.lean`, `gindexBits_generalizedIndex`, `gindexBits_append_step`. |

---

## Branch completeness

`isValidMerkleBranch` lives in EthCLLib's `Spec/SigningRoot`, and
`EthCLLib.Proofs.MerkleBranch` already reduces it past the length guard to
a fold of the branch over the leaf. Its reconstruction theorem
`isValidMerkleBranch_iff` is public, and so is the fold `branchFold` it is
stated on. The rows here are the SizzLean half: that a tree's honest
opening satisfies that fold.

| Cell | Arms | Location | Property | Status | Tracking |
| --- | --- | --- | --- | --- | --- |
| `branch × opening` | | `foldOpening` at `Proofs/Merkle/Opening.lean:115` | The opening lives on the pure path: `naiveOpeningAt` walks the chunk tree `Spec.merkleize` builds, top down, and names each sibling by the sibling subtree's own root (`naiveRootAt` over the other half), so no coherence hypothesis is needed; `naiveLeafAt` names the chunk a path addresses, padding included. `foldOpening` is the same fold `EthCLLib`'s check performs, consuming the top-down list deepest-first. Proved: `foldOpening_naiveOpeningAt` (the tree over `naiveRootAt`), `foldOpening_openingAt` (on `Spec.merkleize`, through `merkleize_eq_naiveRoot`), and in EthCLLib the bridge `branchFold_eq_foldOpening` plus `isValidMerkleBranch_of_foldOpening`, which turns a reconstruction `foldOpening … (gindexBits (2 ^ depth + index)) = vecToBytes root` into `isValidMerkleBranch … = true` for `index < 2 ^ depth`. That is the theorem the fork ledger's `processDeposit` rows wait on | proved | `Proofs/Merkle/Opening.lean`, `foldOpening_naiveOpeningAt`, `foldOpening_openingAt`; `EthCLLib/Proofs/MerkleBranch.lean`, `branchFold_eq_foldOpening`, `isValidMerkleBranch_of_foldOpening`. |
| `branch × mix-in-length` | `listFixed`, `listVar`, `bitlist` | `foldOpening_mixInLength` at `Proofs/Merkle/Opening.lean:187` | The opening of a chunk under a length mix-in, on the pure path: the length chunk prepended to the opening, one `false` prepended to the path, and the fold returns `Spec.mixInLength` of the body root (`foldOpening_mixInLength`), in `merkleize` spelling under the same length bound as `foldOpening_openingAt` (`foldOpening_mixInLength_merkleize`). Stated general over depth, it serves the sidecar inclusion proofs the fork bodies will model | proved | `Proofs/Merkle/Opening.lean`, `foldOpening_mixInLength`, `foldOpening_mixInLength_merkleize`. |
| `branch × deposit-tree` | | | `processDeposit` checks a branch against the deposit contract's incremental tree, which is not an `ofShape` tree. The wire value needs its own connection to a tree the rows above describe. Runtime Verification proved the incremental root equal to the naive full-tree root in Coq, the closest prior art. Out of scope here until that tree is modeled, then a row of its own | out of scope | |
| `branch × normalized` | | | The light-client call sites use `is_valid_normalized_merkle_branch`, which pads a short branch with a zero prefix. `isValidMerkleBranch` rejects a branch whose length differs from the depth, so the normalized form must be modeled before its completeness can be stated | proposed | |

---

## Related work

- [`PLAN.md`](PLAN.md) Phase 5 is the stage this ledger itemizes. Stage 18 is
  the serialization section; *Beyond the three central theorems* is the rest.
- [`ARCHITECTURE.md`](ARCHITECTURE.md) §4 states the three central theorems and
  §11 draws the trust boundary the `trust ×` rows refine.
- [`../README.md`](../README.md#proof-coverage) carries the per-constructor
  table with the proof technique for each arm, the finer reading of the twenty
  green cells.
- [`../../EthCLSpecs/docs/PROOF_LEDGER.md`](../../EthCLSpecs/docs/PROOF_LEDGER.md)
  is the fork-body ledger. Its `processDeposit` rows depend on the branch rows
  here.
- etheorem#61, etheorem#77 (the guard widening), etheorem#76 (this file and the
  script work that reads it).
- ConsenSys `eth2.0-dafny` proved chunk-count and length bookkeeping for its
  merkleizer and left `hash()` uninterpreted. Runtime Verification's Coq work
  proved the deposit contract's incremental Merkle root equal to the naive
  full-tree root. Neither proved a cached tree against a spec merkleizer, and
  neither proved branch completeness, so the rows above have no prior statement
  to reuse beyond the naive-tree shape.
