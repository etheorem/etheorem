# A persistent, cached hash_tree_root layer for SSZ in Lean 4

**The right design is a near-line-for-line port of remerkleable's `PairNode`/`RootNode` tree, with the cache stored as a structural field on each node and made opt-out by holding the value as a plain `T` instead of a `TreeBacked T`.** This buys you `O(depth)` updates with structural sharing on `BeaconState.validators` (~41 SHA-256 calls per validator mutation instead of ~2⁴¹), free correctness by construction (the cache is not on the proof path), and a clean equivalence story to your verified spec layer. The single most important invariant, that the *type* fixes the tree shape, not the contents, is what makes huge-but-empty SSZ Lists tractable: a 2⁴⁰-leaf list mostly consists of `RootNode`s pointing into a precomputed `ZERO_HASHES[d]` table.

The deeper lessons from prior art are that (1) ChainSafe and Lighthouse converged on this exact node shape after experimentation, (2) Nimbus's February 2025 mainnet fork was caused by *list-length* cache invalidation specifically, a bug class Lean's dependent types can make unrepresentable, (3) batched/deferred update layers (Lodestar's `ViewDU`, Lighthouse's Milhouse `with_updates_leaves`) deliver a larger speedup than the persistent tree alone, and (4) FBIP refcounting in Lean 4 already gives you the structural-sharing semantics you need without any explicit `Arc`. What follows is a concrete blueprint with code sketches, written assuming you are integrating this into the Approach B universe-of-SSZ-descriptions architecture from the prior research.

## 1. The remerkleable / ztyp design pattern

The architecture pivots on one observation: **a typed view (`Container`, `List`, `Vector`) is just a thin wrapper over an immutable `Node` tree, and `hash_tree_root` is one-line: `self.get_backing().merkle_root()`**.

The `Node` protocol in `remerkleable/tree.py` has only two concrete subclasses: `PairNode(left, right, root: Optional[Root])` for interior nodes, and `RootNode(root: Root)` for leaves and for any subtree summarized to its hash. There is no separate `ZeroNode` class. A "depth-`d` empty subtree" is simply `RootNode(zero_hashes[d])`, where `zero_hashes` is precomputed at module load via the recurrence `zero_hashes[d+1] = sha256(zero_hashes[d] || zero_hashes[d])` for `d ∈ [0, 100]`. Calling `merkle_root()` on a `RootNode` is **O(1)**, which is what makes a `List[Validator, 2**40]` with 1M populated entries representable: most of the tree is one `RootNode` per unfilled subtree, sharing the precomputed hash.

The cache lives in **one mutable slot per `PairNode`**: `root: Optional[Root]`, initialized to `None`. The body of `merkle_root` is

```python
def merkle_root(self) -> Root:
    if self.root is not None: return self.root
    self.root = merkle_hash(self.left.merkle_root(), self.right.merkle_root())
    return self.root
```

This is *morally const* mutation: the logical value never changes, only the cache fills in, and the operation is idempotent (same input → same hash) so even racing writers cannot produce a wrong observable value. ztyp does the same with explicit `Value Root` field on `PairNode` (no `sync.Once`, no atomic CAS, single-threaded usage is assumed). Lighthouse's Milhouse, ChainSafe's `persistent-merkle-tree`, and Teku's `tech.pegasys.teku.ssz.tree.BranchNode` all converge on this exact shape.

Updates work through a **`Link` closure**: `setter(target_gindex)` walks down the tree composing `rebind_left`/`rebind_right` calls into a single closure that, when applied to the new leaf, allocates exactly one new `PairNode` per level on the path and shares everything off-path by reference:

```python
def rebind_left(self, v):  return PairNode(v, self.right)   # self.right shared
def rebind_right(self, v): return PairNode(self.left, v)    # self.left  shared
```

`PairNode(v, self.right)` allocates a fresh node with `root=None`, so the cache is invalidated *only on the spine*, automatically. When `expand=True`, the setter replaces a `RootNode` mid-path with `PairNode(zero_node(d-1), zero_node(d-1))` to materialize an unfilled subtree for the first time. The cost: `validators[i] = v` on a 2⁴⁰-list is **41 fresh `PairNode` allocations, zero hash work**. Hashing happens lazily on the next `hash_tree_root()` call and walks only the dirty spine because every off-path node already has its `root` cached. Protolambda's published benchmark is **0.057 ms/op for one validator append** in ztyp.

**Typed views and the `_hook` callback.** `BackedView.__new__` stashes `_backing: Node` and `_hook: Optional[Callable[[BackedView], None]]`. When you read `state.validators`, `SubtreeView.get(i)` returns a child view passing `lambda v: self.set(i, v)` as the hook. When the child mutates, it calls its hook, which rebinds the parent's backing, which calls *its* hook, and so on up to the root. This is how mutation appears in-place in Python despite the underlying tree being immutable, and it is also why ChainSafe had to switch to `WeakRef` for parent links in Lodestar to let large states get GC'd when only a sub-view is held live.

**Mix-ins and packing.** A `List[T, N]` is *always* `PairNode(contents, length)` at gindices 2 and 3. The contents subtree has depth `contents_depth = ceil(log2(chunk_count))` where `chunk_count = ceil(N · sizeof(T) / 32)` for basic `T` (packed) and just `N` for composite `T`. Packing is reflected in tree shape, not at serialize time: a `List[uint64, 2**20]` has 2¹⁸ chunks (4 uint64/chunk), and `set(i, v)` reads chunk `i//4`, splices the i%4 sub-slot in via `backing_from_base(chunk, i % elems_per_chunk)`, and writes back. `Bitlist[N]` is the same with 256 bits per chunk and the trailing length-delimiter bit *stripped* before merkleization. `Vector` and `Bitvector` have **no length mix-in** and tree depth `ceil(log2(chunk_count))`. Containers have depth `ceil(log2(num_fields))` and never pack: each field gets its own chunk regardless of size. Unions mix in the selector at the top: `H(hash_tree_root(value), uint256_le(selector))`.

## 2. Translating the design to Lean 4

Lean 4's reference-counting runtime gives you all the structural-sharing semantics for free. Per Ullrich and de Moura's *Counting Immutable Beans* (IFL'19), every heap object carries an exact RC, and `{ node with field := v }` on an RC=1 value is compiled to an in-place destructive update; on an RC>1 value, it allocates a fresh constructor cell and bumps the RCs of unchanged children. **This is exactly the persistent-data-structure semantics remerkleable simulates manually in Python.** Lighthouse's Milhouse uses `Arc` for the same effect; in Lean you write nothing.

The recommended core type:

```lean
inductive Node : Type where
  | leaf : ByteArray → Node                   -- 32 bytes; leaf or summary
  | pair : Node → Node → Option ByteArray → Node
deriving Inhabited
```

The `Option ByteArray` cache field is the direct analogue of remerkleable's `root: Optional[Root]`. Lean compiles two-constructor inductives to discriminated heap blocks; a `pair` cell is a 3-pointer record with O(1) tag dispatch. This is **exactly the pattern `Lean.Expr` uses internally**: every `Expr` carries an `Expr.Data` field with a 64-bit cached hash, mixed in via `mixHash` at construction. The Lean compiler proves by example that this is idiomatic and fast.

Three design alternatives, ranked:

**(A) Cache field directly on the inductive (recommended).** `Option ByteArray` per `pair`. Simple, total, structurally recursive, integrates with `simp`/`decide`. The slight cost is that pattern matches in proofs need to ignore the cache field, easy with a smart accessor `Node.cached`.

**(B) `Thunk ByteArray` instead of `Option ByteArray`.** `Thunk α` is a Lean primitive runtime object; its first `get` evaluates and the result is memoized in the thunk header, thread-safely. Slightly more elegant ("the cache is a thunk of the merkle root") but adds an indirection per node and complicates equational reasoning in proofs.

**(C) External `HashMap`-keyed memoization.** A mutable `HashMap (PtrIdentity Node) ByteArray` in `ST`. This is what Lighthouse's Gen-1 `cached_tree_hash` did with side caches and is what bit Nimbus in February 2025: cache invalidation across structural mutation is the bug class. **Don't do this for the primary cache**; it loses the "modify the tree → cache evicts on the spine for free" property of approach (A).

The integration with the SSZType-indexed types from Approach B has a clean shape:

```lean
-- Layer 1: pure spec (verified)
inductive SSZType where | uint : Nat → SSZType | bool : SSZType | …
def interp : SSZType → Type := …
def hashTreeRoot : (s : SSZType) → interp s → ByteArray := …  -- spec, slow

-- Layer 3: typeclass + iso
class SSZRepr (T : Type) where
  shape : SSZType
  toSSZ : T → interp shape
  fromSSZ : interp shape → T
  isoLeft  : ∀ x, fromSSZ (toSSZ x) = x
  isoRight : ∀ y, toSSZ (fromSSZ y) = y

-- Layer 4: tree-backed parallel representation (this layer)
structure TreeBacked (T : Type) [SSZRepr T] where
  /-- Cached value-level view; logically equal to `fromSSZ (decodeTree tree)` -/
  view  : T
  /-- The canonical Merkle backing; logically equal to `encodeTree (toSSZ view)` -/
  tree  : Node
  /-- Coherence is an invariant, not a propositional field; checked in tests -/
```

The coherence between `view` and `tree` is asserted at construction by smart constructors and never violated by the API; **you do not prove it as a Lean proposition** because the user explicitly does not want formal verification of the cache layer. This is the same stance as Lighthouse's `CachedTreeHash` (cache as a side-channel) but with the cache embedded in the value, like ssz_rs's `Cell<Option<Node>>` pattern. The opt-out is structural: hold a plain `T` with a `SSZRepr T` instance and call `SSZ.hashTreeRoot` (the spec); switch to `TreeBacked T` when you want the cached fast path.

## 3. Where exactly hashes get cached

Three layers of cache, in order of importance:

**Per-Node cache (mandatory).** Every `Node.pair` carries `Option ByteArray`. This is the workhorse. Filled lazily on first `merkleRoot` call; invalidated automatically on update because a new `pair` allocation has `none`.

**Zero-hash table (mandatory, precomputed).** A top-level `def`:

```lean
def ZERO_HASHES : Vector ByteArray 65 := Id.run do
  let mut v := Vector.replicate 65 (ByteArray.mk (Array.replicate 32 0))
  for i in [0:64] do
    v := v.set ⟨i+1, by omega⟩ (sha256Combine v[i] v[i])
  return v

def zeroNode (d : Nat) (h : d ≤ 64) : Node := .leaf ZERO_HASHES[d]
```

Lean evaluates this once at module load (or, with `@[reducible]` and small `d`, at compile time). `merkleRoot (zeroNode d) = ZERO_HASHES[d]` is O(1). This single optimization is the difference between "tractable" and "impossible" for `List[Validator, 2**40]`. Every implementation surveyed (remerkleable, ztyp, Lighthouse, ChainSafe, Teku) precomputes this table; ChainSafe also memoizes the `RootNode` wrappers, ztyp does not.

**Per-typed-value cache (optional, useful).** A `BeaconBlockHeader` whose fields are immutable after signing has a fixed root forever; a `cachePermanentRootStruct` flag (ChainSafe's term) lets you store the computed root once per *value*, skipping even the per-node walk. In Lean: `structure BeaconBlockHeader extends … where rootCache : Option ByteArray := none`, populated by the constructor. The user's proof obligations are unchanged because the spec `hashTreeRoot` is a separate function.

**The mix-in question: cache the raw merkleization separately?** Remerkleable does **not**. The list backing is `PairNode(contents, length)`, and the per-`PairNode` cache at the *list root* automatically gives you `H(merkleize(contents), uint256_le(len))`. The contents subtree's own cache gives you the unmixed root. So the answer falls out of representing the mix-in *as part of the tree shape*: gindex 2 holds contents, gindex 3 holds the length leaf. This is the same trick for unions (selector at gindex 3). Don't invent a separate cache slot; let the tree shape encode the mix-in and the `Node` cache handles it for free.

**Partial population of large Lists.** `validators: List[Validator, 2**40]` populated to length 1M holds: ~1M `Validator`-rooted leaves, ~20 levels of real `PairNode`s above them (since `2^20 > 1M`), and at each of those 20 levels a single `pair` whose right child is `zeroNode(40-k)` for the appropriate depth `k`. Above level 20, every level has both children equal to the same `zeroNode(d)` (sharing one heap block). Total tree size: `O(populated_count + depth)`, not `O(2^40)`.

## 4. Cache invalidation under immutable update

In the immutable world, update is a function `set : (i : Nat) → α → TreeBacked T → TreeBacked T` that returns a fresh value. Because Lean's RC runtime in-place-mutates RC=1 cells, the *physical* cost is exactly remerkleable's: one new `pair` allocation per level on the path, with everything off-path shared by pointer.

```lean
/-- Generalized index navigation: bits of `g` after the leading 1 bit
    encode L (0) / R (1) descent from the root. -/
def gindexBits (g : Nat) : List Bool := …  -- strip leading 1, MSB-first

/-- Update the leaf at `gindex` to `newLeaf`, sharing all off-path subtrees
    with the input. The cache fields on the new spine are `none`. -/
def Node.setAt : Node → (gindex : Nat) → Node → Node
  | n, 1, newLeaf => newLeaf
  | .pair l r _, g, newLeaf =>
      let bits := gindexBits g
      match bits with
      | false :: _ => .pair (l.setAt (g >>> 1 ||| 1 <<< (gindexBits g).length.pred) newLeaf) r none
      | true  :: _ => .pair l (r.setAt _ newLeaf) none
      | []         => newLeaf
  | .leaf _, g, newLeaf =>
      -- "expand" branch: we hit a summary mid-path. Replace with a fresh PairNode
      -- whose children are zeroNode(d-1) and recurse.
      let d := (Nat.log2 g)
      (Node.pair (zeroNode (d-1) (by omega)) (zeroNode (d-1) (by omega)) none).setAt g newLeaf
  termination_by n g _ => g
```

(The exact recursion needs a cleaner formulation, tracking the gindex bit-stream as an explicit `List Bool` argument and recursing on its length. Lean accepts that as structural recursion on the list; no `partial`. The above is sketch-quality.)

The key property: **the only `pair` nodes whose cache field is `none` after `setAt` are exactly those on the path from root to the changed leaf**. Every other `pair` is shared by reference with the old tree and retains its cached root. The next `merkleRoot` call walks only the dirty spine, `O(depth)` SHA-256 calls, and fills in the new caches in returned `pair` cells.

**Lazy vs eager cache fill.** Remerkleable, ztyp, Milhouse, and ChainSafe are all **lazy**: caches are filled on demand. The right reason is that updates happen in batches (one per slot in fork choice) and most intermediate states never have their root requested. ChainSafe's `ViewDU` takes this further with a *deferred-update overlay*: pending changes accumulate in an ordered map keyed by index, and `commit()` does one downward walk rebinding all of them at once. This is the largest performance lever in the entire stack. Lighthouse's Milhouse `with_updates_leaves` (`tree.rs:157-236`) and ChainSafe's `ViewDU.commit` both report dramatic speedups vs. immediate per-update rebinding. Recommend: implement immediate `set` first, add a `ViewDU`-style deferred layer in a follow-up.

In Lean, lazy cache fill has a subtle wrinkle: because Lean is strict, "lazy" here means "compute on first `merkleRoot` call and return a *new* `Node` with the cache populated". Concretely:

```lean
def Node.merkleRootWithCache : Node → ByteArray × Node
  | .leaf b              => (b, .leaf b)
  | .pair l r (some c)   => (c, .pair l r (some c))
  | .pair l r none       =>
      let (lh, l') := l.merkleRootWithCache
      let (rh, r') := r.merkleRootWithCache
      let h := sha256Combine lh rh
      (h, .pair l' r' (some h))
```

The caller threads the new `Node` back into the enclosing structure. Because `TreeBacked` is itself immutable, `def hashTreeRoot (t : TreeBacked T) : ByteArray × TreeBacked T` returns both the hash and a new `TreeBacked` with caches filled. If the caller discards the new tree, the cache work is forfeit; if they keep it (as a beacon-state cache normally would), subsequent calls hit the cache. This is the **explicit-state-passing** version of remerkleable's morally-const mutation, and it composes cleanly with Lean's verification story.

A pragmatic alternative is to use a `Thunk ByteArray` cache slot or a `ST.Ref` keyed by node-pointer in an internal hidden state. Both are acceptable; the explicit-state version is the most transparent for verification.

## 5. The opt-out and spec-equivalence story

Two complementary mechanisms, both worth providing:

**Mechanism 1: structural opt-out.** The user holds their data as plain `T` (e.g. `BeaconState` defined as a Lean record), calls `SSZ.hashTreeRoot a`, and gets the spec-defined recomputation by direct recursion on `SSZType`. To opt *in*, they call `TreeBacked.ofValue a : TreeBacked T` once, then operate on the tree-backed value. **There is no global flag; opt-out is just "use a different type"**. This is ssz_rs's stance and is the cleanest way to isolate the cached fast path.

**Mechanism 2: `@[implemented_by]` on the `hashTreeRoot` spec.** Following Lean core's pattern (`USize.repr` → `lean_string_of_usize`, `Array.usize` → `lean_array_usize`):

```lean
-- Spec (Layer 1, verified)
def SSZ.hashTreeRoot : (s : SSZType) → interp s → ByteArray := …

-- Optimized (Layer 4)
def SSZ.hashTreeRootCached [SSZRepr T] (t : TreeBacked T) : ByteArray :=
  (Node.merkleRootWithCache t.tree).1

-- Optionally swap the spec for the cached version at runtime
@[implemented_by SSZ.hashTreeRoot.fast]
def SSZ.hashTreeRoot' (s : SSZType) (v : interp s) : ByteArray := SSZ.hashTreeRoot s v
```

`@[implemented_by]` is the direct mechanism (Selsam et al., *Sealing Pointer-Based Optimizations Behind Pure Functions*, arXiv:2003.01685): the kernel sees the spec body for proof reduction; the compiler emits a call to the fast version for `#eval` and compiled binaries. **Equivalence is asserted, not proved**, and the user explicitly accepts that. To upgrade the assertion to a kernel-checked obligation later, switch to `@[csimp] theorem hashTreeRoot_eq_fast : SSZ.hashTreeRoot = SSZ.hashTreeRoot.fast := …` and supply a proof.

**Provide both APIs.** A cleaner public surface:

```lean
namespace SSZ
  /-- Pure, slow, formally verified. The reference. -/
  def hashTreeRoot : [SSZRepr T] → T → ByteArray

  /-- Tree-backed, cached, asserted-equivalent. Fast path. -/
  def hashTreeRootCached : [SSZRepr T] → TreeBacked T → ByteArray
end SSZ
```

The user's downstream code chooses representation per use site. A property test `∀ t : TreeBacked T, hashTreeRootCached t = hashTreeRoot t.view` run via `Plausible`/`SlimCheck` against the SSZ Generic Test Suite is the recommended ongoing safety net. Lighthouse runs the same test against `Vec<T>` reference values via AFL+ fuzzing.

## 6. Concrete Lean 4 code sketches

A fuller skeleton, filling in the key pieces:

```lean
namespace SSZ.Tree

abbrev Hash32 := ByteArray  -- invariant: size = 32

@[extern "lean_sha256_combine"]
opaque sha256Combine (left right : @& ByteArray) : ByteArray

inductive Node where
  | leaf : Hash32 → Node
  | pair : Node → Node → Option Hash32 → Node
deriving Inhabited

@[inline] def Node.cached : Node → Option Hash32
  | .leaf h            => some h
  | .pair _ _ c        => c

/-- Precomputed zero-subtree hashes for depths 0..64. -/
def ZERO_HASHES : Vector Hash32 65 := Id.run do
  let mut v := Vector.replicate 65 (ByteArray.mk (Array.replicate 32 0))
  for h : i in [0:64] do
    v := v.set ⟨i+1, by omega⟩ (sha256Combine v[i] v[i])
  pure v

@[inline] def zeroLeaf (d : Nat) (h : d ≤ 64 := by decide) : Node :=
  .leaf ZERO_HASHES[d]

/-- Pure traversal, returning hash and a new Node with caches filled on the
    walked spine. Structurally recursive on `Node`. -/
def Node.merkleRootWithCache : Node → Hash32 × Node
  | .leaf h            => (h, .leaf h)
  | .pair l r (some c) => (c, .pair l r (some c))
  | .pair l r none     =>
      let (lh, l') := l.merkleRootWithCache
      let (rh, r') := r.merkleRootWithCache
      let h := sha256Combine lh rh
      (h, .pair l' r' (some h))

@[inline] def Node.merkleRoot (n : Node) : Hash32 := (n.merkleRootWithCache).1

/-- Build a balanced tree from a list of leaf hashes, padding right with
    zero-subtree leaves up to depth `d`. -/
def Node.ofLeaves (leaves : Array Hash32) (d : Nat) : Node :=
  go d leaves 0 (1 <<< d)
where
  go : (depth : Nat) → Array Hash32 → (lo hi : Nat) → Node
    | 0,    arr, lo, _  => .leaf (arr.getD lo ZERO_HASHES[0])
    | d+1,  arr, lo, hi =>
        let mid := (lo + hi) / 2
        if mid ≥ arr.size then
          -- entire right side is zero
          .pair (go d arr lo mid) (zeroLeaf d) none
        else
          .pair (go d arr lo mid) (go d arr mid hi) none
  termination_by depth _ _ _ => depth

/-- Update one leaf via gindex; structural-share off-path subtrees. -/
partial def Node.setAt : Node → (g : Nat) → Node → Node
  | _,            1, newLeaf => newLeaf
  | .pair l r _,  g, newLeaf =>
      let depth   := Nat.log2 g
      let bit     := (g >>> (depth - 1)) &&& 1
      let gChild  := g ^^^ (1 <<< depth) ||| (1 <<< (depth - 1))
      if bit = 0 then .pair (l.setAt gChild newLeaf) r none
      else            .pair l (r.setAt gChild newLeaf) none
  | .leaf _,      g, newLeaf =>
      -- expand summarized subtree
      let d := Nat.log2 g
      (Node.pair (zeroLeaf (d-1)) (zeroLeaf (d-1)) none).setAt g newLeaf

end SSZ.Tree

namespace SSZ.TreeBacked

structure List (α : Type) (limit : Nat) [SSZRepr α] where
  data       : Array α
  contentsT  : Tree.Node
  /-- root = pair contentsT (leaf (uint256_le data.size)) -/
  rootT      : Tree.Node

@[inline] def List.length (l : List α n) : Nat := l.data.size

@[inline] def List.hashTreeRoot (l : List α n) : Tree.Hash32 :=
  l.rootT.merkleRoot

/-- Set element i, structurally sharing all unchanged subtrees. -/
def List.set [SSZRepr α] (l : List α n) (i : Fin l.data.size) (v : α) : List α n :=
  let leafHash := SSZ.hashTreeRoot v
  let depth := contentsDepth (SSZRepr.shape α) n
  let g := (1 <<< depth) ||| i.val
  let newContents := l.contentsT.setAt g (.leaf leafHash)
  let lenLeaf := .leaf (uint256LE l.data.size)
  let newRoot := .pair newContents lenLeaf none
  { data      := l.data.set i v
    contentsT := newContents
    rootT     := newRoot }

def List.append [SSZRepr α] (l : List α n) (v : α) (h : l.length < n) : List α n :=
  let leafHash := SSZ.hashTreeRoot v
  let depth := contentsDepth (SSZRepr.shape α) n
  let g := (1 <<< depth) ||| l.data.size
  let newContents := l.contentsT.setAt g (.leaf leafHash)
  let lenLeaf := .leaf (uint256LE (l.data.size + 1))
  { data      := l.data.push v
    contentsT := newContents
    rootT     := .pair newContents lenLeaf none }

end SSZ.TreeBacked
```

Three Lean-specific notes on the sketch. **Termination**: `merkleRootWithCache` is structurally recursive on `Node` because `l` and `r` are immediate subterms, so Lean accepts it without `termination_by`. `setAt` is harder because the gindex shrinks but in a non-obvious way; the cleanest fix is to recurse on an explicit `List Bool` of remaining bits, which is structurally decreasing. Use `partial def` only as a stopgap; `partial` makes the function opaque to `simp`/`decide` and breaks any later proof attempts. **Specialization**: mark `List.set` and `List.append` `@[specialize]` so that the typeclass dictionary for `SSZRepr α` is monomorphized at each instantiation (e.g. for `α = Validator`). Mark small projections (`Node.cached`, `List.length`) `@[inline]`. **ByteArray**: `Hash32 = ByteArray` is the right choice, since `ByteArray` is backed by `lean_sarray_object` (packed C buffer, FBIP destructive update), which gives you C-array performance for hash equality and SHA-256 input prep.

## 7. Other performance opportunities

The cache layer above is the foundation; once it works, several orthogonal optimizations can stack on top, ranked by impact-to-effort ratio.

**Batched / deferred updates (largest single win).** ChainSafe's `ViewDU` and Lighthouse Milhouse's `with_updates_leaves` accumulate pending mutations in an ordered map (keyed by index, ordered so subtree ranges can be skipped wholesale) and commit in one downward walk. Per-update spine work drops from `O(log N)` per update to amortized `O((log N) · changed / total)`. For an epoch transition that touches half the validators, this is ~20× over per-update rebinding. Implement as `structure ListDU α n` over `TreeBacked.List` plus a `commit : ListDU → TreeBacked.List` step.

**FFI to a fast SHA-256.** Lean has no built-in SHA-256. Bind one via `@[extern]` to OpenSSL's `SHA256_*`, libsodium, or, for serious wins, `gohashtree` / `noloader/SHA-Intrinsics` which use Intel SHA-NI or ARMv8 Crypto Extensions. ARMv8 SHA gets ~5–7× over generic. The Lake configuration is straightforward: `extern_lib sha256Shim` plus `moreLinkArgs := #["-lcrypto"]`. The `tydeu/lean4-alloy` package lets you embed C inline.

**Batched SHA-256 (gohashtree-style).** SHA-NI / AVX-512 can hash 4–8 sibling pairs in parallel. At the bottom level of a Merkle tree this is huge: 1024 contiguous chunks → 512 parallel `sha256(a||b)` operations → ~4× speedup with SHA-NI VAES, ~8× with full AVX-512. Plumbing requires a batch interface `sha256Batch : Array (ByteArray × ByteArray) → Array ByteArray` and a tree-traversal that collects siblings into batches before calling.

**Hash-consing of zero subtrees and identical genesis state.** Beyond `ZERO_HASHES`, hash-cons identical *populated* subtrees, e.g. the all-zero `inactivity_scores` field of a fresh validator. ChainSafe and Teku both report this as a measurable win. In Lean: a `HashMap (Hash32) Node` weak-cache, populated on construction. Cleanly orthogonal to the cache layer.

**Lazy chunk packing for basic-type lists.** `List[uint64, N]` packs 4 uint64 per chunk. Naively each set rebuilds the full chunk; with an "unpacked overlay" (4 slots per chunk, lazily packed on `merkleRoot` request) you avoid repacking on consecutive sets within the same chunk. Remerkleable does the packing eagerly via `backing_from_base`; for write-heavy workloads, lazy packing wins.

**`BitVec` SIMD for bitlist/bitvector packing.** Lean 4's `BitVec` gets compile-time SIMD via the LLVM backend in some configurations, and the standard library is gradually adding intrinsics. Use `BitVec 256` for chunk-level bit operations.

**Caching serialized form alongside the hash.** A `BeaconBlock`'s SSZ-serialized bytes are recomputed on every gossip; cache them on the value alongside the root cache. Same `Option ByteArray` field pattern.

**Profiling-guided specialization.** `@[specialize]` the SSZType interpreter for the concrete shapes (`BeaconState`, `Validator`, `BeaconBlockBody`). Lean monomorphizes the typeclass dictionary at each call site, eliminating the indirection. Add `@[inline]` to small smart constructors. Run a benchmark against ChainSafe's TS or Lighthouse to identify hot paths.

**Persistent tree as canonical state representation.** The big win Lighthouse reported with Milhouse / tree-states (Aug 2024): once `BeaconState` *is* its persistent tree, fork-choice can keep ~128 hot states in the RAM budget that previously held 4. State copy goes from O(n) to O(1). For a Lean 4 PSE prototype, this is the architectural payoff that justifies the entire layer.

**Generalized-index access for partial views and Merkle proofs.** The same gindex navigation that supports `setAt` gives you `getProof : Node → Gindex → Array Hash32` essentially for free: collect the sibling hashes along the descent. This is how light-client proofs get generated. Specifying the proof API early shapes the rest of the design (e.g., it pushes you to keep gindices at the surface).

## 8. Prior art map

| Library | Language | Node shape | Cache mechanism | Sharing | Notable |
|---|---|---|---|---|---|
| **remerkleable** | Python | `PairNode(l,r,root?)` + `RootNode(root)` | `Optional[Root]` field, lazy-mutated | Python refs | Reference design; `_hook` callback for view-side mutation |
| **ztyp** | Go | `PairNode{Value, L, R}`; `*Root` doubles as leaf | Plain mutation of `Value` field, no `sync.Once` | Go pointers | Pluggable `HashFn`, ~0.057 ms/op append on 2⁴⁰ list |
| **persistent-merkle-tree** (ChainSafe) | TS | `BranchNode(l,r,_root?)` + `LeafNode` | Lazy `_root` field | JS refs (now `WeakRef` for parent links) | Memoized `zeroNode(d)` singletons; `View` vs `ViewDU` two-tier |
| **@chainsafe/ssz ViewDU** | TS | Same + ordered pending-update map | Per-field/per-index pending Maps committed atomically | JS refs | Largest perf lever; commit() walks tree once for all changes |
| **Lighthouse `cached_tree_hash`** (Gen 1) | Rust | Side-cache flat array | Two-phase dirty propagation, cache held alongside value | None (cache is separate) | Cache invalidation is caller's responsibility, historically buggy |
| **Lighthouse Milhouse / tree-states** (Gen 2, 2024) | Rust | `Arc<BranchNode>` persistent tree | Hashes attached to each intermediary node | `Arc::clone` | Vector/List only; rebasing on disk-load; 128 states in old 4-state budget |
| **Teku `ssz.tree`** | Java | `BranchNode`, `LazyBranchNode`, `LeafNode`, `SszSuperNode` | Final fields + GC sharing | JVM refs | `SszSuperNode` flattens fixed-size primitive subtrees; PR #3426 ~3× speedup |
| **Nimbus nim-ssz-serialization** | Nim | Array-backed value + per-field dirty bitmap | Side-cache, dirty flags | None | **List length-change bug caused mainnet fork in Feb 2025** (issue #150) |
| **ssz_rs `Merkleized`** | Rust | In-place memo on the value | `Cell<Option<Node>>` field | None | Light-client oriented; no partial-update benefit |
| **EVMYulLean** | Lean 4 | n/a (EVM only) | n/a | n/a | Reference for Lean 4 Ethereum project organization |

**Academic prior art.** Dahlberg et al. (eprint 2016/683, *Efficient Sparse Merkle Trees*) formalizes the zero-subtree caching identity. The Diem Jellyfish Merkle Tree's `TreeCache`/`FrozenTreeCache` (`diem/storage/jellyfish-merkle/src/tree_cache/mod.rs`) is the cleanest model for batched-commit caching and is a good template if you go the `ViewDU` route. CoW B-trees / multiversion B-trees (Becker; Brodal et al.) are the classical theory underneath Milhouse-style rebasing.

## What to build first

Three weeks of focused work, in order. Week 1: `Node` inductive with `Option ByteArray` cache, `ZERO_HASHES` table, `merkleRootWithCache`, `setAt`, FFI to OpenSSL SHA-256 via `lean4-alloy`. Test against the SSZ Generic Test Suite. Week 2: `TreeBacked.List`, `TreeBacked.Vector`, `TreeBacked.Container` with `@[specialize]` on the polymorphic helpers; smart constructors maintaining the value/tree coherence invariant; `@[implemented_by]` glue to the verified `SSZ.hashTreeRoot` spec. Week 3: integrate `BeaconState` and `Validator`; benchmark validator-update micro and full epoch transition against Lighthouse's published numbers; property-test against the Layer-1 spec using `Plausible`. Defer to subsequent work: deferred-update overlay (`ViewDU`), batched SHA-256, hash-consing, persistent-tree-as-canonical-state, Merkle proof API.

The single highest-risk item is the gindex arithmetic in `setAt`: get this wrong and you silently produce wrong roots on partial updates. Mitigate by structuring the recursion on a `List Bool` of bits (computed once from the gindex) rather than bit-twiddling on `Nat`, and by property-testing equivalence against a slow `merkleize ∘ asLeafArray` reference on every commit. This is exactly the Nimbus failure mode, and Lean's type system gives you the tools to make it unrepresentable rather than merely tested.