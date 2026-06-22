import SizzLean.Hasher.Class
import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.Constants
import SizzLean.Spec.Serialize

/-!
# `SizzLean.Spec.HashTreeRoot`: total SSZ Merkleization

Implements the Merkle-root side of consensus-specs *§Merkleization*
(`simple-serialize.md`): a total recursion on `SSZType` mapping a
value of `s.interp` to its 32-byte `hash_tree_root` (HTR).

Parameterised by `[Hasher H]` (Lean's instance-implicit binder,
requesting a `Hasher` typeclass instance at the call site). Per
ARCHITECTURE.md §3.3 / §9 the FFI SHA-256 shim and the pure-Lean
`Sha256Spec` are the available instances; concrete roots evaluate
through either one.

## Spec-side terms (annotated on first appearance)

* *chunk*: a 32-byte (`BYTES_PER_CHUNK`) leaf in the Merkle tree.
  Basic-type roots are right-padded to a chunk and the chunk *is* the
  root; composite types pack their data into a sequence of chunks
  before merkleizing.
* *merkleization*: bottom-up `combine`-folding of chunks into a
  binary tree, padded with zero subtrees to the next power-of-two leaf
  count (the "limit", determined by the schema not the data).
* *zero hashes*: the precomputed `combine`-tower over an all-zero
  leaf: `Z[0] = 32·0x00`, `Z[d+1] = combine Z[d] Z[d]`. `Z[d]` is the
  root of an all-zero subtree of depth `d`. We materialise these
  abstractly here (`ZERO_HASHES_SPEC`); the cache layer's
  `Cache/MerkleTree/Zero.lean` produces concrete bytes once a
  `Hasher` instance exists.
* *mix-in length*: for variable-length collections (`list`,
  `bitlist`) the body root is combined with a `uint64`-LE encoding
  of the *actual* element/bit count right-padded to a chunk:
  `combine bodyRoot (uint64ToChunk n)`.

## Why a `mutual` block (annotated where first relevant elsewhere)

Same shape `Spec/Interp.lean` and `Spec/Serialize.lean` already use:
the recursion descends into `List SSZType` (container fields), and
Lean 4.29.1's structural-recursion checker rejects passing
`hashTreeRoot` itself as a higher-order argument to `List.map`. The
fix is to inline each list traversal as a mutually-recursive helper
that consumes its list cons-by-cons. See `Spec/Interp.lean`'s
preamble for the long-form explanation.

## `interp`-reduction quirk

Per `Spec/Serialize.lean`'s `uintN`/`bool` arms: a dependent match
arm whose body uses the value `x : s.interp` may need a local
`let x' : ConcreteType := x` to force `s.interp`'s reduction at the
arm before further unfolding. The same idiom appears below.

## `uintN` width coverage

`uintN n` is implemented for `n ∈ {8, 16, 32, 64, 128, 256}`,
the widths used by consensus-spec types Phase 0 through Gloas.
Other `n` fall through to a 32-byte zero chunk; the `BitVec n`
fallback collides with the same dependent-match limitation
`Serialize.lean` hits, and no consensus type exercises those
widths, so the totality-preserving stub is sufficient.
-/

set_option autoImplicit false
-- Same reason as `Spec/Deserialize.lean`: the 17-arm dependent match
-- in `SSZType.hashTreeRoot` (each arm refining `s.interp` against
-- `interp`'s own 17-case recursion) drives the elaborator past the
-- 200k-heartbeat default. Bumped here, not globally, so only this
-- file pays the cost.
set_option maxHeartbeats 5000000

namespace SizzLean.Spec


open SizzLean

/-! ### Chunk primitives

Per spec *§Merkleization*: every Merkle leaf is a 32-byte buffer.
Basic-type encodings are right-padded to that width; composite
encodings are split into 32-byte chunks (also right-padding the last
chunk if needed). -/

/-- A 32-byte all-zero `ByteArray`. The base of the zero-hashes tower
and the right-padding source for short chunks. Built by repeated
`push` so the result is a concrete `ByteArray` literal at compile
time. -/
def zero32 : ByteArray :=
  let rec build : Nat → ByteArray → ByteArray
    | 0,     acc => acc
    | k + 1, acc => build k (acc.push 0)
  build BYTES_PER_CHUNK ByteArray.empty

/-- Right-pad a `ByteArray` with `0x00` to length `BYTES_PER_CHUNK`
(truncating if it is already longer; callers ensure ≤ 32 in practice).
The single-chunk root rule for basic types is exactly this padding. -/
def padToChunk (b : ByteArray) : ByteArray :=
  let n := b.size
  if n ≥ BYTES_PER_CHUNK then b
  else
    let rec go : Nat → ByteArray → ByteArray
      | 0,     acc => acc
      | k + 1, acc => go k (acc.push 0)
    go (BYTES_PER_CHUNK - n) b

/-- Encode a `Nat` as a 32-byte little-endian chunk. Used by both
`mixInLength` (length is a `uint64` per spec) and `mixInSelector`
(selector is a `uint8` on the wire but mixed in as `uint64`-in-chunk
for the same chunk-aligned tree step). Truncates beyond 32 bytes;
SSZ length / selector values fit in 8 bytes by spec. -/
def natToChunk (n : Nat) : ByteArray :=
  let rec go : Nat → Nat → ByteArray → ByteArray
    | 0,     _, acc => acc
    | k + 1, m, acc => go k (m / 256) (acc.push (Nat.toUInt8 (m % 256)))
  go BYTES_PER_CHUNK n .empty

/-- Split a `ByteArray` into a list of 32-byte chunks, right-padding
the final chunk with zeros if its length is not a multiple of
`BYTES_PER_CHUNK`. Empty input yields the empty list. The result is
the chunk leaves of the data's Merkleization in *offset-ascending*
order: chunk 0 = bytes `[0, 32)`, chunk 1 = bytes `[32, 64)`, etc.

The recursion descends on `k` from `total` down to `0`, prepending
each chunk. Counting *down* in the recursion while prepending yields
ascending order naturally (no final reverse needed): step `k=N`
prepends the *highest-offset* chunk, then `k=N-1` prepends the
next-lower offset chunk in front, and so on, so the accumulator
finishes with chunk 0 at the head. -/
def chunkify (b : ByteArray) : List ByteArray :=
  let rec go : Nat → List ByteArray → List ByteArray
    | 0,     acc => acc
    | k + 1, acc =>
        let off := k * BYTES_PER_CHUNK
        let raw := b.extract off (off + BYTES_PER_CHUNK)
        go k (padToChunk raw :: acc)
  let total := (b.size + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK
  if total = 0 then [] else go total []

/-! ### Zero-hashes tower

Per spec *§Merkleization, Helpers*: an all-zero subtree of depth
`d` has root `Z[d]` defined recursively. `ZERO_HASHES_SPEC` exposes
this as a Lean `Vector` of length 65, depth `0..64`, sufficient for
any Merkle tree the spec admits given `MAX_LENGTH = 2^32` chunks
plus mix-ins.

Defined abstractly over `[Hasher H]`: type-checking confirms totality
without picking a concrete instance. The cache layer's
`Cache/MerkleTree/Zero.lean` materialises the 65 concrete byte
values once a hasher instance is in scope. -/

/-- Zero-hash at depth `d`: root of an all-zero subtree of depth `d`.
`zero32` at the leaves; `Hasher.combine` at every interior step.

The `(H := H)` named-argument form is required because `Hasher`'s
parameter `H` is a phantom *tag* type. It does not appear in the
types of `hash` or `combine`, so instance synthesis cannot recover
it from the call's value arguments. `(H := H)` supplies `H`
explicitly; the `[Hasher H]` instance binder then resolves. -/
private def zeroHashAt (H : Type) [Hasher H] : Nat → ByteArray
  | 0     => zero32
  | d + 1 =>
      let z : ByteArray := zeroHashAt H d
      Hasher.combine (H := H) z z

/-- The depth-indexed zero-hashes table, depth 0 through 64.
`Vector.ofFn` (Lean core ≥ 4.10) builds a length-indexed `Vector`
from a function `Fin n → α`; here it materialises the 65-entry
tower. Abstract over `[Hasher H]`; no concrete instance required at
declaration time.

The lambda's parameter type `Fin 65` is inferred from the result
type `Vector ByteArray 65`. `Vector.ofFn`'s signature is
`(Fin n → α) → Vector α n`, and Lean unifies `n` with `65` from the
expected return. `i.val : Nat` is the index projection used to
recurse into `zeroHashAt`. -/
def ZERO_HASHES_SPEC (H : Type) [Hasher H] : Vector ByteArray 65 :=
  Vector.ofFn (fun (i : Fin 65) => zeroHashAt H i.val)

/-! ### Generic merkleization tree

`merkleize chunks depth` builds a balanced binary Merkle tree of
exactly `2 ^ depth` leaves, taking the leading `chunks` as the data
leaves and padding the remainder with zero subtrees of the
appropriate depth. The result is the 32-byte root.

The depth argument (rather than a leaf-count argument) lets us
short-circuit the all-zero suffix via `ZERO_HASHES_SPEC` instead of
materialising the padding explicitly. -/

/-- Look up `ZERO_HASHES[d]` defensively (clamps `d > 64` to the
deepest entry, sufficient because SSZ's `MAX_LENGTH = 2^32` keeps
us within the 65-entry table). -/
private def zeroHashAtClamped (H : Type) [Hasher H] (d : Nat) : ByteArray :=
  if h : d < 65 then (ZERO_HASHES_SPEC H).get ⟨d, h⟩ else zero32

/-- Pair adjacent chunks at tree level `lvl`, using `ZERO_HASHES[lvl]`
as the right sibling for an odd-length tail. The level argument is
load-bearing for correctness: at level `k`, the phantom right
sibling of a lone-tail interior node is an all-zero subtree of
depth `k`, whose root is `ZERO_HASHES[k]`, *not* `zero32` (which
would be wrong for `k > 0`).

The implementation is the tail-recursive accumulator pattern
(`combineLayerAtAux` builds the result in reverse, the outer
`combineLayerAt` reverses once at the end). The natural cons-and-
recurse spelling

```
| x :: y :: rs => Hasher.combine (H := H) x y :: combineLayerAt H lvl rs
```

is non-tail-recursive, the recursive call is the *tail* of a
`cons`, so each step pushes a fresh stack frame holding `combine x
y` until the list bottoms out. For a `ByteVector[BYTES_PER_BLOB]`
(131072 bytes ⇒ 4096 chunks) the first layer descends 2048 frames
deep, which overflows the OS-default 8 MB stack on `BlobSidecar`
mainnet vectors. The accumulator form keeps the stack flat at the
cost of one extra `List.reverse` per layer, `O(n)` time, `O(1)`
stack. -/
private def combineLayerAtAux (H : Type) [Hasher H] (lvl : Nat) :
    List ByteArray → List ByteArray → List ByteArray
  | [],           acc => acc.reverse
  | [x],          acc =>
      (Hasher.combine (H := H) x (zeroHashAtClamped H lvl) :: acc).reverse
  | x :: y :: rs, acc =>
      combineLayerAtAux H lvl rs (Hasher.combine (H := H) x y :: acc)

private def combineLayerAt (H : Type) [Hasher H] (lvl : Nat)
    (cs : List ByteArray) : List ByteArray :=
  combineLayerAtAux H lvl cs []

/-- Promote a single hash up through `remaining` levels of zero
subtrees: each level pairs with `ZERO_HASHES[startLvl + k]` on the
right. Used when the chunk list has reduced to a single item but
the target depth hasn't been reached. -/
private def promoteThroughZeros (H : Type) [Hasher H] :
    (current : ByteArray) → (startLvl : Nat) → (remaining : Nat) → ByteArray
  | c, _,        0     => c
  | c, startLvl, k + 1 =>
      promoteThroughZeros H
        (Hasher.combine (H := H) c (zeroHashAtClamped H startLvl))
        (startLvl + 1) k

/-- Build the Merkle root of a balanced binary tree of `2^depth`
leaves. `chunks` are the *real* left-aligned leaves; the
remaining `2^depth - chunks.length` positions are conceptually
zero, but never materialised. `ZERO_HASHES` short-circuits them
at the corresponding subtree depth.

This matters for large caps like `VALIDATOR_REGISTRY_LIMIT = 2^40`:
explicit padding would require `2^40` `zero32` leaves (~35 TB).
The level-aware combine and the single-leaf promote let us
process realistic chunk lists (a few dozen entries) in `O(depth)`
hash steps regardless of the nominal cap. -/
private def merkleize (H : Type) [Hasher H]
    (chunks : List ByteArray) (depth : Nat) : ByteArray :=
  -- Step down through tree levels until we either reach the target
  -- depth (return the single root) or run out of items and short-
  -- circuit the remaining levels through `ZERO_HASHES`.
  let rec go : List ByteArray → Nat → ByteArray
    | [],   d => zeroHashAtClamped H d
    | [c],  d => promoteThroughZeros H c 0 d
    | cs,   0 => cs.head?.getD zero32  -- defensive: depth=0 with multi-chunk
    | cs,   d + 1 => go (combineLayerAt H 0 cs) d
  -- Specialisation: `go (combineLayerAt 0 cs) d` then `go (combineLayerAt 1 _) (d-1)` etc.
  -- The level tracking is folded into a wrapper that increments
  -- through each call so `combineLayerAt` uses the correct ZH index.
  let rec goAt : List ByteArray → (curLvl : Nat) → (remaining : Nat) → ByteArray
    | [],   _,      remaining => zeroHashAtClamped H remaining
    | [c],  curLvl, remaining => promoteThroughZeros H c curLvl remaining
    | cs,   _,      0         => cs.head?.getD zero32
    | cs,   curLvl, remaining + 1 =>
        goAt (combineLayerAt H curLvl cs) (curLvl + 1) remaining
  -- Use the level-aware version. (The single-`go` above is left as
  -- a fallback for callers that don't track level; we always use
  -- `goAt` from depth root.)
  let _ := go
  goAt chunks 0 depth

/-- `⌈log₂ (max 1 n)⌉`, used to derive a tree depth from a leaf
count. `chunkDepth 0 = 0` (single-leaf tree of `zero32`),
`chunkDepth 1 = 0`, `chunkDepth 2 = 1`, `chunkDepth 3 = 2`, ...
Recurses on a `fuel` argument bounded by `n` itself. -/
def chunkDepth (n : Nat) : Nat :=
  let rec go : (fuel : Nat) → (acc : Nat) → (cur : Nat) → Nat
    | 0,     acc, _   => acc
    | f + 1, acc, cur =>
        if cur ≥ n then acc
        else go f (acc + 1) (cur * 2)
  go n 0 1

/-! ### Mix-in helpers -/

/-- *Mix in length.* Per spec *§Merkleization, Helper functions*:
a variable-length collection's root is `combine bodyRoot
(uint64ToChunk count)`, where `count` is the *actual* element /
bit count of the value (not the cap). -/
private def mixInLength (H : Type) [Hasher H]
    (root : ByteArray) (n : Nat) : ByteArray :=
  Hasher.combine (H := H) root (natToChunk n)

/-- *Mix in selector.* Per spec *§Merkleization, Union*: a union's
root is `combine variantRoot (uint64ToChunk selector)`. The chunk
encoding is the same as length mix-in, only the semantic role
differs. -/
private def mixInSelector (H : Type) [Hasher H]
    (root : ByteArray) (sel : Nat) : ByteArray :=
  Hasher.combine (H := H) root (natToChunk sel)

/-! ### Bit-list to bytes (no trailing delimiter)

The bitlist body merkleization needs the data bits packed LSB-first
into bytes, *without* the trailing-delimiter bit `serialize`
appends. Reconstructing the body via `BitVec.ofFn` would be cleanest,
but Lean 4.29.1's core library doesn't ship that constructor; we go
through `BitVec.ofNat` instead, treating the bit-list LSB-first as
a `Nat`. -/

/-- LSB-first interpretation of a `List Bool` as a `Nat`:
`[b₀,b₁,b₂] ↦ b₀·1 + b₁·2 + b₂·4`. Recurses structurally on the list. -/
def bitsToNatLE : List Bool → Nat
  | []        => 0
  | b :: rest => (if b then 1 else 0) + 2 * bitsToNatLE rest

/-! ### Chunk-count limits

For variable-length basic-type collections (`list t cap` where `t`
is a basic type), the merkleization depth is fixed by the cap, not
the actual length: even a one-element list merkleizes against the
full `cap`-derived tree. These helpers compute the chunk-count limit
from the schema. -/

/-- Number of chunks needed to pack `n` bytes (one chunk per
`BYTES_PER_CHUNK` bytes, ceil division). -/
def bytesToChunkCount (n : Nat) : Nat :=
  (n + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK

/-- Number of chunks needed to pack `n` bits, `n` bits become
`⌈n/8⌉` bytes which become `⌈⌈n/8⌉/32⌉ = ⌈n/256⌉` chunks. -/
def bitsToChunkCount (n : Nat) : Nat :=
  (n + 256 - 1) / 256

/-! ### The merkleizer

A single `mutual` block: `hashTreeRoot` recurses structurally on
`s : SSZType`; the list-traversing helpers (`hashTreeRootFields`
for container fields, `hashTreeRootListFixed` /
`hashTreeRootListComposite` for collection bodies) recurse
structurally on their `List` argument. Cross-calls descend on
subterms, same shape `Spec/Serialize.lean` and `Spec/Interp.lean`
use. -/

mutual

/-- Total SSZ Merkleization.

Per consensus-specs *§Merkleization*. The `uintN n` arms outside
the standard widths fall through to a 32-byte zero chunk so
totality holds; callers that exercise those widths observe the
wrong root and fail conformance, so the absence cannot be silently
shipped. -/
def SSZType.hashTreeRoot (H : Type) [Hasher H] :
    (s : SSZType) → s.interp → ByteArray
  | .uintN 8,             x  =>
      let x' : UInt8 := x
      padToChunk (ByteArray.empty.push x')
  | .uintN 16,            x  =>
      let x' : UInt16 := x
      padToChunk (
        (ByteArray.empty.push x'.toUInt8).push (x' >>> 8).toUInt8)
  | .uintN 32,            x  =>
      let x' : UInt32 := x
      padToChunk (
        ((((ByteArray.empty.push x'.toUInt8
          ).push (x' >>> 8).toUInt8
          ).push (x' >>> 16).toUInt8
          ).push (x' >>> 24).toUInt8))
  | .uintN 64,            x  =>
      let x' : UInt64 := x
      padToChunk (
        ((((((((ByteArray.empty.push x'.toUInt8
          ).push (x' >>> 8).toUInt8
          ).push (x' >>> 16).toUInt8
          ).push (x' >>> 24).toUInt8
          ).push (x' >>> 32).toUInt8
          ).push (x' >>> 40).toUInt8
          ).push (x' >>> 48).toUInt8
          ).push (x' >>> 56).toUInt8))
  | .uintN 128,           x  =>
      let x' : BitVec 128 := x
      padToChunk (natToChunk x'.toNat)
  | .uintN 256,           x  =>
      -- `uint256` already occupies a full chunk (32 bytes); no padding
      -- is needed but `padToChunk` is a no-op at that width.
      let x' : BitVec 256 := x
      padToChunk (natToChunk x'.toNat)
  | .uintN _,             _  =>
      -- Non-spec uintN width, a degenerate case. Return zero chunk.
      zero32
  | .bool,                b  =>
      let b' : Bool := b
      padToChunk (ByteArray.empty.push (if b' then 1 else 0))
  | .bitvector n,         bv =>
      let bv' : BitVec n := bv
      let body := SSZType.serialize (.bitvector n) bv'
      let chunks := chunkify body
      merkleize H chunks (chunkDepth (bytesToChunkCount ((n + 7) / 8)))
  | .bitlist cap,         bs =>
      -- Bitlist body is the bits *without* the trailing-delimiter
      -- bit (the delimiter is a serialization concern, not a
      -- merkleization concern). The mix-in carries the actual
      -- bit-count.
      let bs' : { xs : Array Bool // xs.size ≤ cap } := bs
      let xs := bs'.val
      let bv : BitVec xs.size := BitVec.ofNat xs.size (bitsToNatLE xs.toList)
      let bytes := SSZType.serialize (.bitvector xs.size) bv
      let chunks := chunkify bytes
      let bodyRoot := merkleize H chunks (chunkDepth (bitsToChunkCount cap))
      mixInLength H bodyRoot xs.size
  | .vector t n,          v  =>
      let v' : Vector t.interp n := v
      -- Per SSZ Merkleization spec: a `Vector[basic, N]` packs its
      -- elements into 32-byte chunks and merkleizes at depth
      -- `⌈N·size(basic)/32⌉`. A `Vector[composite, N]` (including
      -- fixed-size composites like `FixedTestStruct`) instead takes
      -- the per-element `hash_tree_root` and merkleizes at depth
      -- `⌈log₂ N⌉`. The two rules differ even when the composite is
      -- fixed-size, so we dispatch on `isBasicType`, not `isFixedSize`.
      if t.isBasicType then
        let body := SSZType.serialize (.vector t n) v'
        let chunks := chunkify body
        merkleize H chunks (chunkDepth (bytesToChunkCount body.size))
      else
        let roots := SSZType.hashTreeRootListComposite H t v'.toList
        merkleize H roots (chunkDepth n)
  | .list t cap,          xs =>
      let xs' : { ys : Array t.interp // ys.size ≤ cap } := xs
      let actualLen := xs'.val.size
      -- Same `isBasicType` vs `isFixedSize` distinction as `.vector`
      -- above. `List[FixedTestStruct, N]` is composite-element and
      -- merkleizes per-element HTR roots at depth `chunkDepth(cap)`,
      -- NOT byte-packed.
      if t.isBasicType then
        let body := SSZType.serializeFixedElems t xs'.val.toList
        let chunks := chunkify body
        let perElem := t.fixedByteSize
        let capChunks := bytesToChunkCount (cap * perElem)
        let bodyRoot := merkleize H chunks (chunkDepth capChunks)
        mixInLength H bodyRoot actualLen
      else
        let roots := SSZType.hashTreeRootListComposite H t xs'.val.toList
        let bodyRoot := merkleize H roots (chunkDepth cap)
        mixInLength H bodyRoot actualLen
  | .container fs, vs =>
      let roots := SSZType.hashTreeRootFields H fs vs
      merkleize H roots (chunkDepth fs.length)

/-- Per-field merkleization for `container fs`. Returns the list of
field roots in declaration order; the caller merkleizes that list. -/
def SSZType.hashTreeRootFields (H : Type) [Hasher H] :
    (fs : List SSZType) → SSZType.interpFields fs → List ByteArray
  | [],      _   => []
  | t :: ts, vs  =>
      SSZType.hashTreeRoot H t vs.1
        :: SSZType.hashTreeRootFields H ts vs.2

/-- Per-element merkleization for composite-element collections
(`vector t n` / `list t cap` with `¬ t.isFixedSize`). Returns the
list of element roots in order.

Tail-recursive over the element list (the `combineLayerAtAux` /
`deserializeFixedElems` accumulator pattern). The natural
`hashTreeRoot … :: hashTreeRootListComposite …` spelling is
non-tail, the recursive call is the tail of a `cons`, so it holds
one stack frame per element and overflows the OS-default 8 MB stack
on the large mainnet collections (`pendingConsolidations` at
262144 elements). The accumulator form is constant-stack; the base
case reverses it, so the root order is unchanged. `acc` defaults to
`[]` so call sites pass only `(t, elems)`. -/
def SSZType.hashTreeRootListComposite (H : Type) [Hasher H] :
    (t : SSZType) → List t.interp → (acc : List ByteArray := []) → List ByteArray
  | _, [],      acc => acc.reverse
  | t, x :: xs, acc =>
      SSZType.hashTreeRootListComposite H t xs (SSZType.hashTreeRoot H t x :: acc)

end

/-- Public entry point matching ARCHITECTURE.md §3.3's signature.
Thin wrapper that picks up `H` from the instance binder so callers
write `hashTreeRoot s x` rather than `SSZType.hashTreeRoot H s x`.

Inference chain at the call site:
1. Caller's `[Hasher H]` instance is in scope (or supplied by elaboration).
2. The implicit `{H : Type}` binder is unified with whichever `H` the
   in-scope instance refines.
3. Inside the body, the *explicit* `H` is passed positionally to
   `SSZType.hashTreeRoot`, the mutual-block functions take `H` as a
   regular argument (not an instance binder on the function itself)
   because the helpers need it positionally for `(H := H)` projections. -/
def hashTreeRoot {H : Type} [Hasher H] (s : SSZType) (x : s.interp) :
    ByteArray :=
  SSZType.hashTreeRoot H s x

end SizzLean.Spec
