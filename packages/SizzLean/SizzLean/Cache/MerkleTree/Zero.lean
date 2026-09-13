import SizzLean.Hasher.Class
import SizzLean.Hasher.Sha256
import LeanHazmatSha256
import SizzLean.Cache.MerkleTree.Node

/-!
# `SizzLean.Cache.MerkleTree.Zero`: the zero-hash tower and the depth-padding leaf

A 100-entry table of all-zero subtree roots, used both to
short-circuit zero-padding in `merkleRootWithCache` and to
materialise `zeroLeaf d` (the right-sibling subtree at any
depth when `setAt` walks past a not-yet-filled position).

The table is **memoised once at module load** into a private
`IO.Ref`, populated by direct calls to `LeanHazmat.Sha256.sha256Combine`
(the FFI primitive, no `Hasher.combine` typeclass dispatch). The
public accessor `zeroHashAt` reads from the memo via `unsafeBaseIO`;
the ref is set-once-at-init and never mutated after, so the access is
morally const. The polymorphic `[Hasher H]` parameter on `zeroHashAt`
matters in the kernel-visible body `zeroHashRec`, which
recurses over `Hasher.combine (H := H)`; `Proofs/Merkle/Zero.lean`
proves it equals the spec tower for every hasher. The runtime
memo is substituted via `@[implemented_by]` under the swap's side
condition, that `H`'s combine is SHA-256.

## Reduction at module-load time

The recurrence
    `Z[0] = zero32`
    `Z[d+1] = LeanHazmat.Sha256.sha256Combine Z[d] Z[d]`
is structural recursion on `Nat`. Each level is computed once at
module load via the FFI `lean_hazmat_sha256_combine` shim; subsequent
`zeroHashAt _ d` calls are O(1) Vector indexes into the memo.

The table is 100 entries because that is the length of
`merkle_minimal.py`'s `zerohashes`, which the spec indexes directly
(so `zerohashes[100]` raises `IndexError`). SSZ's `MAX_LENGTH = 2^32`
caps a real tree near depth 34 and the largest consensus cap,
`VALIDATOR_REGISTRY_LIMIT = 2^40`, reaches 40, so the memo covers
every depth the format admits with room to spare.

`Vector.get` with a `Fin 100` index is total, and the `d ≥ 100`
fallback continues the same recurrence the table was built from
rather than clamping. That keeps `zeroHashAt` equal to the depth-`d`
zero root at *every* depth, which is what lets `Node.ofLeaves` and
the spec's `merkleize` agree with no depth side condition. It also
lets `ofLeaves` / `setAt` typecheck without local bound proofs at
every call site.

## Trust footprint

The `unsafeBaseIO` accessor for the memo adds one implementation-
defined trust assumption: the `initialize` block runs before any
reader. This is parallel to (and same trust class as) the
`@[extern] opaque LeanHazmat.Sha256.sha256Combine` declaration; both are
validated by the `Sha256Equivalence` test suite re-running the
recurrence against the pure-Lean reference.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

open SizzLean.Hasher

open SizzLean

/-- 32-byte all-zero `ByteArray`. The leaf at every depth-`0`
position of an all-zero subtree. Identical to `Spec.zero32` (the
build checks `Cache.zero32 = Spec.zero32` by `rfl` in
`Proofs/Merkle/Zero.lean`), kept as a duplicate rather than
importing the spec-internal helper because the Tree layer is meant
to stand alone (so a future caller could load it without the spec). -/
def zero32 : ByteArray :=
  let rec build : Nat → ByteArray → ByteArray
    | 0,     acc => acc
    | k + 1, acc => build k (acc.push 0)
  build 32 ByteArray.empty

/-- Kernel-visible tower: the spec's recurrence over the caller's
hasher. `zeroHashAt`'s *body* is this definition, so a proof about
`zeroHashAt` sees the same recurrence `SizzLean.Spec.zeroHashAt`
states, per depth and for every `H` at once. -/
def zeroHashRec (H : Type) [Hasher H] : Nat → ByteArray
  | 0     => zero32
  | d + 1 => Hasher.combine (H := H) (zeroHashRec H d) (zeroHashRec H d)

/-- The FFI-specific recurrence the memo is populated from. Used
only at module-load time and in `zeroHashAt`'s past-the-memo
runtime branch, no proof ever names it. Calls
`LeanHazmat.Sha256.sha256Combine` (the FFI primitive) directly
rather than going through `Hasher.combine`'s typeclass dispatch,
since the memo is intentionally Sha256-specific. -/
private def zeroHashRecSha256 : Nat → ByteArray
  | 0     => zero32
  | d + 1 =>
      let z : ByteArray := zeroHashRecSha256 d
      LeanHazmat.Sha256.sha256Combine z z

/-- The depth-indexed zero-hash table, lazily populated at module
load. Held inside an `IO.Ref` so the 100-entry vector is computed
exactly once per process; readers go through `zeroHashes` (and
ultimately `zeroHashAt`) which fetch in O(1). -/
private initialize zeroHashesRef : IO.Ref (Vector ByteArray 100) ←
  IO.mkRef (Vector.ofFn (fun (i : Fin 100) => zeroHashRecSha256 i.val))

/-- Runtime impl of `zeroHashes`: reads the memoised vector
directly from `zeroHashesRef`. Wrapped in `unsafeBaseIO` because
the ref is set-once at init and never mutated, so the value is
morally const. Marked `unsafe` so the compiler accepts the
`unsafeBaseIO` call; the safe `zeroHashes` def below swaps to
this impl via `@[implemented_by]`. -/
private unsafe def zeroHashesUnsafeImpl : Vector ByteArray 100 :=
  unsafeBaseIO zeroHashesRef.get

/-- Safe public-facing zero-hash table. The kernel-visible body
is the pure recurrence (slow, would re-run on every reduction);
the runtime body, substituted via `@[implemented_by]`, is the
`unsafeBaseIO`-backed read from the memoised ref. Both produce
identical bytes by construction (the ref was populated by the
same `zeroHashRec` recurrence at module load), so the trust
footprint of the swap is "the init action ran before any
reader", the same trust class as the `@[extern] opaque sha256Combine`
that populated the ref. -/
@[implemented_by zeroHashesUnsafeImpl]
private def zeroHashes : Vector ByteArray 100 :=
  Vector.ofFn (fun (i : Fin 100) => zeroHashRecSha256 i.val)

/-- Runtime impl of `zeroHashAt`: the memo read below depth 100,
the FFI recurrence above it. Never runs in the kernel; the kernel
sees `zeroHashAt`'s own body, the `zeroHashRec H d` recurrence. -/
private unsafe def zeroHashAtUnsafeImpl (H : Type) [Hasher H] (d : Nat) : ByteArray :=
  if h : d < 100 then zeroHashes.get ⟨d, h⟩ else zeroHashRecSha256 d

/-- Zero-hash at depth `d`: the root of an all-zero subtree of
depth `d`. The kernel-visible body is `zeroHashRec H d`, the spec's
own recurrence; the runtime body, substituted via
`@[implemented_by]`, is the memo read (below 100) with the
uncached FFI recurrence past it. Real trees never leave the memo
(SSZ `MAX_LENGTH = 2^32` keeps any real tree depth well under
100), so the memo and the recurrence agree at every depth a real
tree reaches.

The swap's side condition: the runtime body computes the same
bytes as the kernel body only for a hasher whose `combine` is
SHA-256. That is `Sha256` by definition and `Sha256Spec` by the
`sha256Combine_eq_spec` axiom; a third hasher instance would be
trusted through the same entry. The `SizzLeanTests/ZeroHashDepth`
gate pins the join at depth 100 empirically. -/
@[implemented_by zeroHashAtUnsafeImpl]
def zeroHashAt (H : Type) [Hasher H] (d : Nat) : ByteArray :=
  zeroHashRec H d

/-- Cheap root lookup that *doesn't* allocate a new cache-filled
tree. `.leaf b` → `b`; `.pair _ _ (some r)` → `r` in O(1);
`.pair _ _ none` → recursively walks the children. Used by
builders that need a child's root to embed into a parent's cache
slot at construction time.

Not a substitute for `merkleRootWithCache`, since it doesn't fill
cache slots in the input tree. Use when you only need the root
*value* and the input is expected to be already cached (in which
case it's O(1)).

Structural recursion on `Node`, so the kernel gets unfolding
equations and the proof layer can reason about filled slots. -/
def Node.rootOf (H : Type) [Hasher H] : Node → ByteArray
  | .leaf b               => b
  | .pair _ _ (some r)    => r
  | .pair l r none        =>
      Hasher.combine (H := H) (Node.rootOf H l) (Node.rootOf H r)

/-- A `Node` whose root is the all-zero subtree of depth `d`. Used
by `Node.ofLeaves` to pad the right of an underfilled tree, and by
`Node.setAt` when walking past a not-yet-filled position.

For `d = 0` this is a literal zero leaf; for `d > 0` it is a
`pair` whose cache slot is pre-filled with `zeroHashAt H (d+1)`.
This lets `merkleRootWithCache` short-circuit the entire zero
subtree on the first walk without re-hashing. -/
def zeroLeaf (H : Type) [Hasher H] : Nat → Node
  | 0     => .leaf zero32
  | d + 1 =>
      let child := zeroLeaf H d
      let r := zeroHashAt H (d + 1)
      .pair child child (some r)

/-- Build a balanced binary tree of depth `depth`, taking
`leaves` as the left-aligned data leaves and padding the right
with `zeroLeaf` subtrees as necessary. The result is the `Node`
whose `merkleRootWithCache` matches the spec's `merkleize` of
the same leaf list at the same depth.

Termination: structural recursion on `depth`. -/
def Node.ofLeaves (H : Type) [Hasher H] (leaves : List ByteArray)
    (depth : Nat) : Node :=
  match depth, leaves with
  | 0,     []      => zeroLeaf H 0
  | 0,     l :: _  => .leaf l   -- depth 0 holds exactly one leaf
  | d + 1, ls      =>
      -- Split `ls` at index `2^d`. The left half goes into the
      -- left subtree (size `2^d`); whatever remains feeds the
      -- right subtree. We compute the parent's root inline and
      -- store it in the cache slot. This avoids a subsequent
      -- `merkleRootWithCache` walk re-allocating the same pair
      -- with the cache filled in.
      let half := 2 ^ d
      -- `List.take` is not tail-recursive in Lean core, so `ls.take half`
      -- recurses `half` frames deep and overflows the OS-default 8 MB stack
      -- for the large mainnet leaf counts (a 262144-leaf list splits 131072
      -- at the top). `List.splitAt` yields the same `(take, drop)` pair in a
      -- single tail-recursive pass.
      let (leftLeaves, rightLeaves) := ls.splitAt half
      let leftNode  := Node.ofLeaves H leftLeaves  d
      let rightNode :=
        if rightLeaves.isEmpty then zeroLeaf H d
        else Node.ofLeaves H rightLeaves d
      let root := Hasher.combine (H := H)
        (Node.rootOf H leftNode) (Node.rootOf H rightNode)
      .pair leftNode rightNode (some root)

end SizzLean.Cache.MerkleTree
