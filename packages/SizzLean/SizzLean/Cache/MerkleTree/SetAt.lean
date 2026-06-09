import SizzLean.Hasher.Class
import SizzLean.Cache.MerkleTree.Node
import SizzLean.Cache.MerkleTree.Zero
import SizzLean.Cache.MerkleTree.Merkle

/-!
# `SizzLean.Cache.MerkleTree.SetAt`: generalized-index updates

The highest-risk file in the project per the Nimbus February
2025 incident, an off-by-one in gindex arithmetic caused a
mainnet client to fork. The mitigation here: never do gindex
arithmetic on `Nat`. Instead, extract the path as a `List Bool`
*once* and recurse structurally on the bit list. The compiler
enforces exhaustiveness; the bit-list shape makes left/right
confusion syntactically impossible at the call site.

## Gindex path convention

A *generalized index* `g : Nat` identifies one node in a binary
tree, 1-indexed from the root:

| gindex | binary | path |
|--------|--------|------|
| 1      | `1`    | root            (path: `[]`) |
| 2      | `10`   | left of root    (path: `[false]`) |
| 3      | `11`   | right of root   (path: `[true]`) |
| 4      | `100`  | left-left       (path: `[false, false]`) |
| 5      | `101`  | left-right      (path: `[false, true]`) |
| 6      | `110`  | right-left      (path: `[true, false]`) |
| 7      | `111`  | right-right     (path: `[true, true]`) |

The leading `1` bit is the *root marker*; remaining bits MSB-first
spell the path. `false` = take the left child, `true` = take the
right child.

`gindexBits` returns exactly those path bits, in order from root to
target. The implementation uses `Nat.log2` and `Nat.testBit`,
no division-by-2 ad-hoc, no fuel arguments, so the result is a
direct read of the existing well-tested integer primitives.
-/

set_option autoImplicit false

namespace SizzLean.Cache.MerkleTree

/-- Path bits for a generalized index, root-to-target order
(`false` = left, `true` = right). The leading `1` bit of `g`'s binary
representation is *not* included.

Reads bits MSB-first from position `g.log2 - 1` down to `0`. For
`g = 1`, `log2 = 0`, range is empty → `[]`. For `g = 2`, `log2 = 1`,
range `[0]` reversed → `[0]`, `testBit 2 0 = false` → `[false]`. -/
def gindexBits (g : Nat) : List Bool :=
  let n := g.log2
  (List.range n).reverse.map (fun i => g.testBit i)

example : gindexBits 1 = []                       := rfl
example : gindexBits 2 = [false]                  := rfl
example : gindexBits 3 = [true]                   := rfl
example : gindexBits 4 = [false, false]           := rfl
example : gindexBits 5 = [false, true]            := rfl
example : gindexBits 6 = [true,  false]           := rfl
example : gindexBits 7 = [true,  true]            := rfl
example : gindexBits 8 = [false, false, false]    := rfl

/-- Replace the subtree at the path described by `bits` with
`newSubtree`. Recursion is *structural on the bit list*, this is
the mitigation for the Nimbus-class gindex arithmetic bug. The
`pair`'s cache slot is cleared on the spine (set to `none`); off-path
children are reused by value, so reference-counting gives the
structural sharing for free.

* `[]`: we've reached the target, replace.
* `false :: rest`: descend left, rebuild `pair` with cleared cache.
* `true :: rest`: descend right, rebuild `pair` with cleared cache.

`leaf` with a non-empty bit list means the gindex addresses a
position deeper than the tree extends. Returning the leaf unchanged
is the most conservative response, real use shouldn't hit this. -/
def Node.setAtBits : Node → List Bool → Node → Node
  | _,           [],            newSubtree => newSubtree
  | .leaf b,     _ :: _,        _          => .leaf b
  | .pair l r _, false :: rest, newSubtree =>
      .pair (Node.setAtBits l rest newSubtree) r none
  | .pair l r _, true  :: rest, newSubtree =>
      .pair l (Node.setAtBits r rest newSubtree) none

/-- Update the subtree at generalized index `g` to `newSubtree`.
Pure wrapper around `setAtBits ∘ gindexBits`, the `Nat`→`List Bool`
hop is the only place gindex arithmetic happens, and it's
expressed in terms of `Nat.log2` and `Nat.testBit`. -/
def Node.setAt (n : Node) (g : Nat) (newSubtree : Node) : Node :=
  n.setAtBits (gindexBits g) newSubtree

/-- Flatten a `Node` to its left-to-right leaf array. Used by the
`SetAtRandom` property test as part of the slow reference
(`asLeafArray` followed by a fresh `ofLeaves`-based merkleization,
compared to the fast `setAt`-then-`merkleRoot` path).

Termination: structural recursion on `Node`. -/
def Node.asLeafArray : Node → Array ByteArray
  | .leaf b      => #[b]
  | .pair l r _  => Node.asLeafArray l ++ Node.asLeafArray r

/-! ## Batched updates: `Node.setManyAt`

`setManyAt n [(bits₁, v₁), …, (bitsₖ, vₖ)]` applies all `k` writes in
a single tree walk. When several writes share a path prefix, only
*one* fresh `.pair` is allocated at each level of the shared spine.
Contrast the chained form `((n.setAtBits bits₁ v₁).setAtBits bits₂
v₂).setAtBits …`, which allocates one full spine per write and
clears the cache on every off-target sibling along the way.

### What an empty path means at each level

Path bits are *consumed* as we descend: a write `(b :: rest, v)` at
a pair contributes `(rest, v)` to the matching child's recursion.
By the time the recursion reaches the targeted node, the path is
`[]`, that's the "you're here" signal, exactly like
`Node.setAtBits _ [] v = v`.

At both leaves *and* pairs, an `[]`-path update replaces the entire
current subtree with the update's value. If multiple `[]`-path
updates are present at the same level, the *last* one wins (matching
`setAtBits`'s left-to-right replacement semantics). Non-empty-path
updates at a leaf are silently dropped (the path extends past where
the tree exists, same conservative response as `setAtBits`'s
`.leaf b, _ :: _ => .leaf b` arm).

### Precondition: no path is a strict prefix of another

`setManyAt` does *not* try to apply non-empty-path updates after a
whole-subtree replacement at the same level. If the caller passes
both `([], v)` and `(someBits, w)` at the same level (e.g.
`sszUpdate t with message := …, message.slot := …`, the second
clause is `message`'s child), the `setManyAt` result honours the
whole-subtree replacement and silently drops the deeper write. The
`sszUpdate` macro doesn't generate such mixes in practice; the
nested-vs-flat clauses it produces always target disjoint paths
(no one path is a prefix of another).

### Algorithm

* `n, []`: nothing to do.
* `.leaf b, us`: fold over `us`. Each `([], v)` entry replaces the
  current leaf with `v` (last wins).
* `.pair l r _, us`: first pull out the last `[]`-path update as
  `wholeReplacement?`; if present, return its value (with the
  precondition above). Otherwise partition the non-empty-path
  updates by first bit and descend on each side. Reuse a side by
  value when it has no updates, that's the cache-preservation
  property.

Termination: structural recursion on `Node` (we always descend into
`l` and `r` from the `.pair` arm). The `us` argument is processed
by `filterMap`/`foldl`, not pattern-matched into shorter forms,
the size guarantee comes from the `Node` argument alone.
-/

/-- Apply many gindex updates in a single tree walk. See the module
header for the algorithm and the empty-path conventions. -/
def Node.setManyAt : Node → List (List Bool × Node) → Node
  | n,           []     => n
  | .leaf b,     us     =>
      us.foldl (fun acc u =>
        match u.1 with
        | []     => u.2
        | _ :: _ => acc) (.leaf b)
  | .pair l r _, us =>
      -- Look for a whole-subtree replacement at this level (`[]`-path).
      -- Last one wins. Precondition (see module header): no deeper
      -- write may share the same subtree as a whole-replacement at
      -- the same level.
      let wholeReplacement? : Option Node := us.foldl
        (fun acc u => match u.1 with
          | []     => some u.2
          | _ :: _ => acc) none
      match wholeReplacement? with
      | some w => w
      | none =>
          let lefts  : List (List Bool × Node) := us.filterMap fun u =>
            match u.1 with
            | false :: rest => some (rest, u.2)
            | _             => none
          let rights : List (List Bool × Node) := us.filterMap fun u =>
            match u.1 with
            | true  :: rest => some (rest, u.2)
            | _             => none
          let l' := match lefts  with
            | []     => l
            | _ :: _ => Node.setManyAt l lefts
          let r' := match rights with
            | []     => r
            | _ :: _ => Node.setManyAt r rights
          .pair l' r' none

/-! ## Fused commit + root walk: `Node.commitAndHash`

`setManyAt` followed by `merkleRootWithCache` walks the touched
spine *twice*: once to install the new sub-trees (allocating
`.pair _ _ none` cells along the way), once to fill the cache
slots (allocating `.pair _ _ (some r)` for the same cells).
`commitAndHash` fuses both into one walk, each touched spine cell
is allocated once, with its root computed inline.

For untouched branches, returns the existing child by reference
(zero allocation) and reads its root via `Node.rootOf` (O(1) when
cached, recursive otherwise). New sub-trees supplied via `updates`
should ideally come pre-cached (e.g. from the post-modification
`Node.ofShape` builders that now embed cache slots) so the
recursive `rootOf` on them is O(1) at the top.

The result is observationally equivalent to
`(n.setManyAt updates).merkleRootWithCache H`, just allocated
half as many spine pairs. -/
partial def Node.commitAndHash (H : Type) [Hasher H] :
    Node → List (List Bool × Node) → ByteArray × Node
  | n, [] =>
      -- No updates: fall through to `merkleRootWithCache` which
      -- fills cache slots along any uncached spine the caller may
      -- have left in this subtree. If `n` is fully cached, the
      -- top-level `.pair _ _ (some r)` arm short-circuits in O(1).
      n.merkleRootWithCache H
  | .leaf b, us =>
      -- Last whole-replacement wins (matching setManyAt semantics).
      let final := us.foldl (init := (.leaf b : Node)) fun acc u =>
        match u.1 with
        | []     => u.2
        | _ :: _ => acc
      final.merkleRootWithCache H
  | .pair l r _, us =>
      -- Look for a whole-subtree replacement at this level
      let wholeReplacement? : Option Node := us.foldl
        (fun acc u => match u.1 with
          | []     => some u.2
          | _ :: _ => acc) none
      match wholeReplacement? with
      | some w => w.merkleRootWithCache H
      | none =>
          let lefts  : List (List Bool × Node) := us.filterMap fun u =>
            match u.1 with
            | false :: rest => some (rest, u.2)
            | _             => none
          let rights : List (List Bool × Node) := us.filterMap fun u =>
            match u.1 with
            | true  :: rest => some (rest, u.2)
            | _             => none
          let (rootL, l') := match lefts with
            | []     => (Node.rootOf H l, l)
            | _ :: _ => Node.commitAndHash H l lefts
          let (rootR, r') := match rights with
            | []     => (Node.rootOf H r, r)
            | _ :: _ => Node.commitAndHash H r rights
          let root := Hasher.combine (H := H) rootL rootR
          (root, .pair l' r' (some root))

end SizzLean.Cache.MerkleTree
