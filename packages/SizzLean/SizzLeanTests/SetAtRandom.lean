import SizzLean.Hasher.Class
import SizzLean.Hasher.Sha256
import SizzLean.Cache.MerkleTree.Node
import SizzLean.Cache.MerkleTree.Zero
import SizzLean.Cache.MerkleTree.Merkle
import SizzLean.Cache.MerkleTree.SetAt

/-!
# `SizzLeanTests.SetAtRandom`: randomised property test for `Node.setAt`

Generates many random `(tree, gindex, newLeaf)` triples from a
deterministic seed and checks two things:

1. **Fast path matches slow reference.** `(t.setAt g new).merkleRoot`
   equals `Node.ofLeaves ((t.setAt g new).asLeafArray.toList) depth`'s
   root. Both compute the Merkle root of the same leaf array; the
   former does so through the post-`setAt` tree (which has caches in
   varying states), the latter rebuilds a fresh balanced tree. They
   must agree.
2. **`setAt` actually changes the right leaf.** `(t.setAt g new).
   asLeafArray.get! leafIndex = newLeaf.cached` for the leaf-position
   `leafIndex` derived from `g`. Catches off-by-one errors in
   `gindexBits` directly (not just via root mismatch).

Pure deterministic linear-congruential PRNG so `native_decide` can
evaluate the whole thing at compile time. Seeds are written as
hex literals in source for reproducibility.

## Why both checks

Check (1) alone would catch most bugs but is *root*-level: an
off-by-one that swaps two adjacent leaves of equal value would
pass. Check (2) catches that: even if the swapped leaves happen to
hash to the same root by coincidence (extremely unlikely with random
bytes, but possible structurally), the leaf-position read still
exposes the mis-placement. Together they cover the failure surface.
-/

set_option autoImplicit false

namespace SizzLeanTests.SetAtRandom

open SizzLean.Hasher

open SizzLean
open SizzLean.Cache.MerkleTree

/-! ### Deterministic PRNG

A tiny linear-congruential generator. Not cryptographic, just
enough to produce a varied stream of bytes for property testing.
Parameters from "Numerical Recipes" (period `2^32`). -/

/-- Advance the state by one step. -/
private def lcgNext (s : Nat) : Nat :=
  (s * 1664525 + 1013904223) % 4294967296  -- 2^32

/-- Produce one byte plus the new state. -/
private def randByte (s : Nat) : UInt8 × Nat :=
  let s' := lcgNext s
  let b  := Nat.toUInt8 (s' % 256)
  (b, s')

/-- Produce a 32-byte random `ByteArray` plus the new state. -/
private def randBytes32 (s : Nat) : ByteArray × Nat :=
  let rec go : Nat → Nat → ByteArray → ByteArray × Nat
    | 0,     st, acc => (acc, st)
    | k + 1, st, acc =>
        let (b, st') := randByte st
        go k st' (acc.push b)
  go 32 s ByteArray.empty

/-- Generate a fresh random balanced `Node` of `depth`. Each leaf is
a random 32-byte `ByteArray`; interior pairs have empty caches so
the test exercises the fresh-walk path. -/
private def randNode (H : Type) [Hasher H] :
    (depth : Nat) → Nat → Node × Nat
  | 0,     s =>
      let (b, s') := randBytes32 s
      (.leaf b, s')
  | d + 1, s =>
      let (l, s1) := randNode H d s
      let (r, s2) := randNode H d s1
      (.pair l r none, s2)

/-- Pick a random leaf gindex in `[2^depth, 2^(depth+1))`. -/
private def randGindex (depth : Nat) (s : Nat) : Nat × Nat :=
  let base : Nat := 2 ^ depth
  let span : Nat := base  -- there are `2^depth` leaf positions
  let s' := lcgNext s
  let offset : Nat := s' % span
  (base + offset, s')

/-! ### The slow reference

Rebuild a fresh `Node` from the leaf array (via `Node.ofLeaves`)
and compute its root through `merkleRootWithCache`. This *also*
calls into the cache walker, but from a freshly-built tree with no
cached state along the spine, so it is the apples-to-apples
"what should the canonical root be" target for the property test. -/

private def slowMerkleRoot (H : Type) [Hasher H]
    (leaves : List ByteArray) (depth : Nat) : ByteArray :=
  (Node.ofLeaves H leaves depth).merkleRoot H

/-! ### A single property-test case

Generate one tree, one gindex, one replacement leaf; check fast vs
slow root *and* the leaf-position read. Both must agree. -/

private def oneCase (H : Type) [Hasher H] (depth : Nat)
    (s : Nat) : Bool × Nat :=
  let (tree, s1)        := randNode H depth s
  let (g,    s2)        := randGindex depth s1
  let (newB, s3)        := randBytes32 s2
  let newLeaf : Node := Node.leaf newB
  let updated           := tree.setAt g newLeaf
  let fastRoot          := updated.merkleRoot H
  let leafArr           := updated.asLeafArray
  let slowRoot          := slowMerkleRoot H leafArr.toList depth
  -- The leaf-position derived from `g` is the offset of the
  -- target inside `2^depth`-sized leaf-row: `g - 2^depth`.
  let leafIndex         := g - 2 ^ depth
  let rootsAgree        := fastRoot = slowRoot
  let leafAgrees        :=
    if h : leafIndex < leafArr.size then leafArr[leafIndex] = newB else false
  (rootsAgree && leafAgrees, s3)

/-- Run `count` independent property-test cases, threading the PRNG
state. Returns `true` iff every single case passes. -/
private def runCases (H : Type) [Hasher H] (depth : Nat) (count : Nat)
    (s : Nat) : Bool :=
  match count with
  | 0     => true
  | k + 1 =>
      let (ok, s') := oneCase H depth s
      if ok then runCases H depth k s' else false

/-! ### `Node.setAt` acceptance gate

200 random cases at depth 4 (16 leaves per tree), starting from a
fixed seed for reproducibility. If this fails, the failure is
deterministic, re-run with `set_option diagnostics true` to inspect.

The depth 4 / count 200 combination keeps `native_decide`'s
compile-time cost modest while exercising every position in a
non-trivial tree many times over. -/

example :
    runCases Sha256 (depth := 4) (count := 200) (s := 0xDEADBEEF) = true := by
  native_decide

/-! ## `Node.setManyAt` acceptance gate

Property: applying many updates in one batched walk produces the
same leaf array as applying them sequentially via `setAtBits`. The
batched form is the implementation; the chained form is the
"obviously correct" reference. They must produce identical trees up
to cache state. `asLeafArray` strips cache and exposes structure.

### Why distinct gindexes

With duplicate paths, the two walks diverge: the batched form drops
both writes (the empty-path entries that result from consuming all
bits get filtered out at the inner `.pair`), while the chained form
applies them in order and keeps the last. The two semantics agree
*only* when paths are distinct, which is the workload `sszUpdate`
generates in practice (one path per field). The test therefore picks
`k` distinct gindexes by taking a PRNG-derived offset and stepping
through `k` consecutive leaf positions modulo `2^depth`. -/

/-- Generate `k` random leaves' bytes plus the new PRNG state. -/
private def randLeafBytes (H : Type) [Hasher H] : Nat → Nat → List ByteArray × Nat
  | 0,     s => ([], s)
  | k + 1, s =>
      let (b,    s1) := randBytes32 s
      let (rest, s2) := randLeafBytes H k s1
      (b :: rest, s2)

/-- One batched-vs-chained case. Picks `k` distinct leaf positions
and `k` random replacement leaves; checks `asLeafArray` equality. -/
private def oneBatchedCase (H : Type) [Hasher H] (depth : Nat) (k : Nat)
    (s : Nat) : Bool × Nat :=
  let (tree,    s1) := randNode H depth s
  let (leaves,  s2) := randLeafBytes H k s1
  let s3 := lcgNext s2
  let offset := s3 % (2 ^ depth)
  let gindexes : List Nat :=
    (List.range k).map (fun i => 2 ^ depth + (offset + i) % (2 ^ depth))
  let updates : List (List Bool × Node) :=
    gindexes.zip leaves |>.map (fun (g, b) => (gindexBits g, .leaf b))
  let batched    := tree.setManyAt updates
  let sequential := updates.foldl (fun acc u => acc.setAtBits u.1 u.2) tree
  (batched.asLeafArray = sequential.asLeafArray, s3)

private def runBatchedCases (H : Type) [Hasher H] (depth : Nat) (k : Nat) :
    Nat → Nat → Bool
  | 0,     _ => true
  | n + 1, s =>
      let (ok, s') := oneBatchedCase H depth k s
      if ok then runBatchedCases H depth k n s' else false

/-- 100 cases at depth 4 (16 leaves), 5 distinct updates per case.
`5 < 16` so the offset-and-step scheme cannot collide.

Concrete cache-savings sanity (not gated): at depth 4 with 5
updates clustered consecutively, the batched form allocates ~9 fresh
`.pair`s (5 leaf-level + spine sharing) vs ~20 for the chained form
(5 spines × 4 levels). The exact count is implementation-dependent;
the property test only checks behavioural equivalence. -/
example :
    runBatchedCases Sha256 (depth := 4) (k := 5) 100 0xFACADE = true := by
  native_decide

end SizzLeanTests.SetAtRandom
