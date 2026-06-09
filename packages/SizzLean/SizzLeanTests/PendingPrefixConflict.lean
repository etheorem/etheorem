import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.PendingPrefixConflict`: overlay parent/child writes

`PendingOverlayCoherence` covers the disjoint-path overlay
shapes. This file covers the case its precondition documents but
does not exercise: **two `sszUpdate` statements whose target
gindices have a strict-prefix relation**.

The pending overlay is a `Std.TreeMap Nat (PendingWrite T)` keyed
by gindex. Two `sszUpdate` statements at related gindices both
land in the map without being merged. At commit time,
`commitAndHash`/`setManyAt` follows the
`SizzLean.Cache.MerkleTree.SetAt` precondition: when multiple
updates at the same level include a whole-subtree replacement
(`[]`-path) and a deeper write, the whole-replacement wins and
the deeper write is *silently dropped*. The single-statement
`sszUpdate` macro never emits such mixes, but cross-statement
chains can, and the resulting tree root diverges from
`SSZ.hashTreeRoot t.view`.

These tests are deliberately written to **fail with
`native_decide` when the bug is present**. Each case computes the
expected view by applying the writes in sequence to the original
`T` and asserts the cached root equals
`SSZ.hashTreeRoot Sha256 expectedView`.

| # | Shape                                        | Expected w/ bug         |
|---|----------------------------------------------|-------------------------|
| 1 | parent → child   (struct, one level)         | **FAIL**: child dropped |
| 2 | child  → parent  (struct, one level)         | pass: order coincides   |
| 3 | parent → child → child (two children)        | **FAIL**: both dropped  |
| 4 | parent → sibling → child                     | **FAIL**: child dropped |
| 5 | vector-whole-write → vector-index            | **FAIL**: index dropped |

After the fix, all five should pass.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.PendingPrefixConflict

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanTests.ExampleContainers

private def baseInner : InnerExample :=
  { slot       := 100
    marker     := 200
    rootA      := Vector.replicate 32 0xaa
    rootB      := Vector.replicate 32 0xbb
    rootC      := Vector.replicate 32 0xcc }

private def n0 : NestedExample :=
  { message   := baseInner
    signature := Vector.replicate 96 0xff }

private def newInner : InnerExample :=
  { slot       := 1
    marker     := 2
    rootA      := Vector.replicate 32 0x10
    rootB      := Vector.replicate 32 0x20
    rootC      := Vector.replicate 32 0x30 }

private def newSig : Vector UInt8 96 := Vector.replicate 96 0xc3

private def batchVal (k : UInt8) : ExRoot :=
  Vector.replicate 32 k

private def b0 : BatchExample :=
  { rootsA := Vector.ofFn fun (i : Fin 8) => batchVal (UInt8.ofNat i.val)
    rootsB := Vector.ofFn fun (i : Fin 8) => batchVal (UInt8.ofNat (8 + i.val)) }

private def newVec : Vector ExRoot 8 :=
  Vector.ofFn fun (i : Fin 8) => batchVal (UInt8.ofNat (100 + i.val))

/-! ## Case 1: parent-then-child (struct)

`message := newInner`, then `message.slot := 999`.

Pending after both writes: `{gindex(message) → newInner, gindex(message.slot) → 999}`.
TreeMap iterates `message` first. At its level inside `commitAndHash`,
`message`'s remaining path is `[]` (whole-replacement);
`message.slot`'s is non-empty (further descent). The whole-replacement
wins and the slot write is **silently dropped**.

View, by contrast, reflects both writes (the second `sszUpdate` calls
`{ view with message.slot := 999 }` on top of the first). -/
example :
    let t  : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 n0
    let t1 := sszUpdate t  with message := newInner
    let t2 := sszUpdate t1 with message.slot := 999
    let expected : NestedExample :=
      { n0 with message := { newInner with slot := 999 } }
    t2.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Case 2: child-then-parent (struct)

Inverse order. The later `message := newInner` whole-replacement
*should* override the earlier `message.slot` write, and TreeMap's
gindex-ascending order happens to deliver that, because
`gindex(message) < gindex(message.slot)`. This case is expected to
pass even with the bug present; included so the contrast with
Case 1 is explicit. -/
example :
    let t  : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 n0
    let t1 := sszUpdate t  with message.slot := 999
    let t2 := sszUpdate t1 with message := newInner
    let expected : NestedExample := { n0 with message := newInner }
    t2.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Case 3: parent then two children

`message := newInner`, then `message.slot := 999`, then
`message.marker := 1234`. Both child writes are dropped at commit by
the same precondition. -/
example :
    let t  : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 n0
    let t1 := sszUpdate t  with message := newInner
    let t2 := sszUpdate t1 with message.slot   := 999
    let t3 := sszUpdate t2 with message.marker := 1234
    let expected : NestedExample :=
      { n0 with message :=
          { newInner with slot := 999, marker := 1234 } }
    t3.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Case 4: parent, sibling, child

`message := newInner`, then `signature := newSig`, then
`message.slot := 999`. The sibling write at `signature` is a disjoint
path (no prefix relation) and survives. The `message.slot` write is
still dropped by the parent's whole-replacement. -/
example :
    let t  : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 n0
    let t1 := sszUpdate t  with message      := newInner
    let t2 := sszUpdate t1 with signature    := newSig
    let t3 := sszUpdate t2 with message.slot := 999
    let expected : NestedExample :=
      { message   := { newInner with slot := 999 }
        signature := newSig }
    t3.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Case 5: vector-whole-write then vector-index

`rootsA := newVec`, then `rootsA[0] := x`. Same shape as Case 1 but
the parent is a vector (depth-3 subtree) and the child is one of its
elements. The element write is dropped by the vector-write's
whole-replacement at the `rootsA` subtree level. -/
example :
    let t  : TreeBacked Sha256 BatchExample := TreeBacked.ofValue Sha256 b0
    let t1 := sszUpdate t with rootsA := newVec
    let expected : BatchExample :=
      { rootsA := newVec.set 0 (Vector.replicate 32 0xee)
        rootsB := b0.rootsB }
    (sszUpdate t1 with rootsA[0] := Vector.replicate 32 0xee).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 expected) := by
  native_decide

end SizzLeanTests.PendingPrefixConflict
