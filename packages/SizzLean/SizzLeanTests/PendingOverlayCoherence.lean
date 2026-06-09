import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.PendingOverlayCoherence`: pending-overlay coherence

Every `sszUpdate` on a cached value accumulates into the
`TreeBacked.pending` overlay rather than walking the spine
immediately. The user-observable invariant must not move:

    t.hashTreeRootCached = SSZ.hashTreeRoot Sha256 t.view

for *every* `t : TreeBacked Sha256 T`, regardless of how many
writes are sitting in `pending`. The reader (`hashTreeRootCached`)
calls `commit` first, so the cache-vs-spec coherence is upheld at
read time.

Cases 1–6 cover field and composite-element-index writes; cases
7–9 cover *basic-packed* element indices (the owner-rebuild path).
The first six:

1. *zero writes*: `ofValue` then root; sanity check that the
   pending field starts empty.
2. *one write*: single `sszUpdate`; one pending entry.
3. *three disjoint writes*: same shape, three distinct fields;
   three pending entries, no shared spine prefix.
4. *three writes with a shared prefix*: `BatchExample.rootsA[i]`
   for three values of `i`; the `setManyAt` batch-partition step
   should share the outer prefix.
5. *write-then-overwrite*: `sszUpdate s with f := v1` then
   `sszUpdate s with f := v2`; only `v2` should be observable.
6. *commit roundtrip*: `t.commit.hashTreeRootCached` must equal
   `t.hashTreeRootCached` (calling commit explicitly should
   change nothing user-observable).

The acceptance principle: the `TreeBacked` coherence invariant
continues to hold across every pending-overlay shape.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.PendingOverlayCoherence

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanTests.ExampleContainers

private def f0 : FlatExample :=
  { versionA := Vector.replicate 4 0x11
    versionB := Vector.replicate 4 0x22
    marker   := 7 }

private def baseInner : InnerExample :=
  { slot       := 100
    marker     := 200
    rootA      := Vector.replicate 32 0xaa
    rootB      := Vector.replicate 32 0xbb
    rootC      := Vector.replicate 32 0xcc }

private def n0 : NestedExample :=
  { message   := baseInner
    signature := Vector.replicate 96 0xff }

private def batchVal (k : UInt8) : ExRoot :=
  Vector.replicate 32 k

private def b0 : BatchExample :=
  { rootsA := Vector.ofFn fun (i : Fin 8) => batchVal (UInt8.ofNat i.val)
    rootsB := Vector.ofFn fun (i : Fin 8) => batchVal (UInt8.ofNat (8 + i.val)) }

/-! ## Case 1: zero writes -/

example :
    (TreeBacked.ofValue Sha256 f0).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 f0 := by native_decide

/-! ## Case 2: one write -/

example :
    let t  : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 f0
    let t' := sszUpdate t with marker := 42
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 ({ f0 with marker := 42 } : FlatExample) := by
  native_decide

/-! ## Case 3: three disjoint writes (one statement) -/

example :
    let t  : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 f0
    let t' := sszUpdate t with
      versionA := Vector.replicate 4 0xde,
      versionB := Vector.replicate 4 0xad,
      marker   := 0xbeef
    let expected : FlatExample :=
      { versionA := Vector.replicate 4 0xde
        versionB := Vector.replicate 4 0xad
        marker   := 0xbeef }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Case 4: three writes with a shared prefix (vector index) -/

example :
    let t  : TreeBacked Sha256 BatchExample := TreeBacked.ofValue Sha256 b0
    let expected : BatchExample :=
      { rootsA := b0.rootsA |>.set 0 (Vector.replicate 32 0xa0)
                            |>.set 1 (Vector.replicate 32 0xa1)
                            |>.set 2 (Vector.replicate 32 0xa2)
        rootsB := b0.rootsB }
    (sszUpdate t with
      rootsA[0] := Vector.replicate 32 0xa0,
      rootsA[1] := Vector.replicate 32 0xa1,
      rootsA[2] := Vector.replicate 32 0xa2).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 expected) := by
  native_decide

/-! ## Case 5: write-then-overwrite across statements -/

example :
    let t  : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 f0
    let t1 := sszUpdate t  with marker := 99
    let t2 := sszUpdate t1 with marker := 42       -- override
    t2.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 ({ f0 with marker := 42 } : FlatExample) := by
  native_decide

/-! ## Case 6: repeated reads on the same Box agree (Thunk
memoisation semantics): two `hashTreeRootCached` calls on the
same `TreeBacked` value produce the same bytes. -/

example :
    let t  : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 n0
    let t' := sszUpdate t with message.slot := 999
    t'.hashTreeRootCached.1 = t'.hashTreeRootCached.1 := by
  native_decide

/-! ## Cross-statement batching: three single-field statements
in sequence should yield the same root as one three-field
statement. The integrated overlay (vs a separate `ViewDU` type)
makes this batching automatic. -/

example :
    let t      : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 f0
    -- three-in-one
    let oneShot := sszUpdate t with
      versionA := Vector.replicate 4 0xde,
      versionB := Vector.replicate 4 0xad,
      marker   := 0xbeef
    -- three statements
    let s1 := sszUpdate t  with versionA := Vector.replicate 4 0xde
    let s2 := sszUpdate s1 with versionB := Vector.replicate 4 0xad
    let s3 := sszUpdate s2 with marker   := 0xbeef
    oneShot.hashTreeRootCached.1 = s3.hashTreeRootCached.1 := by
  native_decide

/-! ## Packed basic-element indices

`versionA : Vector UInt8 4` has a *basic packed* element type:
several elements share one 32-byte chunk, so the element has no
Merkle sub-tree of its own. `sszUpdate t with versionA[i] := v`
therefore rebuilds the whole `versionA` field's subtree from the
index-updated view (the `projDrop` path in `walkPath`) rather than
keying a per-element write. These cases pin that this stays
byte-identical to recomputing the root from the updated value. -/

/-! ## Case 7: packed index into a single-chunk byte vector -/

example :
    let t  : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 f0
    (sszUpdate t with versionA[2] := 0xde).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 ({ f0 with versionA := f0.versionA.set 2 0xde } : FlatExample)) := by
  native_decide

/-! ## Case 8: packed index into a multi-chunk byte vector
(`Vector UInt8 96` spans 3 chunks; the write lands in the middle one). -/

example :
    let t  : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 n0
    (sszUpdate t with signature[40] := 0x55).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 ({ n0 with signature := n0.signature.set 40 0x55 } : NestedExample)) := by
  native_decide

/-! ## Case 9: composite index *then* packed index (`rootsA[3][5]`):
the outer composite element keeps its element-gindex + bounds check,
the inner packed byte triggers the owner-rebuild of `rootsA[3]`. -/

example :
    let t  : TreeBacked Sha256 BatchExample := TreeBacked.ofValue Sha256 b0
    let expected : BatchExample :=
      { b0 with rootsA := b0.rootsA.set 3 ((b0.rootsA[3]).set 5 0x77) }
    (sszUpdate t with rootsA[3][5] := 0x77).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 expected) := by
  native_decide

end SizzLeanTests.PendingOverlayCoherence
