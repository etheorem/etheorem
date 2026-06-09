import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.WidthsAndLists`, regression net for basic widths and list sizes

The cache invariant is `t.hashTreeRootCached = SSZ.hashTreeRoot t.view`
for every `t : TreeBacked Sha256 T`. This file pins that invariant
across two dimensions the previous tests only sampled lightly:

* **Field widths**: basic types from 1 bit (`Bool`) to 256 bits
  (`BitVec 256`), exercising the per-width chunk-padding path
  `Node.ofShape` uses for each `.uintN n` / `.bool` arm.
* **List size changes**: SSZList writes that empty, grow,
  shrink, or saturate the underlying cap. Each size change has
  to rebuild the body tree at one shape and rewrite the
  mix-in-length leaf to the new actual size; this is the path
  the user's "writes only contain one gindex" concern was
  asking about.

Tests run through both `TreeBacked.ofValue` (the low-level
cache wrapper) and `SSZ.FastBox` (the user-facing Box). Both
ultimately call the same `commit` walk, but routing through
`Box` exercises the inductive Box constructors + dispatch the
`sszUpdate` macro adds on top.

When something regresses here, the failure points directly at the
offending feature: a width-specific bug surfaces in one `example`
block, a list-size bug in another.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SizzLeanTests.WidthsAndLists

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr
open SizzLeanTests.ExampleContainers

/-! ## Fixture, `WidthsExample` covers every basic width plus a list -/

/-- Container with every basic SSZ width as a field, plus a
`Vector` and an `SSZList` for size-change tests. The field
order ensures each width is at a distinct gindex inside the
container's depth-`chunkDepth 9` tree. -/
structure WidthsExample where
  flag    : Bool          -- 1 bit (1 byte serialised, 1 chunk)
  byte    : UInt8         -- 8 bit
  word    : UInt16        -- 16 bit
  dword   : UInt32        -- 32 bit
  qword   : UInt64        -- 64 bit
  u128    : BitVec 128    -- 128 bit
  u256    : BitVec 256    -- 256 bit (exactly one chunk wide)
  vec     : Vector ExRoot 4
  lst     : SSZList ExRoot 8
deriving DecidableEq, SSZRepr

private def mk (k : UInt8) : ExRoot := Vector.replicate 32 k

private def w0 : WidthsExample :=
  { flag  := false
    byte  := 0x11
    word  := 0x2233
    dword := 0x44556677
    qword := 0x8899aabbccddeeff
    u128  := BitVec.ofNat 128 0x10203040
    u256  := BitVec.ofNat 256 0xabcdef
    vec   := Vector.ofFn (fun (i : Fin 4) => mk (UInt8.ofNat (i.val + 1)))
    lst   := ⟨#[mk 0xa1, mk 0xa2, mk 0xa3], by decide⟩ }

private def emptyLst : SSZList ExRoot 8 :=
  ⟨#[], by decide⟩

private def oneLst : SSZList ExRoot 8 :=
  ⟨#[mk 0xb1], by decide⟩

private def fullLst : SSZList ExRoot 8 :=
  ⟨#[mk 0xc0, mk 0xc1, mk 0xc2, mk 0xc3,
     mk 0xc4, mk 0xc5, mk 0xc6, mk 0xc7], by decide⟩

private def growLst : SSZList ExRoot 8 :=
  ⟨#[mk 0xd0, mk 0xd1, mk 0xd2, mk 0xd3, mk 0xd4, mk 0xd5], by decide⟩

private def shrinkLst : SSZList ExRoot 8 :=
  ⟨#[mk 0xe0], by decide⟩

/-! ## Single-field width writes (CachedSSZ direct) -/

/-- 1-bit `Bool` field. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with flag := true
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with flag := true } : WidthsExample) := by
  native_decide

/-- 8-bit `UInt8` field. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with byte := 0xfe
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with byte := 0xfe } : WidthsExample) := by
  native_decide

/-- 16-bit `UInt16` field. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with word := 0xfedc
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with word := 0xfedc } : WidthsExample) := by
  native_decide

/-- 32-bit `UInt32` field, boundary width (one Lean machine word
on 32-bit targets, half-word on 64-bit). -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with dword := 0xfedcba98
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with dword := 0xfedcba98 } : WidthsExample) := by
  native_decide

/-- 64-bit `UInt64` field. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with qword := 0x123456789abcdef0
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256
        ({ w0 with qword := 0x123456789abcdef0 } : WidthsExample) := by
  native_decide

/-- 128-bit `BitVec 128`, wider than a machine word, still
narrower than a chunk (16 bytes vs 32). -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let newU128 : BitVec 128 := BitVec.ofNat 128 0xdeadbeefcafef00d
    let t' := sszUpdate t with u128 := newU128
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with u128 := newU128 } : WidthsExample) := by
  native_decide

/-- 256-bit `BitVec 256`, exactly one chunk wide; the chunk
leaf is the bytes themselves with no padding. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let newU256 : BitVec 256 := BitVec.ofNat 256 0xfeedfacefeedface
    let t' := sszUpdate t with u256 := newU256
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with u256 := newU256 } : WidthsExample) := by
  native_decide

/-! ## Single-field width writes (SSZ.FastBox) -/

/-- Same `Bool` write, but through the user-facing `SSZ.FastBox`
constructor. Validates the Box dispatch path. -/
example :
    let box : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let box' := sszUpdate box with flag := true
    let (root, _) := box'.hashTreeRoot
    root = SSZ.hashTreeRoot Sha256 ({ w0 with flag := true } : WidthsExample) := by
  native_decide

/-- Same `UInt64` write through `SSZ.FastBox`. -/
example :
    let box : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let box' := sszUpdate box with qword := 0xdeadbeef
    let (root, _) := box'.hashTreeRoot
    root = SSZ.hashTreeRoot Sha256
      ({ w0 with qword := 0xdeadbeef } : WidthsExample) := by
  native_decide

/-- Same `BitVec 256` write through `SSZ.FastBox`. -/
example :
    let box : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let v : BitVec 256 := BitVec.ofNat 256 0x12345678
    let box' := sszUpdate box with u256 := v
    let (root, _) := box'.hashTreeRoot
    root = SSZ.hashTreeRoot Sha256 ({ w0 with u256 := v } : WidthsExample) := by
  native_decide

/-! ## Multi-clause width writes (one `sszUpdate` statement) -/

/-- All sub-32-bit fields in one statement. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with
      flag := true,
      byte := 0xff,
      word := 0xffff
    let expected : WidthsExample :=
      { w0 with flag := true, byte := 0xff, word := 0xffff }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-- All ≥ 64-bit fields in one statement. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let v128 : BitVec 128 := BitVec.ofNat 128 0xdeadbeef
    let v256 : BitVec 256 := BitVec.ofNat 256 0xfeedfacefeedface
    let t' := sszUpdate t with
      qword := 0x1234,
      u128  := v128,
      u256  := v256
    let expected : WidthsExample :=
      { w0 with qword := 0x1234, u128 := v128, u256 := v256 }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-- Every basic-type field in one statement. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let v128 : BitVec 128 := BitVec.ofNat 128 0xaa
    let v256 : BitVec 256 := BitVec.ofNat 256 0xbb
    let t' := sszUpdate t with
      flag  := true,
      byte  := 7,
      word  := 77,
      dword := 7777,
      qword := 777777,
      u128  := v128,
      u256  := v256
    let expected : WidthsExample :=
      { w0 with flag := true, byte := 7, word := 77, dword := 7777,
                qword := 777777, u128 := v128, u256 := v256 }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Same-field overwrite, multi-statement -/

/-- Two writes at the same gindex; the second one wins
(`TreeMap.insert` dedup). -/
example :
    let t  : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t1 := sszUpdate t  with byte := 0x11
    let t2 := sszUpdate t1 with byte := 0xfe
    t2.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with byte := 0xfe } : WidthsExample) := by
  native_decide

/-- Same-field overwrite in one statement (left-to-right last wins). -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with qword := 1, qword := 2, qword := 3
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with qword := 3 } : WidthsExample) := by
  native_decide

/-! ## List-size changes: CachedSSZ -/

/-- Shrink list to empty. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with lst := emptyLst
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := emptyLst } : WidthsExample) := by
  native_decide

/-- Shrink to one element. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with lst := oneLst
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := oneLst } : WidthsExample) := by
  native_decide

/-- Shrink (initial 3 → final 1). -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with lst := shrinkLst
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := shrinkLst } : WidthsExample) := by
  native_decide

/-- Grow (initial 3 → final 6). -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with lst := growLst
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := growLst } : WidthsExample) := by
  native_decide

/-- Grow to exact cap (8 of 8). -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with lst := fullLst
    t'.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := fullLst } : WidthsExample) := by
  native_decide

/-- Shrink from cap-full back to empty. -/
example :
    let t  : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t1 := sszUpdate t  with lst := fullLst
    let t2 := sszUpdate t1 with lst := emptyLst
    t2.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := emptyLst } : WidthsExample) := by
  native_decide

/-- Empty then grow back. -/
example :
    let t  : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t1 := sszUpdate t  with lst := emptyLst
    let t2 := sszUpdate t1 with lst := growLst
    t2.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := growLst } : WidthsExample) := by
  native_decide

/-! ## List-size changes: `SSZ.FastBox` -/

/-- Shrink-to-empty via `SSZ.FastBox`. -/
example :
    let box : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let box' := sszUpdate box with lst := emptyLst
    let (root, _) := box'.hashTreeRoot
    root = SSZ.hashTreeRoot Sha256 ({ w0 with lst := emptyLst } : WidthsExample) := by
  native_decide

/-- Grow-to-cap via `SSZ.FastBox`. -/
example :
    let box : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let box' := sszUpdate box with lst := fullLst
    let (root, _) := box'.hashTreeRoot
    root = SSZ.hashTreeRoot Sha256 ({ w0 with lst := fullLst } : WidthsExample) := by
  native_decide

/-! ## Mixed field + list -/

/-- Set a sub-32-bit field and shrink the list in one statement. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t' := sszUpdate t with
      byte := 0xab,
      lst  := emptyLst
    let expected : WidthsExample := { w0 with byte := 0xab, lst := emptyLst }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-- Set a ≥ 64-bit field and grow the list in one statement. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let v256 : BitVec 256 := BitVec.ofNat 256 0xdead
    let t' := sszUpdate t with
      u256 := v256,
      lst  := fullLst
    let expected : WidthsExample := { w0 with u256 := v256, lst := fullLst }
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-- Width writes spanning all sizes plus a list resize. -/
example :
    let box : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let v128 : BitVec 128 := BitVec.ofNat 128 0x42
    let box' := sszUpdate box with
      flag  := true,
      byte  := 0xcc,
      word  := 0xcccc,
      dword := 0xccccccc,
      qword := 0x42424242,
      u128  := v128,
      lst   := growLst
    let (root, _) := box'.hashTreeRoot
    let expected : WidthsExample :=
      { w0 with flag := true, byte := 0xcc, word := 0xcccc,
                dword := 0xccccccc, qword := 0x42424242, u128 := v128,
                lst := growLst }
    root = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Multi-statement chains with size + width interplay -/

/-- Width write, then list shrink, then another width write. -/
example :
    let t  : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t1 := sszUpdate t  with qword := 0xdead
    let t2 := sszUpdate t1 with lst   := emptyLst
    let t3 := sszUpdate t2 with byte  := 0xff
    let expected : WidthsExample :=
      { w0 with qword := 0xdead, lst := emptyLst, byte := 0xff }
    t3.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-- List grow then shrink in two statements; final state is the
shrunk list, the intermediate growth is never observed at the
root. -/
example :
    let t  : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let t1 := sszUpdate t  with lst := fullLst
    let t2 := sszUpdate t1 with lst := oneLst
    t2.hashTreeRootCached.1 =
      SSZ.hashTreeRoot Sha256 ({ w0 with lst := oneLst } : WidthsExample) := by
  native_decide

/-- A width write at a small field doesn't interfere with a
list-shrink that happens in a later statement. -/
example :
    let box  : SSZ.Box Sha256 WidthsExample := SSZ.FastBox w0
    let box1 : SSZ.Box Sha256 WidthsExample := sszUpdate box  with flag := true
    let box2 : SSZ.Box Sha256 WidthsExample := sszUpdate box1 with lst := emptyLst
    let box3 : SSZ.Box Sha256 WidthsExample := sszUpdate box2 with word := 0x9999
    let (root, _) := box3.hashTreeRoot
    let expected : WidthsExample :=
      { w0 with flag := true, lst := emptyLst, word := 0x9999 }
    root = SSZ.hashTreeRoot Sha256 expected := by
  native_decide

/-! ## Vector inside the same container -/

/-- Single composite-Vector element write, exercises the
Vector-of-`ExRoot` (composite element) index syntax. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let expected : WidthsExample :=
      { w0 with vec := w0.vec.set 2 (mk 0x77) (by decide) }
    (sszUpdate t with vec[2] := mk 0x77).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 expected) := by
  native_decide

/-- Vector index write + width write + list resize in one
statement, three different shape paths in one commit. -/
example :
    let t : TreeBacked Sha256 WidthsExample := TreeBacked.ofValue Sha256 w0
    let expected : WidthsExample :=
      { w0 with vec := w0.vec.set 0 (mk 0x88) (by decide),
                qword := 0xbeef,
                lst := fullLst }
    (sszUpdate t with
      vec[0] := mk 0x88,
      qword  := 0xbeef,
      lst    := fullLst).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 expected) := by
  native_decide

end SizzLeanTests.WidthsAndLists
