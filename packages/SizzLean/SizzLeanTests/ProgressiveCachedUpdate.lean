import SizzLean.Hasher.Sha256
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLean.Repr.Deriving

/-!
# `SizzLeanTests.ProgressiveCachedUpdate`: field writes into a progressive tree

The cached tree of a progressive container keeps its field sub-trees in
the `merkleize_progressive` shelves, and `sszUpdate` keys a field write
at the field's `progressiveFieldBits` path. A wrong path writes the wrong
shelf or runs past a leaf, so the cached root drifts from the spec root.
The gates below catch both. Each one writes through `SSZ.FastBox` and
compares the cached root with `SSZ.hashTreeRoot` of the updated value.

`Wide` spans three shelves with two gaps: position 0 (shelf 0), positions
2 and 4 (shelf 1, around the gaps at 1 and 3), and positions 5 to 8
(shelf 2). Its fields cover a basic leaf, a classic container, a packed
vector, a composite list, a progressive list, and a nested progressive
container. `Outer` puts a progressive container inside a classic one, so
the progressive path also follows a classic prefix.

The roots are `Sha256` (FFI) digests, so the checks close by
`native_decide` (CLAUDE.md, *Proofs involving SSZ hashes*, case 2).
-/

set_option autoImplicit false

namespace SizzLeanTests.ProgressiveCachedUpdate

open SizzLean
open SizzLean.Repr
open SizzLean.Cache
open SizzLean.Hasher

/-- A classic two-field container. -/
structure Pair where
  a : UInt64
  b : UInt64
  deriving Inhabited, SSZRepr

/-- A progressive container with no gaps. -/
@[sizzlean_progressive]
structure Small where
  x : UInt64
  y : UInt32
  deriving Inhabited, SSZRepr

/-- Seven fields over positions 0 to 8, with gaps at 1 and 3. -/
@[sizzlean_progressive, sizzlean_progressive_gaps 1 3]
structure Wide where
  f0 : UInt64
  f2 : Pair
  f4 : Vector UInt64 4
  f5 : SSZList Pair 4
  f6 : ProgressiveList UInt64
  f7 : Small
  f8 : UInt8
  deriving Inhabited, SSZRepr

/-- A classic container around a progressive one. -/
structure Outer where
  z : UInt64
  p : Small
  deriving Inhabited, SSZRepr

private def wide0 : Wide :=
  { f0 := 1
    f2 := { a := 2, b := 3 }
    f4 := ⟨#[4, 5, 6, 7], by decide⟩
    f5 := ⟨#[{ a := 8, b := 9 }, { a := 10, b := 11 }], by decide⟩
    f6 := ⟨#[12, 13, 14]⟩
    f7 := { x := 15, y := 16 }
    f8 := 17 }

/-- The cached root of `b` equals the spec root of its view. -/
private def agrees (b : SSZ.Box Sha256 Wide) : Bool :=
  b.hashTreeRoot.1 == SSZ.hashTreeRoot Sha256 b.view

/-- Every shelf and every field kind, one write each, with a root read
first so the writes land on a cached tree. -/
private def wideWrites : Bool :=
  let b := SSZ.FastBox wide0
  let (_, b) := b.hashTreeRoot
  let b0 := sszUpdate b with f0 := 100
  let b2 := sszUpdate b with f2.b := 300
  let b4 := sszUpdate b with f4[2]! := 600
  let b5 := sszUpdate b with f5[1]!.a := 1000
  let b6 := sszUpdate b with f6[0]! := 1200
  let b7 := sszUpdate b with f7.y := 1600
  let b8 := sszUpdate b with f8 := 170
  agrees b && agrees b0 && agrees b2 && agrees b4 && agrees b5
    && agrees b6 && agrees b7 && agrees b8

example : wideWrites = true := by native_decide

/-- Writes to several shelves in one statement, then more writes after a
commit, so one spine walk installs sub-trees in several shelves. -/
private def wideBatched : Bool :=
  let b := SSZ.FastBox wide0
  let b := sszUpdate b with f0 := 7, f7.x := 8, f2.a := 9
  let (_, b) := b.hashTreeRoot
  let b := sszUpdate b with f8 := 1, f5[0]!.b := 2
  let ok1 := agrees b
  let (_, b) := b.hashTreeRoot
  let b := sszUpdate b with f4[3]! := 3, f6[2]! := 4, f0 := 5
  ok1 && agrees b

example : wideBatched = true := by native_decide

private def outer0 : Outer := { z := 1, p := { x := 2, y := 3 } }

/-- A progressive container under a classic field: the classic field
path and the progressive field path concatenate. -/
private def outerWrites : Bool :=
  let b := SSZ.FastBox outer0
  let (_, b) := b.hashTreeRoot
  let b1 := sszUpdate b with p.y := 30
  let b2 := sszUpdate b with p.x := 20, z := 10
  b1.hashTreeRoot.1 == SSZ.hashTreeRoot Sha256 b1.view
    && b2.hashTreeRoot.1 == SSZ.hashTreeRoot Sha256 b2.view

example : outerWrites = true := by native_decide

end SizzLeanTests.ProgressiveCachedUpdate
