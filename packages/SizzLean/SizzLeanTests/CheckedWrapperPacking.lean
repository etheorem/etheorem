import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Update

/-!
# `SizzLeanTests.CheckedWrapperPacking`: indexed writes into a checked wrapper

The `sszUpdate` cached-write path classifies a `Vector` / `SSZList`
element as basic-packed or composite. When that decision read the
Lean *type name* (`Bool`, `UInt8..UInt64`, `BitVec _`), a checked
wrapper (a `structure` over `UInt64` whose `SSZRepr.shape` is
`.uintN 64`) fell through to composite. The write then keyed a
`PendingWrite` at a per-element subtree gindex, which is the wrong
address for a packed field: the cached root went stale while the
serialized view stayed byte-correct.

These gates pin the shape-based classification with a wrapper that
is independent of any consensus-spec package. Every case checks two
facts, and the two are deliberately separate:

* the cached root after the write equals a *fresh* merkleization
  (`SSZ.hashTreeRoot`) of the plain updated value, built without
  the cache;
* serialization of the cached value is byte-correct
  (`SSZ.serialize t'.view` equals `SSZ.serialize` of the plain
  updated value).

A regression that only broke the cache shows up in the first check
alone. A regression that broke the view shows up in the second.

Coverage:

* (a) one indexed write into a packed `SSZList` of wrappers;
* (b) one indexed write into a packed `Vector` of wrappers;
* (c) writes on both sides of a chunk boundary (four `.uintN 64`
  values fill one 32-byte chunk, so indexes 3 and 4 sit in
  different chunks);
* (d) two writes to the same index (the second wins);
* (e) a root taken *before* an indexed write, compared after.
-/

set_option autoImplicit false

namespace SizzLeanTests.CheckedWrapperPacking

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr

/-! ### The wrapper and its containers

`Wrapper64` is the checked-arithmetic stand-in: a `structure` over
`UInt64` with a hand-written `SSZRepr` whose shape is `.uintN 64`.
Nothing about it depends on `EthCLLib` or `EthCLSpecs`. -/

/-- A checked wrapper over `UInt64`. Its SSZ wire shape is
`.uintN 64`, so SSZ packs four wrappers per 32-byte chunk, exactly
like a bare `UInt64`. -/
structure Wrapper64 where
  raw : UInt64
deriving DecidableEq, Inhabited

/-- Hand-written instance with the `.uintN 64` shape and the
identity iso. The iso is definitional: `interp (.uintN 64)`
reduces to `UInt64`, and structure eta makes `⟨x.raw⟩` and `x`
the same term, so both laws close by `rfl`. -/
instance : SSZRepr Wrapper64 where
  shape    := .uintN 64
  toRepr   := fun x => x.raw
  fromRepr := fun r => ⟨r⟩
  to_from  := fun _ => rfl
  from_to  := fun _ => rfl

/-- Spot-check that the shape the classifier reads is `.uintN 64`. -/
example : SSZRepr.shape (T := Wrapper64) = .uintN 64 := rfl

/-- A two-field container whose `xs` is a capped list of wrappers.
Four wrappers fill one chunk, so the list packs. -/
structure WList where
  xs     : SSZList Wrapper64 16
  marker : UInt64
deriving DecidableEq, Inhabited, SSZRepr

/-- A two-field container whose `ys` is a fixed `Vector` of eight
wrappers: two chunks of four. -/
structure WVec where
  ys     : Vector Wrapper64 8
  marker : UInt64
deriving DecidableEq, Inhabited, SSZRepr

private def wlist0 : WList :=
  { xs := ⟨#[⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩, ⟨50⟩, ⟨60⟩], by decide⟩, marker := 7 }

private def wvecOf (f : Nat → UInt64) : WVec :=
  { ys := Vector.ofFn (fun (i : Fin 8) => ⟨f i.val⟩), marker := 9 }

private def wvec0 : WVec := wvecOf (fun i => Nat.toUInt64 (i + 1))

/-! ### (a) One indexed write into a packed `SSZList` of wrappers -/

example :
    let upd : WList := { wlist0 with xs := wlist0.xs.set! 1 ⟨77⟩ }
    let t := TreeBacked.ofValue Sha256 wlist0
    let t' := sszUpdate t with xs[1]! := ⟨77⟩
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 upd
      ∧ SSZ.serialize t'.view = SSZ.serialize upd := by
  native_decide

/-- The same write through the checked `[i]` form, which threads
`Except IndexError`. -/
example :
    let r := (sszUpdate (TreeBacked.ofValue Sha256 wlist0) with xs[1] := ⟨77⟩)
    let upd : WList := { wlist0 with xs := wlist0.xs.set! 1 ⟨77⟩ }
    (match r with
     | .ok t' =>
         t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 upd
           ∧ SSZ.serialize t'.view = SSZ.serialize upd
     | .error _ => false) = true := by
  native_decide

/-! ### (b) One indexed write into a packed `Vector` of wrappers -/

example :
    let upd : WVec := { wvec0 with ys := wvec0.ys.set! 5 ⟨55⟩ }
    let t := TreeBacked.ofValue Sha256 wvec0
    let t' := sszUpdate t with ys[5]! := ⟨55⟩
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 upd
      ∧ SSZ.serialize t'.view = SSZ.serialize upd := by
  native_decide

/-! ### (c) Writes on both sides of a chunk boundary

Four `.uintN 64` values fill one 32-byte chunk. Index 3 is the
last element of chunk 0 and index 4 the first element of chunk 1,
so the two writes land in different chunks of the same field. -/

example :
    let upd : WVec :=
      { wvec0 with ys := (wvec0.ys.set! 3 ⟨300⟩).set! 4 ⟨400⟩ }
    let t := TreeBacked.ofValue Sha256 wvec0
    let t' := sszUpdate t with ys[3]! := ⟨300⟩, ys[4]! := ⟨400⟩
    t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 upd
      ∧ SSZ.serialize t'.view = SSZ.serialize upd := by
  native_decide

/-! ### (d) Two writes to the same index

Both clauses key the same owning-field gindex. The view applies
them in order, so the second wins, and the committed root must
describe that final value. -/

example :
    let upd : WList := { wlist0 with xs := wlist0.xs.set! 2 ⟨42⟩ }
    let t := TreeBacked.ofValue Sha256 wlist0
    let t' := sszUpdate t with xs[2]! := ⟨99⟩, xs[2]! := ⟨42⟩
    t'.view.xs[2]! = ⟨42⟩
      ∧ t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 upd
      ∧ SSZ.serialize t'.view = SSZ.serialize upd := by
  native_decide

/-! ### (e) A root taken before an indexed write

The pre-write cached root describes the pre-write value. After the
write, the cached root must describe the updated value, not reuse
the pre-write one; a stale cache fails the second comparison. -/

example :
    let t := TreeBacked.ofValue Sha256 wvec0
    let before := t.hashTreeRootCached.1
    let beforeOk := before = SSZ.hashTreeRoot Sha256 wvec0
    let upd : WVec := { wvec0 with ys := wvec0.ys.set! 3 ⟨300⟩ }
    let t' := sszUpdate t with ys[3]! := ⟨300⟩
    beforeOk
      ∧ t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 upd
      ∧ SSZ.serialize t'.view = SSZ.serialize upd
      ∧ t'.hashTreeRootCached.1 ≠ before := by
  native_decide

/-! ### The uncached flavour agrees on the view side

The uncached path never touches the Merkle vocabulary, so the
wrapper write reduces to the plain `set!` rewrite. Pinned with
`rfl`, matching the house pattern in `TreeBackedSetField.lean`. -/

example :
    (sszUpdate (UncachedSSZ.ofValue Sha256 wlist0) with xs[1]! := ⟨77⟩).view
      = { wlist0 with xs := wlist0.xs.set! 1 ⟨77⟩ } := by
  rfl

end SizzLeanTests.CheckedWrapperPacking
