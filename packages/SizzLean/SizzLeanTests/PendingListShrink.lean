import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.PendingListShrink`: element writes, shrink, and OOB

`sszUpdate t with xs[i] := v` is an *index* form, so it returns
`Except IndexError (TreeBacked …)`: the eager view write is
bounds-checked **in program order**, and an out-of-range index
rejects with `.error .indexError` (the SSZ-level surface of the
pyspec's `IndexError`). Two distinct OOB moments, handled differently
and both exercised here:

* **Issue-time OOB**: the index is already out of range against the
  view *at the moment the write is issued*. The guard fails and the
  whole `sszUpdate` returns `.error`; nothing is written and no pending
  entry is recorded. (Cases 2, 4, 5, 7.)
* **Commit-time supersession**: the index is in range at issue (so the
  write is `.ok` and a pending closure is recorded), but a *later*
  whole-field write shrinks the field so the index no longer exists.
  The deferred closure re-checks its bound against the final view at
  commit, returns `none`, and is dropped, the cached root still
  matches `SSZ.hashTreeRoot view`. (Case 1.)

In-bounds writes (Cases 3, 6, 8) succeed and the cached root matches the
recomputed root. Assertions compare at the `Option`/`Bool` level
(`.toOption.map … = some root`, `.toOption.isNone = true`) since
`Except`/`TreeBacked` carry no `DecidableEq`; every check is byte-exact
via `native_decide`. No `Array.set!` OOB panic output is produced any
more: the guard rejects before the view write on issue-OOB, and the
commit closure's own bound check avoids the OOB projection.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.PendingListShrink

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr
open SizzLeanTests.ExampleContainers

private def mk (k : UInt8) : ExRoot := Vector.replicate 32 k

/-- Initial `vals` with 5 distinct entries (cap 8). -/
private def initialVals : SSZList ExRoot 8 :=
  ⟨#[mk 0x11, mk 0x22, mk 0x33, mk 0x44, mk 0x55], by decide⟩

/-- `initialVals` truncated to length 2, positions 2..4 disappear. -/
private def shorterVals : SSZList ExRoot 8 :=
  ⟨#[mk 0xa1, mk 0xa2], by decide⟩

private def s0 : ListShrinkExample :=
  { vals := initialVals, marker := 7 }

/-! ## Case 1: in-bounds index, then shorten (commit-time supersession)

`xs[3] := v` (3 < 5, in bounds ⇒ `.ok`, pending records `vals[3]`),
then `xs := shorter` (length 2). At commit the `vals[3]` closure
re-checks `3 < 2`, returns `none`, and is dropped; only the whole-list
write survives, so the root matches `shorter`. -/
example :
    (((sszUpdate (TreeBacked.ofValue Sha256 s0) with vals[3] := mk 0xff)
      >>= fun t1 => Except.ok (sszUpdate t1 with vals := shorterVals)).toOption.map
        (·.hashTreeRootCached.1))
      = some (SSZ.hashTreeRoot Sha256 ({ s0 with vals := shorterVals } : ListShrinkExample)) := by
  native_decide

/-! ## Case 2: shorten, then index OOB in the shortened list (issue-time OOB)

`xs := shorter` (length 2), then `xs[3] := v`: at issue `vals` is
already length 2, so `3` is out of range ⇒ the second `sszUpdate`
rejects. -/
example :
    (sszUpdate (sszUpdate (TreeBacked.ofValue Sha256 s0) with vals := shorterVals)
      with vals[3] := mk 0xff).toOption.isNone = true := by
  native_decide

/-! ## Case 3: bare in-bounds index -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with vals[3] := mk 0xff).toOption.map
        (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256
          ({ s0 with vals := initialVals.set! 3 (mk 0xff) } : ListShrinkExample)) := by
  native_decide

/-! ## Case 4: bare OOB index past current length ⇒ reject -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with vals[6] := mk 0xff).toOption.isNone = true := by
  native_decide

/-! ## Case 5: bare OOB index, non-zero-`Inhabited` element type ⇒ reject

Same rejection regardless of `default α`: the guard fails before any
projection, so `default NonZeroElem` is never consulted. -/
private def nzInitial : SSZList NonZeroElem 8 :=
  ⟨#[{ a := 10, b := 20 },
     { a := 11, b := 21 },
     { a := 12, b := 22 }], by decide⟩

private def nz0 : NonZeroListExample :=
  { vals := nzInitial, marker := 7 }

example :
    (sszUpdate (TreeBacked.ofValue Sha256 nz0) with vals[6] := { a := 99, b := 99 }).toOption.isNone = true := by
  native_decide

/-! ## Case 6: same-statement whole-list write + in-bounds index

`vals := shorter, vals[1] := v`: the index `1` is in range in the
original view, so the statement is `.ok`; the view let-chain applies
`shorter` then `set! 1`, giving `shorter.set! 1 v`. -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with
      vals    := shorterVals,
      vals[1] := mk 0xee).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256
          ({ s0 with vals := shorterVals.set! 1 (mk 0xee) } : ListShrinkExample)) := by
  native_decide

/-! ## Case 7: same-statement whole-list write + OOB index ⇒ reject

`vals := shorter, vals[6] := v`: index `6` is out of range in the
original (length 5) view, so the statement rejects. -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with
      vals    := shorterVals,
      vals[6] := mk 0xff).toOption.isNone = true := by
  native_decide

/-! ## Case 8: reverse-order multi-clause, in-bounds index

`vals[1] := v, vals := shorter`: index `1` in range ⇒ `.ok`; the
whole-list write runs second in the view let-chain, so the final view
is `shorter`. -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with
      vals[1] := mk 0xcc,
      vals    := shorterVals).toOption.map (·.hashTreeRootCached.1)
      = some (SSZ.hashTreeRoot Sha256 ({ s0 with vals := shorterVals } : ListShrinkExample)) := by
  native_decide

end SizzLeanTests.PendingListShrink
