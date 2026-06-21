import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Box
import SizzLean.Cache.Update

/-!
# `SizzLeanTests.Modify`: the `sszModify` read-modify-write macro

Acceptance gates for `sszModify`, the read-modify-write sugar over
`sszUpdate t with path := … (sszGet t path)` that names the path once. Two forms:

* `sszModify t path := g` applies a function `g` to the current value;
* `sszModify t path as x => body` binds the current value to `x` and rewrites it to
  `body` (the `fun`-free inline form, for `{ x with … }` record updates).

Both expand to the same `sszUpdate` / `sszGet` pair, so the gates check that the result
root matches the directly-updated value and the open-coded form, on the total `[i]!`
element path (where the read returns the bare element) and on a plain field path. They
cover all three flavours, `UncachedSSZ` / `TreeBacked` / `SSZ.Box`. The authoritative
signal is `Build completed successfully`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.Modify

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr

/-- A basic-element list fixture (mirrors `InfallibleIndex.S`). -/
structure S where
  xs     : SSZList UInt64 8
  marker : UInt64
deriving DecidableEq, Inhabited, SSZRepr

private def s0 : S := { xs := ⟨#[10, 20, 30], by decide⟩, marker := 7 }

/-- A struct element, for the `{ x with … }` body form. -/
structure E where
  a : UInt64
  b : UInt64
deriving DecidableEq, Inhabited, SSZRepr

structure S2 where
  es : SSZList E 8
deriving DecidableEq, Inhabited, SSZRepr

private def t0 : S2 := { es := ⟨#[{ a := 1, b := 2 }, { a := 3, b := 4 }], by decide⟩ }

/-! ## Both forms return the bare box on a total `[i]!` path (no `Except`)

These ascriptions fail to typecheck if the result were wrapped in `Except`. -/

example : SSZ.Box Sha256 S := sszModify (SSZ.FastBox s0) xs[1]! := (fun w => w + 5)
example : SSZ.Box Sha256 S := sszModify (SSZ.FastBox s0) xs[1]! as v => v + 5

/-! ## `:= g`: root matches the directly-updated value (`xs[1] = 20`, `+5 = 25`) -/

example :
    ((sszModify (SSZ.FastBox s0) xs[1]! := (fun w => w + 5)).hashTreeRoot).1
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 25 } : S) := by
  native_decide

/-! ## `as x => body`: root matches the directly-updated value (`20 * 2 = 40`) -/

example :
    ((sszModify (SSZ.FastBox s0) xs[1]! as v => v * 2).hashTreeRoot).1
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 40 } : S) := by
  native_decide

/-! ## `as x => body` with a `{ x with … }` record update (the motivating case)

`es[0] = { a := 1, b := 2 }`, so `a + 10` gives `{ a := 11, b := 2 }`. -/

example :
    ((sszModify (SSZ.FastBox t0) es[0]! as e => { e with a := e.a + 10 }).hashTreeRoot).1
      = SSZ.hashTreeRoot Sha256 ({ t0 with es := t0.es.set! 0 { a := 11, b := 2 } } : S2) := by
  native_decide

/-! ## A plain field path (no index segment) -/

example :
    ((sszModify (SSZ.FastBox s0) marker := (fun m => m + 1)).hashTreeRoot).1
      = SSZ.hashTreeRoot Sha256 ({ s0 with marker := 8 } : S) := by
  native_decide

/-! ## `sszModify` is exactly its desugaring -/

example :
    ((sszModify (SSZ.FastBox s0) xs[1]! := (fun w => w + 5)).hashTreeRoot).1
      = ((sszUpdate (SSZ.FastBox s0) with xs[1]! := (sszGet (SSZ.FastBox s0) xs[1]!) + 5).hashTreeRoot).1 := by
  native_decide

/-! ## The two forms agree -/

example :
    ((sszModify (SSZ.FastBox s0) xs[1]! := (fun w => w + 5)).hashTreeRoot).1
      = ((sszModify (SSZ.FastBox s0) xs[1]! as v => v + 5).hashTreeRoot).1 := by
  native_decide

/-! ## The uncached and `TreeBacked` flavours also accept it -/

example : UncachedSSZ Sha256 S := sszModify (UncachedSSZ.ofValue Sha256 s0) xs[1]! := (fun w => w + 5)
example : TreeBacked Sha256 S := sszModify (TreeBacked.ofValue Sha256 s0) xs[2]! as v => v + 1

/-! ## `sszAppend` appends to a list field (cap-clamping `SSZList.push`) -/

example : SSZ.Box Sha256 S := sszAppend (SSZ.FastBox s0) xs 99

example :
    ((sszAppend (SSZ.FastBox s0) xs 99).hashTreeRoot).1
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.push 99 } : S) := by
  native_decide

end SizzLeanTests.Modify
