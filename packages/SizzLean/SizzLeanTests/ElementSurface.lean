import SizzLean.Repr.Instances

/-!
# `SizzLeanTests.ElementSurface`: element access + collection surface

Acceptance gates for the element-facing API on the capped SSZ collection types
`SSZList` and `Bitlist`, the surface a caller works through without projecting
into the `.val` subtype field.

Two groups:

* **Faithful `GetElem`.** The validity predicate is `fun xs i => i < xs.size`,
  so the three reads behave like `Array`'s: `xs[i]'h` reads with an in-bounds
  proof, `xs[i]?` is a real bounds check (`none` past the end), and `xs[i]!`
  returns the element type's `default` past the end. The `?` / proof forms are
  the load-bearing gate here: the previous `fun _ _ => True` predicate made
  `xs[i]?` *always* `some`, so a past-the-end read never reported `none`.
* **Collection surface.** `toArray` / `toList` / `foldl` / `map` / `mapCap` / `push` /
  `any` / `all` / `findIdx?` / `contains` and the `for x in xs` (`ForIn`) loop on
  `SSZList`, plus `Bitlist.size` / `Bitlist.toArray`. Each delegates to the
  underlying `Array`, so each gate is that it reduces to the `Array` answer.
  `push` (cap-clamping append) and `mapCap` (cap-preserving map) carry a size
  proof, so both their below-cap and at-cap behaviour is gated.
* **Byte-vector coercion.** The `CoeOut (Vector UInt8 n) ByteArray` instance, fired
  at a type ascription and at a `ByteArray`-typed function argument.

`Array`-folding reductions (`map`, `foldl`, `findIdx?`, the option / bang
reads) go through well-founded recursion, so the behavioural checks use
`native_decide`, matching `CollectionInstances`. The definitional projections
(`toArray`, `Bitlist.size`) close by `rfl`.

## Expected panic line

The out-of-range `xs[i]!` / `bs[i]!` checks drive the read past the end, which
prints an `Error: index out of bounds` line to stderr before returning the
`default`. That line is expected, the same as `InfallibleIndex.lean`'s OOB
cases. The authoritative signal is `Build completed successfully`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.ElementSurface

open SizzLean SizzLean.Repr

/-! ## Fixtures: a three-element list and bitlist, both capped at 8 -/

private def xs : SSZList UInt64 8 := ⟨#[10, 20, 30], by decide⟩
private def bs : Bitlist 8 := ⟨#[true, false, true], by decide⟩
/-- A list already at capacity, for the `push` clamp branch. -/
private def full3 : SSZList UInt64 3 := ⟨#[1, 2, 3], by decide⟩
/-- A fixed-length byte vector, for the `Vector UInt8 n → ByteArray` coercion. -/
private def v4 : Vector UInt8 4 := ⟨#[1, 2, 3, 4], by decide⟩

/-! ## Faithful `GetElem` on `SSZList`

The validity predicate is `i < xs.size`, so the proof / option / bang reads
behave like `Array`'s on the same buffer. -/

/-- Proof-carrying read (`xs[i]'h`) returns the element. -/
example : xs[1]'(by decide) = 20 := by native_decide

/-- `xs[i]?` is `some` in bounds. -/
example : xs[2]? = some 30 := by native_decide
/-- `xs[i]?` is `none` past the end. The faithful predicate is what makes this
`none` rather than the old `some` of the `fun _ _ => True` instance. -/
example : xs[7]? = none := by native_decide

/-- `xs[i]!` is the element in bounds. -/
example : xs[0]! = 10 := by native_decide
/-- `xs[i]!` is the element type's `default` (`0` for `UInt64`) past the end. -/
example : xs[7]! = (0 : UInt64) := by native_decide

/-! ## Faithful `GetElem` on `Bitlist` (element type `Bool`) -/

example : bs[0]'(by decide) = true := by native_decide
example : bs[1]? = some false := by native_decide
example : bs[7]? = none := by native_decide
/-- `bs[i]!` is `false` (the `Bool` default) past the end. -/
example : bs[7]! = false := by native_decide

/-! ## `SSZList` collection surface -/

/-- `toArray` is the underlying buffer (definitional, so `rfl`). -/
example : xs.toArray = #[10, 20, 30] := rfl
/-- `toList` of the elements. -/
example : xs.toList = [10, 20, 30] := by native_decide
/-- `foldl` over the elements. -/
example : xs.foldl (· + ·) 0 = 60 := by native_decide
/-- `map` over the elements yields an `Array`. -/
example : xs.map (· + 1) = #[11, 21, 31] := by native_decide
/-- `any`: some element matches. -/
example : xs.any (· == 20) = true := by native_decide
/-- `all`: every element matches / a counterexample exists. -/
example : xs.all (· < 100) = true := by native_decide
example : xs.all (· < 25) = false := by native_decide
/-- `findIdx?` of the first match, `none` when absent. -/
example : xs.findIdx? (· == 30) = some 2 := by native_decide
example : xs.findIdx? (· == 99) = none := by native_decide
/-- `contains` (needs `BEq UInt64`). -/
example : xs.contains 20 = true := by native_decide
example : xs.contains 99 = false := by native_decide

/-- `for x in xs` iterates the elements through the `ForIn` instance. -/
example :
    (Id.run do
      let mut acc : UInt64 := 0
      for x in xs do
        acc := acc + x
      return acc) = 60 := by native_decide

/-! ## `SSZList.push`: cap-clamping append

Below capacity it appends (`xs` is 3 of 8); at capacity it returns the list unchanged
(`full3` is 3 of 3), so the `if size < cap` clamp branch never overflows. -/

/-- Append below capacity grows the list by one. -/
example : (xs.push 99).toArray = #[10, 20, 30, 99] := by native_decide
example : (xs.push 99).val.size = 4 := by native_decide
/-- At capacity, `push` clamps: the list is returned unchanged. -/
example : (full3.push 99).toArray = #[1, 2, 3] := by native_decide
example : (full3.push 99).val.size = 3 := by native_decide

/-! ## `SSZList.mapCap`: cap-preserving map

Unlike `SSZList.map` (which drops to a bare `Array`), `mapCap` stays an `SSZList` at the
same cap, carrying `Array.size_map`. -/

/-- The result is an `SSZList` at the *same* cap (this ascription fails for the bare-`Array`
`map`). -/
example : SSZList UInt64 8 := xs.mapCap (· + 100)
/-- Same-type map: each element shifted, length preserved. -/
example : (xs.mapCap (· + 100)).toArray = #[110, 120, 130] := by native_decide
example : (xs.mapCap (· + 100)).val.size = 3 := by native_decide
/-- Element-type-changing map (`UInt64 → Bool`), still at cap 8. -/
example : (xs.mapCap (· > 15) : SSZList Bool 8).toArray = #[false, true, true] := by native_decide

/-! ## `Bitlist` collection surface -/

/-- Runtime length (definitional projection of `Array.size`). -/
example : bs.size = 3 := rfl
/-- `toArray` is the underlying bit buffer (definitional). -/
example : bs.toArray = #[true, false, true] := rfl

/-! ## `Vector UInt8 n → ByteArray` representation coercion

The `CoeOut` instance lets a fixed-length byte vector flow into a `ByteArray` position
(the wire-bytes seam: a `Root` / pubkey into a hash or BLS-verify argument). It is the
identity on the underlying buffer, `⟨v.toArray⟩`. `CoeOut` (source-keyed) rather than
plain `Coe`, since the source type `Vector UInt8 ?n` is parametric. -/

/-- The coercion fires at a type ascription and is the underlying bytes. -/
example : (v4 : ByteArray).toList = [1, 2, 3, 4] := by native_decide
example : (v4 : ByteArray).size = 4 := by native_decide

/-- The coercion also fires at a `ByteArray`-typed function argument (the real use site). -/
private def consumeBytes (b : ByteArray) : Nat := b.size
example : consumeBytes v4 = 4 := by native_decide

end SizzLeanTests.ElementSurface
