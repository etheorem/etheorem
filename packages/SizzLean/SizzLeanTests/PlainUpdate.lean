import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Box
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.PlainUpdate`: the plain arms of `sszUpdate` and `sszGet`

Acceptance gates for the temporary plain-value dispatch arm of
`sszUpdate` (the fourth arm of `elabSszUpdate`) and the plain arm of
the type-directed `sszGet` (`elabSszGet`). When the base
term's type is none of `TreeBacked H T` / `UncachedSSZ H T` /
`SSZ.Box H T`, the macro emits the view-side update rooted at the
base itself, so on a plain SSZ struct

* a one-clause field write `sszUpdate t with f := v` *is* the record
  update `{ t with f := v }` — literally the same elaborated term,
  no `let`, no wrapper — which the `example … := rfl` gates below
  pin (the property the boxed-to-plain switch stages rely on:
  proofs written against the record spelling stay valid);
* an element clause `fs[i]! := v` is `{ t with fs := t.fs.set! i v }`,
  the same view-side emission the cache flavours build;
* several clauses run the cache flavours' `let`-chain with the base
  as the root read: every right-hand side is evaluated against the
  original base, exactly like a multi-field record update, and
  shared-prefix clauses compose;
* a *checked* `[i]` segment is a compile error (the plain arm has no
  `Except` result to reject into); the infallible `[i]!` form, whose
  out-of-range write is a no-op, covers the plain mode;
* a read `sszGet t path` *is* the projection `t.path`, literally the
  same elaborated term (the `with_unfolding_none rfl` gates below
  compare the terms with no unfolding at all), while a cache value
  still reads through `.view`. A checked `[i]` read keeps its
  `Except IndexError _` result on a plain base too;
* `sszModify` (both forms) and `sszAppend?` work unchanged on a plain
  value, because they expand to `sszGet` and `sszUpdate`.

The cases mirror `Modify.lean`, `InfallibleIndex.lean` and
`MultiSetterIndex.lean` on a plain value, plus one
`@[sizzlean_progressive]` container, which needs no special case
because the plain arms emit view-side code only. Value and
root comparisons involve SSZ hashes / array primitives, so they
close by `native_decide` (CLAUDE.md, *Proofs involving SSZ hashes*,
case 2 and the array-reduction caveat).

## Expected panic lines

The out-of-range `[i]!` cases below drive `Array.set!` and the `get!`
read past the end. Each one prints an `index out of bounds` line
(with a `PANIC` prefix for the read) before it returns the array
unchanged or the element's `default`. Those lines are expected; the
authoritative signal is `Build completed successfully`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.PlainUpdate

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr
open SizzLeanTests.ExampleContainers

/-! ## Fixtures

`S`, `E` and `S2` mirror the fixtures of `Modify.lean` /
`InfallibleIndex.lean`; `n0` exercises one nesting level through
`NestedExample` from `ExampleContainers`. -/

/-- A basic-element list fixture (mirrors `InfallibleIndex.S`). -/
structure S where
  xs     : SSZList UInt64 8
  marker : UInt64
  deriving DecidableEq, Inhabited, SSZRepr

private def s0 : S := { xs := ⟨#[10, 20, 30], by decide⟩, marker := 7 }

/-- A struct element, for the `{ x with … }` read-modify-write body. -/
structure E where
  a : UInt64
  b : UInt64
  deriving DecidableEq, Inhabited, SSZRepr

structure S2 where
  es : SSZList E 8
  deriving DecidableEq, Inhabited, SSZRepr

private def t0 : S2 := { es := ⟨#[{ a := 1, b := 2 }, { a := 3, b := 4 }], by decide⟩ }

/-- A nested fixture: one inner-struct field plus a sibling vector,
shape mirrors `SignedBeaconBlockHeader`. -/
private def n0 : NestedExample :=
  { message :=
      { slot := 1, marker := 2
        rootA := Vector.replicate 32 1
        rootB := Vector.replicate 32 2
        rootC := Vector.replicate 32 3 }
    signature := Vector.replicate 96 4 }

/-! ## The result is the plain value, not `Except`

These ascriptions fail to typecheck if the plain arm wrapped the
result (no clause below uses a checked index). -/

example : S := sszUpdate s0 with marker := 8
example : S := sszUpdate s0 with xs[1]! := 99
example : S := sszUpdate s0 with marker := 8, xs[1]! := 99
example : NestedExample := sszUpdate n0 with message.slot := 42, message.marker := 7

/-! ## One-clause forms are the hand-written record updates

The plain arm emits the bare record update with no `let`, so each
gate closes by `rfl` against the plain spelling the switch stages
move the spec bodies to. -/

/-- Flat field. -/
example : (sszUpdate s0 with marker := 8) = { s0 with marker := 8 } := rfl

/-- Infallible element write: `.set!` on the field. -/
example :
    (sszUpdate s0 with xs[1]! := 99) = { s0 with xs := s0.xs.set! 1 99 } := rfl

/-- Nested field: one record update per path level. -/
example :
    (sszUpdate n0 with message.slot := 42)
      = { n0 with message := { n0.message with slot := 42 } } := rfl

/-! ## Several clauses: the `let`-chain, every RHS against the original base

The chain composes clause by clause, like nested record updates;
clause right-hand sides read the original `s0` / `t₀`, matching
multi-field record-update semantics. -/

/-- Two clauses, field and element mixed. -/
example :
    (sszUpdate s0 with marker := 8, xs[1]! := 99)
      = { { s0 with marker := 8 } with xs := s0.xs.set! 1 99 } := by
  native_decide

/-- Two clauses writing the same list in sequence: the second reads
the list the first wrote (`#[10, 21, 2]`, not `#[10, 21, 30]`). -/
example :
    (sszUpdate s0 with xs[1]! := 21, xs[2]! := 2)
      = (let l := s0.xs.set! 1 21
         { { s0 with xs := l } with xs := l.set! 2 2 }) := by
  native_decide

/-- Shared-prefix clauses compose: the second nested write reads the
inner struct the first one produced. -/
example :
    (sszUpdate n0 with message.slot := 42, message.marker := 7)
      = (let v1 : NestedExample := { n0 with message := { n0.message with slot := 42 } }
         { v1 with message := { v1.message with marker := 7 } }) := by
  native_decide

/-! ## The `InfallibleIndex` cases on a plain value

In-range `[i]!` writes match the directly-updated value; an
out-of-range `[i]!` write is a silent no-op (`Array.set!` semantics),
so the value and root are unchanged. -/

/-- In range: the root matches the hand-written record update. -/
example :
    SSZ.hashTreeRoot Sha256 (sszUpdate s0 with xs[1]! := 99)
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 99 } : S) := by
  native_decide

/-- Out of range (`xs` holds 3 of 8): no-op, root unchanged. -/
example :
    SSZ.hashTreeRoot Sha256 (sszUpdate s0 with xs[7]! := 99)
      = SSZ.hashTreeRoot Sha256 s0 := by
  native_decide

/-! ## The `Modify` write forms, spelled through `sszUpdate`

The two body forms of `sszModify`, spelled by hand through
`sszUpdate`, with the read on the right-hand side in plain
projection syntax. The section *`sszModify` and `sszAppend?` on a
plain value* below runs the macros themselves. -/

/-- The `:= g` form: the read element feeds the function
(`xs[1] = 20`, `+5 = 25`). -/
example :
    SSZ.hashTreeRoot Sha256 (sszUpdate s0 with xs[1]! := s0.xs[1]! + 5)
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 25 } : S) := by
  native_decide

/-- The `as x => { x with … }` form (`es[0] = { a := 1, b := 2 }`,
so `a + 10` gives `{ a := 11, b := 2 }`). -/
example :
    SSZ.hashTreeRoot Sha256
        (sszUpdate t0 with es[0]! := { t0.es[0]! with a := t0.es[0]!.a + 10 })
      = SSZ.hashTreeRoot Sha256
          ({ t0 with es := t0.es.set! 0 { a := 11, b := 2 } } : S2) := by
  native_decide

/-- A plain field path (`marker + 1 = 8`). -/
example :
    SSZ.hashTreeRoot Sha256 (sszUpdate s0 with marker := s0.marker + 1)
      = SSZ.hashTreeRoot Sha256 ({ s0 with marker := 8 } : S) := by
  native_decide

/-! ## The `MultiSetterIndex` case on a plain value

An `[i]!` write into the composite-element `Vector ExRoot 8` field of
`BatchExample` matches the hand-written `.set!` record update, in
value and root, over a sweep of bases and in-range indices. -/

/-- A deterministic 32-byte root. -/
private def mkRoot (k : Nat) : ExRoot :=
  Vector.ofFn fun (i : Fin 32) => ((k * 31 + i.val) % 256).toUInt8

/-- A `BatchExample` varying with `k`. -/
private def mkBatch (k : Nat) : BatchExample :=
  { rootsA := Vector.ofFn fun (i : Fin 8) => mkRoot (k * 8 + i.val)
    rootsB := Vector.ofFn fun (i : Fin 8) => mkRoot (k * 8 + i.val + 100) }

/-- One sweep case: value and root of the plain update equal the
hand-written record update. -/
private def batchCaseOk (k : Nat) : Bool :=
  let i := k % 8
  let v := mkBatch k
  let updated : BatchExample := sszUpdate v with rootsA[i]! := mkRoot (k + 50)
  let direct : BatchExample := { v with rootsA := v.rootsA.set! i (mkRoot (k + 50)) }
  updated == direct
    && SSZ.hashTreeRoot Sha256 updated == SSZ.hashTreeRoot Sha256 direct

private def batchSweep : Nat → Bool
  | 0 => true
  | k + 1 => if batchCaseOk (k + 1) then batchSweep k else false

example : batchSweep 30 = true := by native_decide

/-! ## A `@[sizzlean_progressive]` container

The plain arm emits view-side code only, so a progressive container
needs no special case (no gindex geometry exists to get wrong): the
update is the record update, and the root follows from the value. -/

@[sizzlean_progressive]
structure Prog where
  side  : UInt16
  color : UInt8
  deriving Inhabited, DecidableEq, SSZRepr

private def p0 : Prog := { side := 0x0102, color := 7 }

example : (sszUpdate p0 with color := 9) = { p0 with color := 9 } := rfl

example :
    SSZ.hashTreeRoot Sha256 (sszUpdate p0 with color := 9)
      = SSZ.hashTreeRoot Sha256 { p0 with color := 9 } := by
  native_decide

/-! ## A checked `[i]` segment on a plain base is a compile error

The plain arm has no `Except` result to reject into, and no spec
body uses a checked index on a plain value; the message names the
supported form. -/

/--
error: sszUpdate: a checked `[i]` index segment is not supported on a plain (non-boxed) base; use the infallible `[i]!` form, whose out-of-range write is a no-op
-/
#guard_msgs in
example : S := sszUpdate s0 with xs[1] := 99

/-! ## Plain reads: `sszGet` is the projection

On a plain base `elabSszGet` emits the projection rooted at the base
itself. `with_unfolding_none rfl` unifies the two sides with no
definition unfolded, so each gate holds only when `sszGet` elaborates
to the very term the hand-written projection gives. A wrapper, a
`let` or a stray `.view` would make it fail. -/

/-- Flat field. -/
example : sszGet s0 marker = s0.marker := by with_unfolding_none rfl

/-- Infallible element read. -/
example : sszGet s0 xs[1]! = s0.xs[1]! := by with_unfolding_none rfl

/-- Nested field. -/
example : sszGet n0 message.slot = n0.message.slot := by with_unfolding_none rfl

/-- Element, then field. -/
example : sszGet t0 es[1]!.b = t0.es[1]!.b := by with_unfolding_none rfl

/-- A progressive container reads the same way. -/
example : sszGet p0 color = p0.color := by with_unfolding_none rfl

/-- The values (`xs = #[10, 20, 30]`, `es[1] = { a := 3, b := 4 }`). -/
example : sszGet s0 xs[1]! = 20 := by native_decide
example : sszGet t0 es[1]!.b = 4 := by native_decide
example : sszGet n0 message.marker = 2 := by native_decide

/-- An out-of-range `[i]!` read yields the element's `default`, as
`get!` does (`xs` holds 3 of 8). -/
example : sszGet s0 xs[5]! = 0 := by native_decide

/-! ## A checked `[i]` read keeps its `Except` result

The read side has an `Except IndexError _` result to reject into on
any base, so the checked form stays available on a plain value: in
range it is `.ok` of the element, out of range it rejects with the
real index and bound. -/

example : Except IndexError UInt64 := sszGet s0 xs[1]

example : (sszGet s0 xs[1]).toOption = some 20 := by native_decide

example :
    (match sszGet s0 xs[5] with
     | .error (.indexError 5 3) => true
     | _ => false) = true := by
  native_decide

/-! ## Cache values still read through `.view`

The type-directed dispatch keeps the term of the earlier `sszGet`
macro on the three cache types. -/

private def u0 : UncachedSSZ Sha256 S := ⟨s0⟩

example : sszGet u0 marker = u0.view.marker := by with_unfolding_none rfl

private def b0 : SSZ.Box Sha256 S := SSZ.FastBox s0

example : sszGet b0 xs[1]! = b0.view.xs[1]! := by with_unfolding_none rfl

/-! ## The base type decides after postponing

In `List.map (fun s => sszGet s marker) [x]` the binder `s` has no
type when the body elaborates; the list argument fixes it later.
`elabSszGet` postpones until then and picks the arm from the type
it finally gets: the projection for `S`, `.view` for the box. With no
later argument the type stays unknown, and the elaborator asks for an
ascription. -/

example : List.map (fun s => sszGet s marker) [s0] = [7] := by native_decide

example : List.map (fun b => sszGet b marker) [b0] = [7] := by native_decide

/-- error: sszGet: the type of the base `s` is not known; add a type ascription -/
#guard_msgs in
example := fun s => sszGet s marker

/-! ## `sszModify` and `sszAppend?` on a plain value

Both macros expand to `sszGet` and `sszUpdate`, so with both plain
arms in place they run on a plain value with no change. The results
are plain values (the ascriptions fail to typecheck otherwise) and
match the hand-written record updates. -/

example : S := sszModify s0 xs[1]! := (fun w => w + 5)
example : S2 := sszModify t0 es[0]! as e => { e with a := e.a + 10 }
example : Option S := sszAppend? s0 xs 99

/-- The `:= g` form on an element (`xs[1] = 20`, `+5 = 25`). -/
example :
    (sszModify s0 xs[1]! := (fun w => w + 5)) = { s0 with xs := s0.xs.set! 1 25 } := by
  native_decide

/-- The `:= g` form on a field (`marker + 1 = 8`). -/
example : (sszModify s0 marker := (· + 1)) = { s0 with marker := 8 } := by
  native_decide

/-- The `as x => { x with … }` form (`es[0] = { a := 1, b := 2 }`,
so `a + 10` gives `{ a := 11, b := 2 }`). -/
example :
    (sszModify t0 es[0]! as e => { e with a := e.a + 10 })
      = { t0 with es := t0.es.set! 0 { a := 11, b := 2 } } := by
  native_decide

/-- An out-of-range `sszModify` is a no-op, as the `[i]!` write is. -/
example : (sszModify s0 xs[7]! := (fun w => w + 5)) = s0 := by native_decide

/-- `sszAppend?` with room: `some` of the longer list (3 of 8 → 4). -/
example :
    (sszAppend? s0 xs 99).map (fun s => s.xs.toArray) = some #[10, 20, 30, 99] := by
  native_decide

/-- A full list for the `none` case. -/
structure Full where
  ys : SSZList UInt64 2
  deriving DecidableEq, Inhabited, SSZRepr

private def f0 : Full := { ys := ⟨#[1, 2], by decide⟩ }

/-- `sszAppend?` on a full list: `none`, the spec's reject. -/
example : sszAppend? f0 ys 3 = none := by native_decide

end SizzLeanTests.PlainUpdate
