import EthCLLib

/-!
# `EthCLLib.Tests.CLIndex`: size-aware indices

`SPEC_ARITHMETIC.md` §4.6 with the index table of §3.7. The `ToIndex` class
and its `Nat` / `CLUint64` / `CLInt` instances, the pure raising read `getAt`
(`Except IndexError`), and the pure checked write `setAt` live in
`Spec/State.lean` beside `sszGetIdx`, which keeps its `Nat` index and its
behavior for the current fork bodies. The pins, in order:

- The position table for each index kind: in range, `-1`, `-size`, below
  `-size`, `size`, and the empty collection, where a positive out-of-range and
  a below-`-size` negative both map to `none`.
- Reads and writes at each index kind, on a plain array, an SSZ list, a
  vector, and a bit list.
- The error class: an index fault lifts to `outOfBounds` through the existing
  `ErrorConv`, never into the arithmetic fault, and a value-range fault lifts
  to `.arithmetic`. The two failures of a checked write stay distinct and
  classified apart.
- A negative-index success feeding arithmetic, the §4.6 read-then-bind shape.
-/

set_option autoImplicit false

namespace EthCLLib.Tests.CLIndex

open EthCLLib.Spec
open SizzLean.Cache

/-- Core ships no `DecidableEq` for a bare `Except`, so the `decide` pins
below carry their own. Same shape as `Checked`'s derived instance; local to
this module, so no importer sees it. -/
local instance {E α : Type} [DecidableEq E] [DecidableEq α] :
    DecidableEq (Except E α) :=
  fun a b =>
    match a, b with
    | .ok x, .ok y => decidable_of_iff (x = y)
        (⟨fun h => by rw [h], fun h => Except.ok.inj h⟩ :
          (x = y) ↔ (Except.ok x = Except.ok y))
    | .ok _, .error _ => isFalse (fun h => by cases h)
    | .error _, .ok _ => isFalse (fun h => by cases h)
    | .error x, .error y => decidable_of_iff (x = y)
        (⟨fun h => by rw [h], fun h => Except.error.inj h⟩ :
          (x = y) ↔ (Except.error x = Except.error y))

/-! ## The position table (`ToIndex.pos?`)

Into a collection of three elements, the §3.7 rows. -/

#guard ToIndex.pos? (1 : Nat) 3 == some 1
#guard ToIndex.pos? 3 3 == none
#guard ToIndex.pos? 0 0 == none

#guard ToIndex.pos? (1 : CLUint64) 3 == some 1
#guard ToIndex.pos? (3 : CLUint64) 3 == none

#guard ToIndex.pos? (1 : CLInt) 3 == some 1
#guard ToIndex.pos? (3 : CLInt) 3 == none
#guard ToIndex.pos? (-1 : CLInt) 3 == some 2
#guard ToIndex.pos? (-3 : CLInt) 3 == some 0
#guard ToIndex.pos? (-4 : CLInt) 3 == none
#guard ToIndex.pos? (-1 : CLInt) 0 == none

/-! ## Reads

A stand-in for the beacon state's validator balances. -/

def balances : Array CLUint64 := #[10, 20, 30]

-- A `Nat` index reads the element; `size` raises.
example : getAt balances (1 : Nat) = .ok 20 := rfl
example : (getAt balances (3 : Nat) : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl

-- A `CLUint64` index reads the element; the out-of-range one raises.
example : getAt balances (1 : CLUint64) = .ok 20 := rfl
example : (getAt balances (3 : CLUint64) : Except IndexError _)
  = .error (IndexError.indexError 0 3) := rfl

-- A negative `CLInt` index counts from the end: `-1` is the last element,
-- `-size` the first, below `-size` raises.
example : getAt balances (-1 : CLInt) = .ok 30 := rfl
example : getAt balances (-3 : CLInt) = .ok 10 := rfl
example : (getAt balances (-4 : CLInt) : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl

-- Every index raises on the empty collection.
example : (getAt (#[] : Array CLUint64) (0 : Nat) : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl
example : (getAt (#[] : Array CLUint64) (-1 : CLInt) : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl

-- The same reads on an SSZ list, a vector, and a bit list, each kind at the
-- §3.7 rows.
def sszBalances : SizzLean.Repr.SSZList CLUint64 10 := ⟨#[10, 20, 30], by decide⟩
def sszEmpty : SizzLean.Repr.SSZList CLUint64 10 := ⟨#[], by decide⟩

example : getAt sszBalances (-1 : CLInt) = .ok 30 := rfl
example : getAt sszBalances (-3 : CLInt) = .ok 10 := rfl
example : (getAt sszBalances (-4 : CLInt) : Except IndexError _)
  = .error (IndexError.indexError 0 3) := rfl
example : (getAt sszBalances (3 : Nat) : Except IndexError _)
  = .error (IndexError.indexError 0 3) := rfl
example : (getAt sszEmpty (0 : Nat) : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl
example : (getAt sszEmpty (-1 : CLInt) : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl

def vec3 : Vector CLUint64 3 := #v[10, 20, 30]
def vec0 : Vector CLUint64 0 := #v[]

example : getAt vec3 (1 : CLUint64) = .ok 20 := rfl
example : getAt vec3 (-1 : CLInt) = .ok 30 := rfl
example : getAt vec3 (-3 : CLInt) = .ok 10 := rfl
example : (getAt vec3 (-4 : CLInt) : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (getAt vec3 (3 : Nat) : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (getAt vec0 (0 : Nat) : Except IndexError _) = .error (IndexError.indexError 0 0) := rfl

def bits : SizzLean.Repr.Bitlist 8 := ⟨#[true, false, true], by decide⟩
def bits0 : SizzLean.Repr.Bitlist 8 := ⟨#[], by decide⟩

example : getAt bits (-1 : CLInt) = .ok true := rfl
example : getAt bits (-3 : CLInt) = .ok true := rfl
example : (getAt bits (-4 : CLInt) : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (getAt bits (3 : Nat) : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (getAt bits0 (0 : Nat) : Except IndexError _) = .error (IndexError.indexError 0 0) := rfl

/-! ## Writes

The pure checked write `setAt` takes the same class: an out-of-range index
raises `IndexError`, in range it returns the updated collection. -/

example : setAt balances (1 : Nat) 99 = .ok #[10, 99, 30] := rfl
example : (setAt balances (3 : Nat) 99 : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl

example : setAt balances (-1 : CLInt) 99 = .ok #[10, 20, 99] := rfl
example : setAt balances (-3 : CLInt) 99 = .ok #[99, 20, 30] := rfl
example : (setAt balances (-4 : CLInt) 99 : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl

example : (setAt (#[] : Array CLUint64) (0 : Nat) 99 : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl
example : (setAt (#[] : Array CLUint64) (-1 : CLInt) 99 : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl

example : setAt sszBalances (1 : Nat) 99 = .ok ⟨#[10, 99, 30], by decide⟩ := rfl
example : setAt sszBalances (-1 : CLInt) 99 = .ok ⟨#[10, 20, 99], by decide⟩ := rfl
example : setAt sszBalances (-3 : CLInt) 99 = .ok ⟨#[99, 20, 30], by decide⟩ := rfl
example : (setAt sszBalances (-4 : CLInt) 99 : Except IndexError _)
  = .error (IndexError.indexError 0 3) := rfl
example : (setAt sszBalances (3 : Nat) 99 : Except IndexError _)
  = .error (IndexError.indexError 0 3) := rfl
example : (setAt sszEmpty (0 : Nat) 99 : Except IndexError _)
  = .error (IndexError.indexError 0 0) := rfl

example : setAt vec3 (-1 : CLInt) 99 = .ok #v[10, 20, 99] := rfl
example : setAt vec3 (-3 : CLInt) 99 = .ok #v[99, 20, 30] := rfl
example : (setAt vec3 (3 : Nat) 99 : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (setAt vec3 (-4 : CLInt) 99 : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (setAt vec0 (0 : Nat) 99 : Except IndexError _) = .error (IndexError.indexError 0 0) := rfl

example : setAt bits (-1 : CLInt) false = .ok ⟨#[true, false, false], by decide⟩ := rfl
example : setAt bits (-3 : CLInt) false = .ok ⟨#[false, false, true], by decide⟩ := rfl
example : (setAt bits (3 : Nat) false : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (setAt bits (-4 : CLInt) false : Except IndexError _) = .error (IndexError.indexError 0 3) := rfl
example : (setAt bits0 (0 : Nat) false : Except IndexError _) = .error (IndexError.indexError 0 0) := rfl

/-! ## The two failure classes of a checked write

A store into a checked field converts the value first: the conversion's range
failure is the arithmetic fault, the write's own failure is the index fault
(`§4.5`, the store row). They lift into different constructors, so the
runner's caught sets keep them apart. -/

/-- The checked-write shape of §4.3: the value's range test first, then the
indexed write. -/
def checkedWrite (xs : Array CLUint64) (i : Nat) (raw : Nat) :
    Except StateTransitionError (Array CLUint64) := do
  let v ← CLUint64.ofNat? raw
  liftErr (setAt xs i v)

-- In range: the write lands.
example : checkedWrite balances 1 99 = .ok #[10, 99, 30] := by decide

-- A value past the maximum raises the arithmetic fault, before any write.
example : checkedWrite balances 1 18446744073709551616
  = .error (.arithmetic "Uint64()") := by decide

-- An out-of-range index raises the index fault, with a value that converts.
example : checkedWrite balances 3 99 = .error (.outOfBounds 0 3) := by decide

-- The classes differ, typed: the index fault carries no arithmetic cause, the
-- range fault does, and the admit tables take them apart.
example : StateTransitionError.arithCause (.outOfBounds 3 3) = none := rfl
example : StateTransitionError.arithCause (.arithmetic "Uint64()")
  = some ArithCause.range := rfl
#guard RunnerCaughtSet.assertionAndIndex.admits (.outOfBounds 3 3)
#guard !RunnerCaughtSet.assertionAndIndex.admits (.arithmetic "Uint64()")
#guard RunnerCaughtSet.valueError.admits (.arithmetic "Uint64()")
#guard !RunnerCaughtSet.valueError.admits (.outOfBounds 3 3)

-- A rejected index has no position, so the reject's diagnostic index field is
-- the `0` placeholder; the payload is diagnostic only.
example : checkedWrite balances (3 : Nat) 99 != .error (.arithmetic "Uint64()") := by decide

/-! ## A read feeds arithmetic

`§4.6`: the read lifts into the machine's error channel as `outOfBounds`, the
operators bind through the arithmetic lift, and a negative-index success
reaches the operation. -/

def increased (delta : CLUint64) : Except StateTransitionError CLUint64 := do
  let prev ← liftErr (getAt balances (-1 : CLInt))
  prev + delta

example : increased 5 = .ok 35 := by decide

-- The same body at an out-of-range index stays an index fault, never an
-- arithmetic one.
def increasedAt (i : Nat) (delta : CLUint64) : Except StateTransitionError CLUint64 := do
  let prev ← liftErr (getAt balances i)
  prev + delta

example : increasedAt 7 5 = .error (.outOfBounds 0 3) := by decide
#guard StateTransitionError.arithCause (.outOfBounds 7 3) == none

end EthCLLib.Tests.CLIndex
