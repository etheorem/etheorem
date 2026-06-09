import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.TreeBackedSetField`, `sszUpdate` on example containers

The cached-update coherence statement:

    ∀ (v : T) (newField : F),
      (sszUpdate (TreeBacked.ofValue Sha256 v) with field := newField).hashTreeRootCached
        = SSZ.hashTreeRoot Sha256 { v with field := newField }

is enforced by PRNG batches on the example containers from
`ExampleContainers.lean`. Each case randomises both an initial
value and a fresh field value, applies the macro, and checks the
cached root against the spec root on the struct-updated value.

* `runFlatCases` (50 cases): flat 3-field `sszUpdate` on
  `FlatExample`. Multi-clause emission with no nesting.
* `runNestedCases` (20 cases): nested + sibling `sszUpdate` on
  `NestedExample`. Path composition across one nesting level plus
  a sibling flat clause.

The companion file `LeanEthCS.TreeBackedSetField`
runs analogous tests against real consensus-spec containers
(`Fork`, `SignedBeaconBlockHeader`). The two share the same
property-test structure on disjoint type surfaces, so a regression
in either the macro or the underlying `Node.setManyAt` walker is
caught at both layers.

Also included: a small `rfl` block confirming the uncached
emission path (on `UncachedSSZ`) reduces to a plain
`{ view := { … with f := v } }` struct rewrite. If the macro's
uncached branch ever drags in Merkle infrastructure those `rfl`s
stop closing.
-/

set_option autoImplicit false

namespace SizzLeanTests.TreeBackedSetField

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanTests.ExampleContainers

/-! ### Deterministic PRNG (LCG, "Numerical Recipes" parameters). -/

private def lcgNext (s : Nat) : Nat :=
  (s * 1664525 + 1013904223) % 4294967296

private def randByte (s : Nat) : UInt8 × Nat :=
  let s' := lcgNext s
  (Nat.toUInt8 (s' % 256), s')

private def randBytes (n : Nat) (s : Nat) : ByteArray × Nat :=
  let rec go : Nat → Nat → ByteArray → ByteArray × Nat
    | 0,     st, acc => (acc, st)
    | k + 1, st, acc =>
        let (b, st') := randByte st
        go k st' (acc.push b)
  go n s ByteArray.empty

private def randVersion (s : Nat) : ExVersion × Nat :=
  let (ba, s') := randBytes 4 s
  (Vector.ofFn (fun (i : Fin 4) => ba.get! i.val), s')

private def randRoot (s : Nat) : ExRoot × Nat :=
  let (ba, s') := randBytes 32 s
  (Vector.ofFn (fun (i : Fin 32) => ba.get! i.val), s')

private def randSig (s : Nat) : Vector UInt8 96 × Nat :=
  let (ba, s') := randBytes 96 s
  (Vector.ofFn (fun (i : Fin 96) => ba.get! i.val), s')

private def randUInt64 (s : Nat) : UInt64 × Nat :=
  let s1 := lcgNext s
  let s2 := lcgNext s1
  let lo := s1 % 4294967296
  let hi := s2 % 4294967296
  (Nat.toUInt64 (lo + hi * 4294967296), s2)

/-! ### Flat multi-field, `sszUpdate t with f₁ := v₁, f₂ := v₂, f₃ := v₃` -/

private def oneFlatCase (s : Nat) : Bool × Nat :=
  let (vA0, s1) := randVersion s
  let (vB0, s2) := randVersion s1
  let (m0,  s3) := randUInt64 s2
  let (vA',  s4) := randVersion s3
  let (vB',  s5) := randVersion s4
  let (m',   s6) := randUInt64 s5
  let v : FlatExample := { versionA := vA0, versionB := vB0, marker := m0 }
  let t : TreeBacked Sha256 FlatExample := TreeBacked.ofValue Sha256 v
  let t' := sszUpdate t with
              versionA := vA',
              versionB := vB',
              marker   := m'
  let updated : FlatExample :=
    { v with versionA := vA', versionB := vB', marker := m' }
  let rootOk := t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 updated
  let viewOk :=
        t'.view.versionA = vA'
     && t'.view.versionB = vB'
     && t'.view.marker   = m'
  (rootOk && viewOk, s6)

private def runFlatCases : Nat → Nat → Bool
  | 0,     _ => true
  | k + 1, s =>
      let (ok, s') := oneFlatCase s
      if ok then runFlatCases k s' else false

example : runFlatCases 50 0xFEEDFACE = true := by native_decide

/-! ### Nested + sibling, `sszUpdate t with f.g := v, f.h := w, k := x` -/

private def oneNestedCase (s : Nat) : Bool × Nat :=
  let (slot0,  s1)  := randUInt64 s
  let (m0,     s2)  := randUInt64 s1
  let (rA0,    s3)  := randRoot s2
  let (rB0,    s4)  := randRoot s3
  let (rC0,    s5)  := randRoot s4
  let (sig0,   s6)  := randSig s5
  let (newSlot, s7) := randUInt64 s6
  let (newM,    s8) := randUInt64 s7
  let (newSig,  s9) := randSig s8
  let i0 : InnerExample :=
    { slot := slot0, marker := m0, rootA := rA0, rootB := rB0, rootC := rC0 }
  let v : NestedExample := { message := i0, signature := sig0 }
  let t : TreeBacked Sha256 NestedExample := TreeBacked.ofValue Sha256 v
  let t' := sszUpdate t with
              message.slot   := newSlot,
              message.marker := newM,
              signature      := newSig
  let updated : NestedExample :=
    { v with
        message := { i0 with slot := newSlot, marker := newM }
        signature := newSig }
  let rootOk := t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 updated
  let viewOk :=
        t'.view.message.slot   = newSlot
     && t'.view.message.marker = newM
     && t'.view.signature      = newSig
  (rootOk && viewOk, s9)

private def runNestedCases : Nat → Nat → Bool
  | 0,     _ => true
  | k + 1, s =>
      let (ok, s') := oneNestedCase s
      if ok then runNestedCases k s' else false

example : runNestedCases 20 0xCAB1E = true := by native_decide

/-! ### Uncached `sszUpdate` reduces under `rfl`

`Cache/Update.lean`'s uncached branch emits a plain
`{ view := { t.view with f := v, … } } : UncachedSSZ H T`. The two
`rfl` examples below pin that proof shape, if a future macro
change drags Merkle infrastructure into the uncached path the
examples stop closing and CI catches it. -/

example (u : UncachedSSZ Sha256 FlatExample) (m : UInt64) :
    (sszUpdate u with marker := m).view
      = { u.view with marker := m } := by
  rfl

example (u : UncachedSSZ Sha256 FlatExample) (m : UInt64) :
    (sszUpdate u with marker := m).hashTreeRoot
      = SSZ.hashTreeRoot Sha256 ({ u.view with marker := m } : FlatExample) := by
  rfl

/-! ### `sszUpdate` on `SSZ.Box` dispatches to both flavours

`Cache/Update.lean`'s box branch emits a two-arm `match` that
wraps each arm in the appropriate `SSZ.Box.cached` /
`SSZ.Box.uncached` constructor. These examples pin that the
constructor a value enters with is the constructor the result
comes out with, i.e. `sszUpdate` on `Box` preserves the flavour. -/

private def f0 : FlatExample :=
  { versionA := Vector.replicate 4 0x11
    versionB := Vector.replicate 4 0x22
    marker   := 5 }

example :
    let b := SSZ.FastBox f0
    let b' := sszUpdate b with marker := 99
    b'.view = { f0 with marker := 99 } := by
  native_decide

example :
    let b := SSZ.PureBox f0
    let b' := sszUpdate b with marker := 99
    b'.view = { f0 with marker := 99 } := by
  rfl

example :
    let b := SSZ.FastBox f0
    let b' := sszUpdate b with marker := 99
    b'.hashTreeRoot.1 = SSZ.hashTreeRoot Sha256 ({ f0 with marker := 99 } : FlatExample) := by
  native_decide

end SizzLeanTests.TreeBackedSetField
