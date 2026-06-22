import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Update
import SizzLeanTests.ExampleContainers

/-! ## Vector-index `sszUpdate t with v[i] := x` on `BatchExample`.

A property test on the small `BatchExample` (8 entries per
vector, depth 3) rather than a full consensus container like
`HistoricalBatch` (64 entries, depth 6). Real-container coverage
of this path comes from the `EthCLSpecs` `ssz_static` conformance
sweep. The smaller depth keeps the SSZ-library test fast while
still exercising the runtime-`i` gindex path: the macro composes
the outer container's field-0 prefix `[false]` with `gindexBits
(base + i)` for the inner vector position.

If the runtime gindex computation drops the outer-field prefix,
the per-element gindex base is wrong, or the view-side
`Vector.set!` substitution mismatches the tree-side write, this
test fails on the first iteration.
-/

set_option autoImplicit false

namespace SizzLeanTests.MultiSetterIndex

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanTests.ExampleContainers

/-! ### PRNG (LCG). -/

private def lcgNext (s : Nat) : Nat :=
  (s * 1664525 + 1013904223) % 4294967296

private def randByte (s : Nat) : UInt8 × Nat :=
  let s' := lcgNext s
  (Nat.toUInt8 (s' % 256), s')

private def randBytes32 (s : Nat) : ByteArray × Nat :=
  let rec go : Nat → Nat → ByteArray → ByteArray × Nat
    | 0,     st, acc => (acc, st)
    | k + 1, st, acc =>
        let (b, st') := randByte st
        go k st' (acc.push b)
  go 32 s ByteArray.empty

private def randRoot (s : Nat) : ExRoot × Nat :=
  let (ba, s') := randBytes32 s
  (Vector.ofFn (fun (i : Fin 32) => ba.get! i.val), s')

/-- Build a `Vector ExRoot 8` by streaming the PRNG. -/
private def randVector8Roots (s : Nat) : Vector ExRoot 8 × Nat :=
  let rec go : Nat → Nat → Array ExRoot → Array ExRoot × Nat
    | 0,     st, acc => (acc, st)
    | k + 1, st, acc =>
        let (r, st') := randRoot st
        go k st' (acc.push r)
  let (arr, s') := go 8 s (Array.mkEmpty 8)
  let v : Vector ExRoot 8 := Vector.ofFn (fun (i : Fin 8) => arr[i.val]!)
  (v, s')

private def randIndexLt8 (s : Nat) : Nat × Nat :=
  let s' := lcgNext s
  (s' % 8, s')

/-! ### One property-test case. -/

private def oneBatchCase (s : Nat) : Bool × Nat :=
  let (rA, s1) := randVector8Roots s
  let (rB, s2) := randVector8Roots s1
  let (i,  s3) := randIndexLt8 s2
  let (newR, s4) := randRoot s3
  let v : BatchExample := { rootsA := rA, rootsB := rB }
  let t : TreeBacked Sha256 BatchExample := TreeBacked.ofValue Sha256 v
  let updated : BatchExample :=
    { v with rootsA := rA.set! i newR }
  -- `rootsA[i]` is an index form ⇒ `Except`; `i < 8` always holds here,
  -- so it is `.ok`. (An out-of-range `i` would `.error`/reject.)
  match (sszUpdate t with rootsA[i] := newR) with
  | .ok t' =>
      let rootOk := t'.hashTreeRootCached.1 = SSZ.hashTreeRoot Sha256 updated
      let viewOk := if h : i < 8 then t'.view.rootsA[i] = newR else false
      (rootOk && viewOk, s4)
  | .error _ => (false, s4)

private def runBatchCases : Nat → Nat → Bool
  | 0,     _ => true
  | k + 1, s =>
      let (ok, s') := oneBatchCase s
      if ok then runBatchCases k s' else false

example : runBatchCases 30 0xBEEF = true := by native_decide

end SizzLeanTests.MultiSetterIndex
