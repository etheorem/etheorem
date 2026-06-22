import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Cache.TreeBacked
import SizzLeanTests.ExampleContainers

/-!
# `SizzLeanTests.TreeBackedCoherence`: coherence on example containers

The cache-layer coherence theorem

    ∀ (v : T) (t := TreeBacked.ofValue Sha256 v),
      t.hashTreeRootCached = SSZ.hashTreeRoot Sha256 t.view

is what makes the cached path safe to substitute for the spec one
at runtime. It is empirically asserted in Lean via `native_decide`
cases rather than proved.

This file does it on the example containers from
`ExampleContainers.lean`. Real consensus-spec containers exercise
the same coherence property through the `EthCLSpecs` `ssz_static`
conformance sweep, so the two cover disjoint type surfaces.

Cases per container:
* one zero-init value
* one PRNG-derived value with non-trivial bytes (to catch
  zero-leaf shortcuts)
-/

set_option autoImplicit false

namespace SizzLeanTests.TreeBackedCoherence

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLeanTests.ExampleContainers

/-! ## Zero values for example containers. -/

private def zeroRoot    : ExRoot    := Vector.replicate 32 0
private def zeroVersion : ExVersion := Vector.replicate 4 0
private def zeroSig     : Vector UInt8 96 := Vector.replicate 96 0

private def zeroFlat : FlatExample :=
  { versionA := zeroVersion, versionB := zeroVersion, marker := 0 }

private def zeroInner : InnerExample :=
  { slot   := 0
    marker := 0
    rootA  := zeroRoot
    rootB  := zeroRoot
    rootC  := zeroRoot }

private def zeroNested : NestedExample :=
  { message := zeroInner, signature := zeroSig }

private def zeroBatch : BatchExample :=
  { rootsA := Vector.replicate 8 zeroRoot
    rootsB := Vector.replicate 8 zeroRoot }

/-! ## Realistic values: hand-picked non-zero bytes. -/

private def realisticVersion : ExVersion :=
  Vector.ofFn (fun (i : Fin 4) => Nat.toUInt8 (0x10 + i.val))

private def realisticRoot : ExRoot :=
  Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 i.val)

private def realisticSig : Vector UInt8 96 :=
  Vector.ofFn (fun (i : Fin 96) => Nat.toUInt8 (i.val * 3 % 256))

private def realisticFlat : FlatExample :=
  { versionA := realisticVersion
    versionB := Vector.ofFn (fun (i : Fin 4) => Nat.toUInt8 (0x20 + i.val))
    marker   := 0xDEADBEEF }

private def realisticInner : InnerExample :=
  { slot   := 1234
    marker := 5678
    rootA  := realisticRoot
    rootB  := Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 (i.val + 32))
    rootC  := Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 (i.val + 64)) }

private def realisticNested : NestedExample :=
  { message := realisticInner, signature := realisticSig }

private def realisticBatch : BatchExample :=
  let mkRoot (k : Nat) : ExRoot :=
    Vector.ofFn (fun (i : Fin 32) => Nat.toUInt8 ((i.val + k) % 256))
  { rootsA := Vector.ofFn (fun (i : Fin 8) => mkRoot (i.val * 7))
    rootsB := Vector.ofFn (fun (i : Fin 8) => mkRoot (i.val * 13 + 100)) }

/-! ## Coherence gates. -/

example :
    (TreeBacked.ofValue Sha256 zeroFlat).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 zeroFlat := by native_decide

example :
    (TreeBacked.ofValue Sha256 realisticFlat).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 realisticFlat := by native_decide

example :
    (TreeBacked.ofValue Sha256 zeroNested).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 zeroNested := by native_decide

example :
    (TreeBacked.ofValue Sha256 realisticNested).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 realisticNested := by native_decide

example :
    (TreeBacked.ofValue Sha256 zeroBatch).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 zeroBatch := by native_decide

example :
    (TreeBacked.ofValue Sha256 realisticBatch).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 realisticBatch := by native_decide

end SizzLeanTests.TreeBackedCoherence
