import Lean
import Plausible.Sampleable
import Plausible.Arbitrary
import SizzLean
import EthCLLib.TheoremVectors.Types

/-!
# `EthCLLib.TheoremVectors.Sampleable`: the generators the search draws with

The `SampleableExt` / `Shrinkable` supply of §9.5. Two layers:

- hand-written `SampleableExt` instances for the scalar family (`UInt8`
  through `UInt64`, `Bool`, `Fin n`, `ByteArray`), so a scalar drawn on
  its own has one behavior everywhere;
- one generic instance for every type with `SSZRepr`, driven by SizzLean's
  type description: `proxy` is the shape's `interp` image, `interp` is
  `fromRepr`, and the draw and the shrink walk the description
  (`genShape`, `shrinkShape`). This answers the plan's decision point B:
  the instance falls out of the description, so no hand-written
  per-container generators and no extension to SizzLean are needed. A
  mainnet state's fixed-length vectors stay at their length, the way
  §9.5 notes shrinking cannot cut them; the lists take their length from
  `Gen`'s size parameter capped by the SSZ limit.

The draws run at elaboration time inside the probe's compiled `sample`
face (§11.1), so the `Gen` stack runs over its pure reader and state
layers, seeded by the run's `theorem_vectors.seed` (§14.4). The same seed
and size draw the same bytes, which is what makes a build reproducible.

## Lean idioms annotated

- `instance (priority := 2000)` / `(priority := 1200)`: the instance
  priorities that
  keep synthesis deterministic. The scalar instances outrank the generic
  `SSZRepr` one, which also applies to the scalar types. Plausible's own
  `selfContained` sits at priority 1000 with a `default_instance` tag;
  the generic instance's 1200 keeps the shape walk ahead of it, which
  matters because a `selfContained` match needs `Repr`, `Shrinkable`,
  and `Arbitrary` together and would bypass the description's bounded
  lists if one applied.
- The generic instance's arms reference Plausible's instances by name
  instead of synthesizing over `interp`-typed goals: `interp s` reduces
  for a concrete scalar shape, so an instance keyed on it would overlap
  the type's own instance and synthesis would report the ambiguity.
- The wide `uintN` widths reduce on their literals (`128`, `256`) and
  draw, shrink, and print like any `BitVec`; Fulu's state carries one
  (`baseFeePerGas : BitVec 256`). Any other width is the residual arm:
  `interp (.uintN n)` is stuck for a symbolic width, so no
  `BitVec`-typed value has the interp type there, and the draw fails
  honestly while the shrink proposes nothing.
-/

set_option autoImplicit false

open Lean
open Plausible
open SizzLean (SSZRepr)
open SizzLean.Spec (SSZType)

namespace EthCLLib.TheoremVectors

/-! ## The seeded draw (§9.4) -/

/-- One seeded draw at `size`, run over Plausible's pure `Gen` stack.
`none` when the generator failed. Pure: the same seed and size draw the
same value, which is what makes a build reproducible (§14.4's `seed`).
The seed is hashed before `mkStdGen`, because the generator state over
small seeds is near-linear in the seed, and the draws' seeds are small
consecutive integers (`seed + draw`, plus a per-position offset), whose
raw form repeats values across draws. -/
def runDrawPure {α : Type} (seed size : Nat) (g : Plausible.Gen α) : Option α :=
  let gen := mkStdGen
    (mixHash (UInt64.ofNat seed) 0x9E3779B97F4A7C15).toNat
  let st := (StateT.run g (ULift.up gen)).run (ULift.up size)
  match st with
  | .ok (a, _) => some a
  | .error _ => none

/-! ## The scalar instances (§9.5) -/

/-- `UInt64` draws small most of the time and boundary-scale otherwise.
QuickCheck's small draws stay inside the size parameter, and a protocol
scalar's interesting values sit on both sides of constants such as
`minDepositAmountG`; the wide arm reaches them. -/
instance (priority := 2000) UInt64.sampleableExt : Plausible.SampleableExt UInt64 where
  proxy := UInt64
  interp := id
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := ⟨do
    if ← Gen.chooseAny Bool then
      let n ← Gen.choose Nat 0 (2 ^ 64 - 1) (by omega)
      return UInt64.ofNat n.val
    else
      Plausible.Arbitrary.arbitrary⟩

/-- The other fixed-width integers take Plausible's draw and shrink,
declared here so the generator's scalar face is this module's. -/
instance (priority := 2000) UInt8.sampleableExt : Plausible.SampleableExt UInt8 where
  proxy := UInt8
  interp := id
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := inferInstance

/-- `UInt16` takes Plausible's draw and shrink, declared here so the
generator's scalar face is this module's. -/
instance (priority := 2000) UInt16.sampleableExt : Plausible.SampleableExt UInt16 where
  proxy := UInt16
  interp := id
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := inferInstance

/-- `UInt32` takes Plausible's draw and shrink, declared here so the
generator's scalar face is this module's. -/
instance (priority := 2000) UInt32.sampleableExt : Plausible.SampleableExt UInt32 where
  proxy := UInt32
  interp := id
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := inferInstance

/-- `Bool` takes Plausible's draw; the shrink proposes nothing, the way
`Bool.shrinkable` does. -/
instance (priority := 2000) Bool.sampleableExt : Plausible.SampleableExt Bool where
  proxy := Bool
  interp := id
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := inferInstance

/-- `Fin n` draws and shrinks through Plausible's instances, which take
`Fin (n+1)`; `Fin 0` has no draw, the same gap its codec's `default`
answers `none` for (§9.1). -/
instance Fin.sampleableExt {n : Nat} : Plausible.SampleableExt (Fin (n + 1)) where
  proxy := Fin (n + 1)
  interp := id
  proxyRepr := inferInstance
  shrink := inferInstance
  sample := inferInstance

/-- A byte string draws `size` random bytes and shrinks by truncation.
The generator's byte-string inputs come from fixed-width byte vectors,
whose draws go through the shape layer; this instance is the type's own
face for the probe's scalar/container test. -/
instance ByteArray.sampleableExt : Plausible.SampleableExt ByteArray where
  proxy := ByteArray
  interp := id
  proxyRepr := ⟨fun b _ => Std.Format.text (hexOf b)⟩
  shrink := ⟨fun b =>
    (Plausible.Nat.shrink b.size).map fun n =>
      ByteArray.mk (b.data.take n)⟩
  sample := ⟨do
    let n ← Gen.getSize
    let mut b := ByteArray.emptyWithCapacity n
    for _ in [0:n] do
      b := b.push (UInt8.ofNat (← Gen.chooseNat))
    return b⟩

/-! ## The shape layer (§9.5) -/

/-- `n` sequential draws, with the drawn count as the array's size. -/
private def drawN {α : Type} (elem : Plausible.Gen α) :
    (n : Nat) → Plausible.Gen { xs : Array α // xs.size = n }
  | 0 => pure ⟨#[], rfl⟩
  | n + 1 => do
    let x ← elem
    let ⟨xs, h⟩ ← drawN elem n
    return ⟨xs.push x, by simp [h, Array.size_push]⟩

/-- The drawn array bounded by `cap` (§9.5): the length sits at the `Gen`
size parameter, capped by the SSZ limit. The limit itself is reachable, so
a hypothesis at a full container (`xs.size = cap`) has a satisfying draw. -/
private def drawBounded {α : Type} (elem : Plausible.Gen α) (cap : Nat) :
    Plausible.Gen { xs : Array α // xs.size ≤ cap } := do
  if hcap : cap = 0 then
    return ⟨#[], hcap ▸ Nat.zero_le _⟩
  else
    let size ← Gen.getSize
    let hi := min (cap + 1) (size + 1)
    have h0 : 0 < hi := by
      have : 0 < cap := by omega
      unfold hi
      omega
    let nSub ← Gen.chooseNatLt 0 hi h0
    let n := nSub.val
    have hlt : n < hi := nSub.property.2
    have hle : n ≤ cap := by
      unfold hi at hlt
      omega
    let ⟨xs, hs⟩ ← drawN elem n
    have hsz : xs.size ≤ cap := by
      rw [hs]
      exact hle
    pure ⟨xs, hsz⟩

/-- Draw a fixed-length vector: every element drawn, the length stays. -/
private def drawVector {α : Type} (elem : Plausible.Gen α) :
    (n : Nat) → Plausible.Gen (Vector α n)
  | 0 => pure ⟨#[], rfl⟩
  | n + 1 => do
    let x ← elem
    let v ← drawVector elem n
    return v.push x

mutual
/-- The draw of one SSZ shape (§9.5): each field by its own instance,
each list bounded by its SSZ limit and by `Gen`'s size parameter, each
fixed-length vector at its length. The scalar arms route through the
instances above, so `UInt64`'s wide/small mix reaches container fields. -/
def genShape : (s : SSZType) → Plausible.Gen s.interp
  | .uintN 8 => Plausible.SampleableExt.interpSample UInt8
  | .uintN 16 => Plausible.SampleableExt.interpSample UInt16
  | .uintN 32 => Plausible.SampleableExt.interpSample UInt32
  | .uintN 64 => Plausible.SampleableExt.interpSample UInt64
  -- the wide widths reduce on their literals, and Fulu's state carries
  -- one (`baseFeePerGas : BitVec 256`), so they draw like any BitVec
  | .uintN 128 =>
    (Plausible.BitVec.Arbitrary.arbitrary (α := BitVec 128) :
      Plausible.Gen (BitVec 128))
  | .uintN 256 =>
    (Plausible.BitVec.Arbitrary.arbitrary (α := BitVec 256) :
      Plausible.Gen (BitVec 256))
  -- `interp (.uintN n)` is stuck for a symbolic width, so any other
  -- width has no value to produce (see the module docstring)
  | .uintN _ => throw Plausible.Gen.genericFailure
  | .bool => Plausible.SampleableExt.interpSample Bool
  | .vector t n => drawVector (genShape t) n
  | .list t cap => drawBounded (genShape t) cap
  | .bitvector n =>
    (Plausible.BitVec.Arbitrary.arbitrary (α := BitVec n) : Plausible.Gen (BitVec n))
  | .bitlist cap => drawBounded (Plausible.SampleableExt.interpSample Bool) cap
  | .container fs => drawFields fs

/-- Draw a container's field tuple, field by field. -/
private def drawFields : (fs : List SSZType) → Plausible.Gen (SSZType.interpFields fs)
  | [] => pure PUnit.unit
  | t :: ts => do
    let x ← genShape t
    let rest ← drawFields ts
    return (x, rest)

end

/-- One shrink step over an array (§9.6): the half prefix, the last
element dropped, then a smaller first element. The steps propose a lean
candidate list, because each candidate of a container input is
re-serialized by the probe's `shrink` face, and a drawn state's forty
fields would otherwise flood the loop with candidates. At two elements
the half prefix and the dropped last element are the same array; at one
element the cut to empty is the only length step. -/
private def shrinkArray {α : Type} (elemShrink : α → List α) (xs : Array α) :
    List (Array α) :=
  let half := xs.size / 2
  let shorter :=
    if half < xs.size then
      if 0 < half then [xs.take half] else []
    else []
  let dropped :=
    if 0 < xs.size && (half == 0 || xs.size - 1 != half) then
      [xs.take (xs.size - 1)]
    else []
  let element :=
    if h : 0 < xs.size then
      ((elemShrink xs[0]).head?.map fun c => xs.set (Fin.mk 0 h) c).toList
    else []
  shorter ++ dropped ++ element

/-- One shrink step over a vector (§9.6): a smaller first element. The
length stays, the way §9.5 says shrinking cannot cut a fixed length, and
the walk proposes one candidate per step, for the same allocation reason
as `shrinkArray`. -/
private def shrinkVector {α : Type} (elemShrink : α → List α) :
    (n : Nat) → Vector α n → List (Vector α n)
  | 0, _ => []
  | n + 1, v =>
    if h : 0 < n + 1 then
      (elemShrink v[0]).head?.toList.map fun c =>
        Vector.mk (v.toArray.set (Fin.mk 0 h) c)
          (by rw [Array.size_set, Vector.size_toArray])
    else []

mutual
/-- One shrink step over one SSZ shape's value (§9.6). The order: a
container's variable fields' length cuts first, then the fixed fields'
element cuts; within one field, the length steps come before the
element steps. -/
def shrinkShape : (s : SSZType) → s.interp → List s.interp
  | .uintN 8, x => Plausible.UInt8.shrinkable.shrink x
  | .uintN 16, x => Plausible.UInt16.shrinkable.shrink x
  | .uintN 32, x => Plausible.UInt32.shrinkable.shrink x
  | .uintN 64, x => Plausible.UInt64.shrinkable.shrink x
  -- the wide widths reduce on their literals; they shrink like any
  -- BitVec, the way their draws draw
  | .uintN 128, x => Plausible.BitVec.shrinkable.shrink x
  | .uintN 256, x => Plausible.BitVec.shrinkable.shrink x
  -- any other width shrinks to nothing, the way its draw fails
  | .uintN _, _ => []
  | .bool, _ => []
  | .vector t n, v => shrinkVector (shrinkShape t) n v
  | .list t cap, xs =>
    (shrinkArray (shrinkShape t) xs.val).filterMap fun a =>
      if h : a.size ≤ cap then some ⟨a, h⟩ else none
  | .bitvector _, x => Plausible.BitVec.shrinkable.shrink x
  | .bitlist cap, xs =>
    (shrinkArray (fun _ => []) xs.val).filterMap fun a =>
      if h : a.size ≤ cap then some ⟨a, h⟩ else none
  | .container fs, p => shrinkFields fs p

/-- Is the shape variable-length? The container's variable fields'
length cuts come before the fixed fields' element cuts (§9.6). -/
def isVarShape : SSZType → Bool
  | .list .. => true
  | .bitlist .. => true
  | _ => false

/-- The variable fields' length cuts, first. -/
private def shrinkVarCuts : (fs : List SSZType) → SSZType.interpFields fs →
    List (SSZType.interpFields fs)
  | [], _ => []
  | t :: ts, (x, rest) =>
    let here : List (SSZType.interpFields (t :: ts)) :=
      if isVarShape t then
        (shrinkShape t x).map fun x' => (x', rest)
      else []
    here ++ ((shrinkVarCuts ts rest).map fun r' => (x, r'))

/-- The fields' element cuts, after the length cuts: a smaller field in
place, earlier fields first. -/
private def shrinkBase : (fs : List SSZType) → SSZType.interpFields fs →
    List (SSZType.interpFields fs)
  | [], _ => []
  | t :: ts, (x, rest) =>
    ((shrinkShape t x).map fun x' => (x', rest)) ++
      ((shrinkBase ts rest).map fun r' => (x, r'))

/-- One shrink step over a container: the variable fields' length cuts,
then the fields' element cuts (§9.6). -/
private def shrinkFields : (fs : List SSZType) → SSZType.interpFields fs →
    List (SSZType.interpFields fs)
  | fs, p => shrinkVarCuts fs p ++ shrinkBase fs p

end

mutual
/-- The proxy's print (§9.5's `proxyRepr`), structural over the shape.
The residual wide `uintN` arm prints a placeholder, the way its draw
fails. -/
def shapeFmt : (s : SSZType) → s.interp → Nat → Std.Format
  | .uintN 8, x, _ => Std.Format.text (toString x)
  | .uintN 16, x, _ => Std.Format.text (toString x)
  | .uintN 32, x, _ => Std.Format.text (toString x)
  | .uintN 64, x, _ => Std.Format.text (toString x)
  | .uintN 128, x, _ => Std.Format.text (toString x)
  | .uintN 256, x, _ => Std.Format.text (toString x)
  | .uintN _, _, _ => Std.Format.text "uintN"
  | .bool, x, _ => Std.Format.text (toString x)
  | .vector t _, v, _ =>
    Std.Format.bracket "["
      (Std.Format.joinSep (v.toList.map fun x => shapeFmt t x 0)
        (Std.Format.text ", ")) "]"
  | .list t _, xs, _ =>
    Std.Format.bracket "["
      (Std.Format.joinSep (xs.val.toList.map fun x => shapeFmt t x 0)
        (Std.Format.text ", ")) "]"
  | .bitvector _, x, _ => Std.Format.text (toString x)
  | .bitlist _, xs, _ =>
    Std.Format.bracket "["
      (Std.Format.joinSep (xs.val.toList.map fun b => Std.Format.text (toString b))
        (Std.Format.text ", ")) "]"
  | .container (t :: ts), (x, rest), _ =>
    Std.Format.bracket "(" (Std.Format.joinSep
      [shapeFmt t x 0, fieldsFmt ts rest 0] (Std.Format.text ", ")) ")"
  | .container [], _, _ => Std.Format.text "()"

/-- The field tuple's print, one bracketed group per nesting level. -/
private def fieldsFmt : (fs : List SSZType) → SSZType.interpFields fs → Nat → Std.Format
  | [], _, _ => Std.Format.text "()"
  | t :: ts, (x, rest), _ => Std.Format.bracket "(" (Std.Format.joinSep
      [shapeFmt t x 0, fieldsFmt ts rest 0] (Std.Format.text ", ")) ")"

end

/-- The `Repr` the generic proxy carries. -/
@[implicit_reducible]
def reprShape (s : SSZType) : Repr s.interp := ⟨shapeFmt s⟩

/-- The generic instance of §9.5: every type with `SSZRepr` draws and
shrinks through its shape's description. The proxy is the shape's
`interp` image and `interp` is `fromRepr`, so what the draw produces is
the same value the probe's codecs serialize and decode (§9.1). The
priority sits above Plausible's `selfContained` (1000) and below the
scalar instances (2000), so a container takes the shape walk and a
scalar takes its own instance. -/
instance (priority := 1200) sszSampleableExt {T : Type} [r : SSZRepr T] : Plausible.SampleableExt T where
  proxy := r.shape.interp
  proxyRepr := reprShape r.shape
  shrink := ⟨shrinkShape r.shape⟩
  sample := ⟨genShape r.shape⟩
  interp := r.fromRepr

end EthCLLib.TheoremVectors
