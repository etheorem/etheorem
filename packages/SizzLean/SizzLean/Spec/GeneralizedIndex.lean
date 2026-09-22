import SizzLean.Spec.HashTreeRoot

/-!
# `SizzLean.Spec.GeneralizedIndex`: `get_generalized_index`

Models `get_generalized_index(typ, path)` from
[`ssz/merkle-proofs.md`](https://github.com/ethereum/consensus-specs/blob/v1.5.0/ssz/merkle-proofs.md).
The spec folds left over the path, outermost step first:

```
root = 1
for p in path:
    root = root * base * get_power_of_two_ceil(chunk_count(typ)) + pos
    typ  = get_elem_type(typ, p)
```

so the outer step's slot lands in the *high* bits and the inner
step's slot in the low bits. The loop body is `SSZType.stepInto`
here: it returns the slot `pos`, the bit depth `d` of the factor
(`base · 2 ^ ⌈log₂ chunk_count⌉` is always a power of two, `2 ^ d`),
and the type the step lands in. `SSZType.generalizedIndexAux` is
the fold itself, one step at a time over an accumulator.

## The pieces, against the spec

* `SSZType.itemLength` is the spec's `item_length`: the byte width
  of a basic type, one chunk for everything compound.
* `SSZType.chunkCount` is the spec's `chunk_count`: `1` for basic
  types, `⌈length / 256⌉` for the bit shapes, `⌈length · item_length
  / 32⌉` for vectors and lists (the cap governs lists), and the
  field count for containers. `2 ^ chunkDepth n`
  is `get_power_of_two_ceil n`.
* A `field k` step applies to a container: `pos = k`, the block
  width is the field count rounded up to a power of two, and the
  next type is field `k`'s own type.
* An `elem i` step applies to a vector or a list: `pos =
  i · item_length / 32`, the *chunk* index, so a basic-element
  collection addresses the chunk that packs the element. A list's
  body is the left child of the mix-in-length pair, one extra
  factor of `2`. The next type is the element type.
* A `length` step applies to a list: `pos = 1`, factor `2`, and the
  next type is `uintN 64`, the spec's `__len__` arm. Any step past
  it lands on a basic type and is rejected, the spec's
  `assert not issubclass(typ, BasicValue)`.
* A step into a basic type, a step on the wrong constructor, or a
  slot out of range returns `none`, mirroring the spec's assertions.

## The bit-level statement

`SSZType.pathBits` spells the path the fold builds: per step, the
`d` low bits of `pos`, most significant first. The bridge to the
cache layer's `gindexBits` is
`SizzLean.Proofs.Merkle.gindexBits_generalizedIndex`
(`Proofs/Merkle/Gindex.lean`): a returned index's bit path is
exactly `pathBits`. The per-step corollaries there line the
container and composite-element cases up with the bit lists the
`sszUpdate` elaborator's `walkPath` emits.
-/

set_option autoImplicit false

namespace SizzLean.Spec
open SSZType

/-- One step of a Merkle path. -/
inductive PathStep where
  /-- The `k`-th field of a container. -/
  | field : (k : Nat) → PathStep
  /-- The `i`-th element of a vector or a list body. -/
  | elem : (i : Nat) → PathStep
  /-- The mix-in length leaf of a list. -/
  | length : PathStep

/-- The spec's `item_length`: the byte width a basic type occupies
in a packed body, one full chunk for everything compound. -/
def SSZType.itemLength (t : SSZType) : Nat :=
  if t.isBasicType then t.fixedByteSize else BYTES_PER_CHUNK

/-- The spec's `chunk_count`: how many chunks represent a type's
top-level members. `1` for basic types, `⌈length / 256⌉` for the bit
shapes, `⌈length · item_length / 32⌉` for vectors and lists (the cap
governs lists), the field count for containers. -/
def SSZType.chunkCount : SSZType → Nat
  | .uintN _ => 1
  | .bool => 1
  | .bitvector n => bitsToChunkCount n
  | .bitlist cap => bitsToChunkCount cap
  | .vector t n => bytesToChunkCount (n * itemLength t)
  | .list t cap => bytesToChunkCount (cap * itemLength t)
  | .container fs => fs.length

/-- One step of the fold: the slot `pos` inside the current node's
block, the block's bit depth `d` (the factor is `2 ^ d`), and the
type the step lands in. `none` marks a step the spec's assertions
reject. The basic-type check is the spec's
`assert not issubclass(typ, BasicValue)` at the top of the loop. -/
def SSZType.stepInto (s : SSZType) (step : PathStep) : Option (Nat × Nat × SSZType) :=
  if s.isBasicType then none
  else
    match s, step with
    | .container fs, .field k =>
        if hk : k < fs.length then
          some (k, chunkDepth fs.length, fs.get ⟨k, hk⟩)
        else none
    | .vector t n, .elem i =>
        if i < n then
          some (i * itemLength t / BYTES_PER_CHUNK,
            chunkDepth (chunkCount (.vector t n)), t)
        else none
    | .list t cap, .elem i =>
        if i < cap then
          some (i * itemLength t / BYTES_PER_CHUNK,
            chunkDepth (chunkCount (.list t cap)) + 1, t)
        else none
    | .list _ _, .length => some (1, 1, .uintN 64)
    | _, _ => none

/-- The fold behind `get_generalized_index`, one step at a time:
`acc ↦ 2 ^ d · acc + pos`. Structural on the path, so the equations
reduce on concrete paths. -/
def SSZType.generalizedIndexAux (s : SSZType) :
    List PathStep → Nat → Option Nat
  | [], acc => some acc
  | step :: rest, acc =>
      match s.stepInto step with
      | none => none
      | some (pos, d, s') => s'.generalizedIndexAux rest (acc * 2 ^ d + pos)

/-- `get_generalized_index`: the generalized index reached by
descending `path` from the root (`1`). `none` marks a path the
spec's assertions reject. -/
def SSZType.generalizedIndex (s : SSZType) (path : List PathStep) : Option Nat :=
  s.generalizedIndexAux path 1

/-- The bit path the fold builds: per step, the `d` low bits of the
step's slot, most significant bit first, outermost step's bits
first. The mirror of `generalizedIndexAux` at the bit level. -/
def SSZType.pathBits : (s : SSZType) → List PathStep → List Bool
  | _, [] => []
  | s, step :: rest =>
      match s.stepInto step with
      | none => []
      | some (pos, d, s') =>
          (List.range d).reverse.map (pos.testBit ·) ++ s'.pathBits rest

/-- The fold consumes the head step, then recurses. The equation
lemma the top theorems rewrite with. -/
theorem generalizedIndex_step (s : SSZType) (step : PathStep)
    (rest : List PathStep) (acc : Nat) :
    s.generalizedIndexAux (step :: rest) acc
      = match s.stepInto step with
        | none => none
        | some (pos, d, s') => s'.generalizedIndexAux rest (acc * 2 ^ d + pos) := rfl

/-- The empty path is the root: the base equation the one-step
top theorems below rewrite with. -/
theorem generalizedIndex_nil (s : SSZType) :
    s.generalizedIndex [] = some 1 :=
  rfl

/-! ### The one-step equations

`stepInto` on each valid shape/step pair, with the range and
basic-type conditions discharged. The top theorems and the
bit-level bridge in `Proofs/Merkle/Gindex.lean` rewrite with
these instead of unfolding the fold's match. -/

/-- A container's `field k` step: slot `k`, depth `chunkDepth
fs.length`, next type field `k`'s own type. -/
theorem stepInto_field (fs : List SSZType) (k : Nat) (hk : k < fs.length) :
    (container fs).stepInto (.field k)
      = some (k, chunkDepth fs.length, fs.get ⟨k, hk⟩) := by
  simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
    if_false, dif_pos hk]

/-- A vector's `elem i` step: slot `i · item_length / 32`, depth
`chunkDepth (chunk_count)`, next type the element type. -/
theorem stepInto_elem_vector (t : SSZType) (n i : Nat) (hi : i < n) :
    (vector t n).stepInto (.elem i)
      = some (i * itemLength t / BYTES_PER_CHUNK,
        chunkDepth (chunkCount (.vector t n)), t) := by
  simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
    if_false, if_pos hi]

/-- A list's `elem i` step: the vector step plus one level for the
mix-in-length pair. -/
theorem stepInto_elem_list (t : SSZType) (cap i : Nat) (hi : i < cap) :
    (list t cap).stepInto (.elem i)
      = some (i * itemLength t / BYTES_PER_CHUNK,
        chunkDepth (chunkCount (.list t cap)) + 1, t) := by
  simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true,
    if_false, if_pos hi]

/-- A list's `length` step: the mix-in pair's right child, and the
walk continues on `uint64`. -/
theorem stepInto_length (t : SSZType) (cap : Nat) :
    (list t cap).stepInto .length = some (1, 1, .uintN 64) := by
  simp only [SSZType.stepInto, SSZType.isBasicType, Bool.false_eq_true, if_false]

/-- A composite type's `itemLength` is one full chunk. -/
theorem itemLength_of_not_isBasicType (t : SSZType) (hc : ¬ t.isBasicType) :
    t.itemLength = BYTES_PER_CHUNK := by
  simp only [SSZType.itemLength, if_neg hc]

/-- A composite-element vector holds one chunk per element. -/
theorem chunkCount_vector_composite (t : SSZType) (n : Nat) (hc : ¬ t.isBasicType) :
    (vector t n).chunkCount = n := by
  show bytesToChunkCount (n * itemLength t) = n
  rw [itemLength_of_not_isBasicType t hc]
  show ((n * 32 + 31) / 32) = n
  omega

/-- A composite-element list holds one chunk per element. -/
theorem chunkCount_list_composite (t : SSZType) (cap : Nat) (hc : ¬ t.isBasicType) :
    (list t cap).chunkCount = cap := by
  show bytesToChunkCount (cap * itemLength t) = cap
  rw [itemLength_of_not_isBasicType t hc]
  show ((cap * 32 + 31) / 32) = cap
  omega

/-- The one-step path is the slot in the root's block. -/
theorem generalizedIndexAux_nil (s : SSZType) (acc : Nat) :
    s.generalizedIndexAux [] acc = some acc := rfl

/-- A container's field `k` sits at slot `k` of the field block:
`2 ^ chunkDepth fs.length + k`. This is the gindex the
`sszUpdate` macro writes for a container field update. -/
theorem generalizedIndex_field_top (fs : List SSZType) (k : Nat) (hk : k < fs.length) :
    (container fs).generalizedIndex [.field k]
      = some (2 ^ chunkDepth fs.length + k) := by
  simp only [SSZType.generalizedIndex, generalizedIndex_step,
    stepInto_field _ _ hk, Nat.one_mul, generalizedIndexAux_nil]

/-- A field of a field. Field `k₁` of container `fs` is the container `gs`, and the
path goes on into field `k₂` of `gs`. The outer gindex shifts left by
`chunkDepth gs.length` bits, and `k₂` fills them.

`hfield` names the type the second step starts from. `stepInto` returns it as
`fs.get`, so the proof restates it in that form. -/
theorem generalizedIndex_field_field (fs gs : List SSZType) (k₁ k₂ : Nat)
    (hk₁ : k₁ < fs.length) (hk₂ : k₂ < gs.length) (hfield : fs[k₁] = container gs) :
    (container fs).generalizedIndex [.field k₁, .field k₂]
      = some ((2 ^ chunkDepth fs.length + k₁) * 2 ^ chunkDepth gs.length + k₂) := by
  have hget : fs.get ⟨k₁, hk₁⟩ = container gs := by simpa using hfield
  simp only [SSZType.generalizedIndex, generalizedIndex_step,
    stepInto_field _ _ hk₁, hget, stepInto_field _ _ hk₂, Nat.one_mul,
    generalizedIndexAux_nil]

/-- A composite-element vector's element `i` sits at slot `i` of the
element block: `2 ^ chunkDepth n + i`. A basic-element vector packs
its elements into chunks, so its slot is the chunk index instead
(the packed examples below). -/
theorem generalizedIndex_elem_vector_top (t : SSZType) (n i : Nat)
    (hi : i < n) (hc : ¬ t.isBasicType) :
    (vector t n).generalizedIndex [.elem i]
      = some (2 ^ chunkDepth n + i) := by
  have hpos : i * itemLength t / BYTES_PER_CHUNK = i := by
    rw [itemLength_of_not_isBasicType t hc]
    show i * 32 / 32 = i
    omega
  simp only [SSZType.generalizedIndex, generalizedIndex_step,
    stepInto_elem_vector _ _ _ hi, hpos, chunkCount_vector_composite t n hc,
    Nat.one_mul, generalizedIndexAux_nil]

/-- A composite-element list's element `i` sits at slot `i` of the
body block, and the body is the left child of the mix-in-length
pair: `2 ^ (chunkDepth cap + 1) + i`. -/
theorem generalizedIndex_elem_list_top (t : SSZType) (cap i : Nat)
    (hi : i < cap) (hc : ¬ t.isBasicType) :
    (list t cap).generalizedIndex [.elem i]
      = some (2 ^ (chunkDepth cap + 1) + i) := by
  have hpos : i * itemLength t / BYTES_PER_CHUNK = i := by
    rw [itemLength_of_not_isBasicType t hc]
    show i * 32 / 32 = i
    omega
  simp only [SSZType.generalizedIndex, generalizedIndex_step,
    stepInto_elem_list _ _ _ hi, hpos, chunkCount_list_composite t cap hc,
    Nat.one_mul, generalizedIndexAux_nil]

/-- A list's `length` step is the right child of the mix-in-length
pair: `2 * 1 + 1 = 3`. -/
theorem generalizedIndex_length_top (t : SSZType) (cap : Nat) :
    (list t cap).generalizedIndex [.length] = some 3 := by
  simp only [SSZType.generalizedIndex, generalizedIndex_step,
    stepInto_length, generalizedIndexAux_nil]

/-! ### The spec's own examples, as `rfl`

The examples pin the fold's order, the packing rule, and the
rejections. -/

/-- Basic-element vectors pack: element 5 of `vector[uint64, 8]`
shares chunk 1 with elements 4 through 7, so the address is slot 1
of a two-chunk block: `2 * 1 + 1 = 3`. -/
example : (vector (uintN 64) 8).generalizedIndex [.elem 5] = some 3 := rfl

/-- Descending recurses on the field's own type, and the outer
step's bits sit high: field 1 of the outer container, then field 0
of the inner one, is `3 * 2 + 0 = 6`. -/
example : (container [container [uintN 64, uintN 64],
    container [uintN 64, uintN 64]]).generalizedIndex
    [.field 1, .field 0] = some 6 := rfl

/-- A list element descends through the mix-in pair's left child
first: element 1 of a four-element list of two-field containers is
`2 ^ (chunkDepth 4 + 1) + 1 = 9`, then field 1 doubles and adds:
`2 * 9 + 1 = 19`. -/
example : (list (container [uintN 64, uintN 64]) 4).generalizedIndex
    [.elem 1, .field 1] = some 19 := rfl

/-- A path cannot continue into a basic type: the spec's
`assert not issubclass(typ, BasicValue)`. -/
example : (container [uintN 64]).generalizedIndex
    [.field 0, .field 0] = none := rfl

/-- `__len__` descends into `uint64`, so nothing follows it. -/
example : (list (uintN 64) 10).generalizedIndex
    [.length, .elem 0] = none := rfl

/-- A basic-element list addresses the chunk that packs the
element: element 2 of `list[uint64, 10]` sits in chunk 0 of a
three-chunk body, below the mix-in pair: `2 ^ (chunkDepth 3 + 1)`. -/
example : (list (uintN 64) 10).generalizedIndex [.elem 2] = some 8 := rfl

end SizzLean.Spec
