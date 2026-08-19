import SizzLean.Spec.HashTreeRoot
import SizzLean.Spec.GIndexError

/-!
# `SizzLean.Spec.GeneralizedIndex`: SSZ generalized-index arithmetic

A *generalized index* numbers the nodes of a binary Merkle tree. The root is `1`,
and node `k`'s children are `2k` and `2k+1` (consensus-specs *§Merkle proofs*).
A node at tree `depth` and left-to-right `index` (`0 ≤ index < 2^depth`) has
generalized index `2^depth + index`.

This module models `get_power_of_two_ceil`, `get_generalized_index`,
`get_generalized_index_length` (= `floorLog2`) and `get_subtree_index`. It also
recovers `(depth, index)` from a gindex, the pair the `isValidMerkleBranch`
completeness kit consumes.

Pure `Nat`/`SSZType` arithmetic, kernel-clean, zero new axioms.

## Which definition this models

`ssz/merkle-proofs.md` presents `get_generalized_index` as Python over
`item_length` / `chunk_count` / `get_item_position`. That block is prose, not
generated spec code: it names `Elements` and `Bits`, which exist in neither
remerkleable nor the pyspec. The executable spec builds a gindex through
remerkleable (`Path(ssz_class) / step …`, then `Path.gindex()`). The governing
rule is therefore the per-type `key_to_static_gindex`, which `itemPosition`
models.
Where the two readings differ, notably on how a bitfield step selects its chunk,
the executable one wins.

## Where this connects

The converse lemmas below tie a gindex to the `(depth, index)` pair.
`EthCLLib.Proofs.GeneralizedIndexBranch` carries that through to acceptance for a
container field, one step and two. That covers the light-client
`EXECUTION_PAYLOAD` / sync-committee / `FINALIZED_ROOT` /
`EXECUTION_BLOCK_HASH` gindices and the Fulu data column sidecar's
`blob_kzg_commitments` proof.

A path crossing a composite *list* element (the Deneb blob sidecar's
`blob_kzg_commitments[i]`) is out of reach. It needs an openability lemma for the
mix-in-length level, which the tree vocabulary does not carry.
-/

set_option autoImplicit false

namespace SizzLean.Spec

/-- A generalized Merkle-tree index (consensus-specs *§Merkle proofs*). A plain
`Nat`. The valid range is `g ≥ 1`, since the root is `1`. Hypotheses pin that
range where it matters, and no subtype does. -/
abbrev GeneralizedIndex := Nat

/-- `get_generalized_index_length(g)` = `floorlog2(g)`: the tree depth a gindex
addresses. Unconditionally `Nat.log2 g`, including `g = 0`, where `log2 0 = 0`. -/
def floorLog2 (g : GeneralizedIndex) : Nat := g.log2

/-- `get_subtree_index(g) = g % 2^floorlog2(g)`: the left-to-right position of the
addressed node within its depth level. -/
def getSubtreeIndex (g : GeneralizedIndex) : Nat := g % 2 ^ floorLog2 g

-- Worked positions: the root is 1, and node 12 sits at depth 3, index 4.
example : floorLog2 1 = 0 := rfl
example : floorLog2 12 = 3 := rfl
example : getSubtreeIndex 12 = 4 := rfl

/-- `get_power_of_two_ceil(x)` (consensus-specs *§Merkle proofs helpers*): the
smallest power of two `≥ x`, with `0, 1 ↦ 1`. `chunkDepth` already computes that
ceiling's exponent. -/
def getPowerOfTwoCeil (x : Nat) : Nat := 2 ^ chunkDepth x

-- From the spec table: 0→1, 3→4 (rounds up), 4→4 (already a power of two).
example : getPowerOfTwoCeil 0 = 1 := rfl
example : getPowerOfTwoCeil 3 = 4 := rfl
example : getPowerOfTwoCeil 4 = 4 := rfl

/-- One step of an SSZ access path. `field k` selects container field `k`, or
element `k` of a vector or list. `length` selects a list's `__len__` node.
Non-stringly-typed model of the spec's `int | SSZVariableName`. -/
inductive PathStep where
  | field  : Nat → PathStep
  | length : PathStep

/-- `chunk_count(typ)`: number of 32-byte chunks the top level of `typ` occupies.
A container gives its field count. Vectors and lists of basic types pack several
elements per chunk, modeled per the spec's `chunk_count` arms. -/
def chunkCount : SSZType → Nat
  | .container fs   => fs.length
  | .vector t n     => (n * itemLength t + 31) / 32
  | .list t cap     => (cap * itemLength t + 31) / 32
  | .bitvector n    => (n + 255) / 256
  | .bitlist cap    => (cap + 255) / 256
  | .uintN _        => 1
  | .bool           => 1
where
  /-- `item_length`: byte width of a basic type, else 32. -/
  itemLength : SSZType → Nat
    | .uintN bits => (bits + 7) / 8
    | .bool       => 1
    | _           => 32

/-- Which 32-byte chunk of `typ`'s top level holds element (or field) `k`.

A container gives each field its own chunk, so there the position is the field
index. Everything else packs. A vector or list of basic types measures the
element's byte offset and divides by the 32-byte chunk width, and a bitfield fits
256 bits per chunk. Modeled on remerkleable's per-type `key_to_static_gindex`
(`complex.py`, `bitfields.py`).

The multiplication comes first, as in the spec's `start = k * item_length(elem)`
then `start // 32`. `itemLength t` is `32` for composite `t`, so the one formula
covers packed and unpacked alike. -/
def itemPosition : SSZType → Nat → Nat
  | .container _, k => k
  | .bitvector _, k => k / 256
  | .bitlist _,   k => k / 256
  | .vector t _,  k => k * chunkCount.itemLength t / 32
  | .list t _,    k => k * chunkCount.itemLength t / 32
  | _,            k => k

-- A container is one field per chunk, so the position is the field index.
example : itemPosition (.container [.bool, .bool, .bool]) 2 = 2 := rfl
-- Four `uint64`s fill one chunk, so every element of them sits at position 0.
example : itemPosition (.vector (.uintN 64) 4) 2 = 0 := rfl
-- 32 bytes per chunk for a byte list, so element 33 has moved on to chunk 1.
example : itemPosition (.list (.uintN 8) 64) 33 = 1 := rfl
-- Bitfields pack 256 bits to the chunk, not 32 bytes.
example : itemPosition (.bitlist 512) 300 = 1 := rfl
-- A width that does not divide 32: element 10 of a `uint24` vector starts at
-- byte 30, so it is still chunk 0.
example : itemPosition (.vector (.uintN 24) 16) 10 = 0 := rfl
-- A width wider than a chunk: element 3 of a `uint512` vector starts at byte
-- 192, chunk 6.
example : itemPosition (.vector (.uintN 512) 4) 3 = 6 := rfl

/-- `get_elem_type(typ, p)`: the type a path step lands on. Container field type,
or the element type of a vector / list, or `bool` for a bitfield, whose elements
are single bits. `.length` lands on the `uint64` length node.

A bitfield element and a `.length` node are both basic, so `getGeneralizedIndex`
raises `basicTypeDescent` on any step past one. That guard keeps the off-shape
`| t, _ => t` arm out of view. -/
def elemType : SSZType → PathStep → SSZType
  | .container fs, .field k => fs.getD k .bool
  | .vector t _,   .field _ => t
  | .list t _,     .field _ => t
  | .bitvector _,  .field _ => .bool
  | .bitlist _,    .field _ => .bool
  | _,             .length  => .uintN 64
  | t,             _        => t

/-- How many positions a `.field` step can name on `typ`. A container holds its
fields, a vector its elements, and a list or bitfield its declared capacity. The
capacity bounds the step. A gindex addresses a tree position, and a list's tree
has capacity-many leaves however few are filled.

Basic types get `0`, which no `k` satisfies. `getGeneralizedIndex` never reaches
that arm: `basicTypeDescent` refuses a basic type first. -/
def stepCapacity : SSZType → Nat
  | .container fs => fs.length
  | .vector _ n   => n
  | .list _ cap   => cap
  | .bitvector n  => n
  | .bitlist cap  => cap
  | .uintN _      => 0
  | .bool         => 0

/-- `get_generalized_index(typ, *path)`: fold the path into the gindex of the
addressed node. `length` descends to the list length node (`base·2 + 1`). A field
step multiplies by `base · getPowerOfTwoCeil (chunkCount typ)` and adds
`itemPosition typ k`, where `base` is `2` for list and bitlist (the length
mix-in level) and `1` otherwise.

The added term is the *chunk* position. It coincides with the path index for a
container and for composite elements. The two diverge wherever the top level
packs, and `itemPosition` carries that distinction.

Partial, as the spec is, and it refuses a path three ways.
`basicTypeDescent` covers `assert not issubclass(typ, BasicValue)`, checked
before every step. `lengthOnNonList` covers
`assert issubclass(typ, (List, ByteList))` on a `.length` step.
`indexOutOfRange` covers the `KeyError` each composite `key_to_static_gindex`
raises for a step past `stepCapacity`. A path the spec refuses gets an error
rather than a number, so an off-shape path cannot pass for a real tree
position. -/
def getGeneralizedIndex (typ : SSZType) (path : List PathStep) :
    Except GIndexError GeneralizedIndex :=
  go typ path 1
where
  go : SSZType → List PathStep → GeneralizedIndex → Except GIndexError GeneralizedIndex
    | _, [],           acc => .ok acc
    | t, step :: rest, acc =>
        -- `merkle-proofs.md:178`: a basic type has no children, so no step of any
        -- kind continues past one.
        if t.isBasicType then .error .basicTypeDescent
        else match step with
          | .length =>
              -- `merkle-proofs.md:180`: only a list carries a length mix-in node.
              match t with
              | .list _ _ => go (.uintN 64) rest (acc * 2 + 1)
              | _         => .error .lengthOnNonList
          | .field k =>
              -- The range check every composite `key_to_static_gindex` runs. It
              -- also keeps `elemType`'s `fs.getD k` off its default.
              if k ≥ stepCapacity t then .error .indexOutOfRange
              else
                let base := match t with
                  | .list _ _ | .bitlist _ => 2
                  | _ => 1
                go (elemType t (.field k)) rest
                  (acc * base * getPowerOfTwoCeil (chunkCount t) + itemPosition t k)

example :
    getGeneralizedIndex (.container [.bool, .bool, .bool, .bool, .bool]) [.field 3]
      = .ok 11 := rfl

-- x.y[2] where x is a 2-field container, y is field 1 = list of 4 bools. Booleans
-- are one byte, so all four pack into chunk 0 and the element step contributes 0,
-- not 2. Getting this wrong is invisible without an example like this one.
example :
    getGeneralizedIndex (.container [.bool, .list .bool 4]) [.field 1, .field 2]
      = .ok (3 * 2 * getPowerOfTwoCeil ((4 * 1 + 31) / 32) + 0) := rfl
-- The same packing at the top level: `Vector[uint64, 4]` is a single chunk, so
-- every element addresses gindex 1, the root's own chunk.
example : getGeneralizedIndex (.vector (.uintN 64) 4) [.field 2] = .ok 1 := rfl
-- Composite elements are one per chunk, so there the position is the index.
example :
    getGeneralizedIndex (.vector (.container [.bool, .bool]) 4) [.field 2]
      = .ok (2 ^ 2 + 2) := rfl
-- len(x.y): the __len__ node sits right of the list body root.
example :
    getGeneralizedIndex (.container [.bool, .list .bool 4]) [.field 1, .length]
      = .ok 7 := rfl

/-! The refused paths, one per assert. Without these the arms above would be
indistinguishable from a total function that happens to agree on-shape. -/

-- `merkle-proofs.md:178`, descending into a basic type.
example : getGeneralizedIndex (.uintN 64) [.field 0] = .error .basicTypeDescent := rfl
example : getGeneralizedIndex .bool [.field 7] = .error .basicTypeDescent := rfl
-- A bitfield element is a bit, so the same assert refuses the step after one.
-- `elemType` lands on `.bool`.
example :
    getGeneralizedIndex (.bitlist 512) [.field 300, .field 300]
      = .error .basicTypeDescent := rfl
-- `merkle-proofs.md:180`, `__len__` on a shape with no length mix-in.
example :
    getGeneralizedIndex (.container [.bool, .bool]) [.length]
      = .error .lengthOnNonList := rfl
example : getGeneralizedIndex (.vector .bool 4) [.length] = .error .lengthOnNonList := rfl
-- A field index past the field list. Without the range check this returns
-- `.ok 9`, a depth-3 address in a tree one level deep.
example :
    getGeneralizedIndex (.container [.bool, .bool]) [.field 7]
      = .error .indexOutOfRange := rfl
-- An element past a vector's length, and past a list's capacity.
example :
    getGeneralizedIndex (.vector (.container [.bool]) 4) [.field 99]
      = .error .indexOutOfRange := rfl
example : getGeneralizedIndex (.list .bool 4) [.field 4] = .error .indexOutOfRange := rfl
-- Bitfields bound by bits, not by chunks: 512 bits is 2 chunks, and bit 512 is
-- one past the end.
example : getGeneralizedIndex (.bitlist 512) [.field 512] = .error .indexOutOfRange := rfl
-- The capacity bounds the step, so the last addressable position of a list is
-- `cap - 1` however few elements it holds.
example : getGeneralizedIndex (.list .bool 4) [.field 3] = .ok 2 := rfl

/-- `2 ^ d ≤ n < 2 ^ (d + 1)` pins `n.log2` to `d`. The toolchain's
`Nat.log2_eq_iff` states that equivalence; this names the direction the
decomposition lemmas below use, and discharges its `n ≠ 0` side condition from
the lower bound. -/
theorem log2_eq_of_bounds {n d : Nat} (hlo : 2 ^ d ≤ n) (hhi : n < 2 ^ (d + 1)) :
    n.log2 = d := by
  have hn : n ≠ 0 := by
    have := Nat.one_le_two_pow (n := d)
    omega
  exact (Nat.log2_eq_iff hn).mpr ⟨hlo, hhi⟩

/-- **Converse decomposition (depth).** A gindex built as `2 ^ d + k` with
`k < 2 ^ d` reports depth `d`. The direction a call site needs: it constructs the
gindex from a known `(depth, index)` and must get them back. -/
theorem floorLog2_two_pow_add {d k : Nat} (hk : k < 2 ^ d) :
    floorLog2 (2 ^ d + k) = d := by
  unfold floorLog2
  refine log2_eq_of_bounds (Nat.le_add_right _ _) ?_
  rw [Nat.pow_succ]
  omega

/-- **Converse decomposition (index).** The same gindex reports position `k`. -/
theorem getSubtreeIndex_two_pow_add {d k : Nat} (hk : k < 2 ^ d) :
    getSubtreeIndex (2 ^ d + k) = k := by
  unfold getSubtreeIndex
  rw [floorLog2_two_pow_add hk, Nat.add_comm, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hk

/-- **The container arm, evaluated.** A single field step on a container is the
textbook gindex `2 ^ chunkDepth fieldCount + k`. Here `acc = 1` and `base = 1`,
and `itemPosition` on a container is the field index, a container being the one
shape that never packs.

`hk` discharges the range check. Without it the step is refused, so the
hypothesis is what makes this an equation about a gindex at all.

Not `rfl`, because `Nat.mul` recurses on its second argument, so `1 * x` does
not reduce while `x` is open. -/
theorem getGeneralizedIndex_container_field {fs : List SSZType} {k : Nat}
    (hk : k < fs.length) :
    getGeneralizedIndex (.container fs) [.field k]
      = .ok (2 ^ chunkDepth fs.length + k) := by
  simp [getGeneralizedIndex, getGeneralizedIndex.go, getPowerOfTwoCeil, chunkCount,
    itemPosition, stepCapacity, SSZType.isBasicType, Nat.not_le.mpr hk]

end SizzLean.Spec
