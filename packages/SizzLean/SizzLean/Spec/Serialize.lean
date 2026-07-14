import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.Constants

/-!
# `SizzLean.Spec.Serialize`: total SSZ encoder

Implements the encode side of consensus-specs *§Serialization*
(`simple-serialize.md`): a total recursion on `SSZType` mapping a
value of `s.interp` to its canonical wire-form `ByteArray`.

## Endianness: little-endian everywhere

Per spec *§Serialization, Basic types*, every multi-byte integer
(basic types and offset placeholders alike) is little-endian: byte 0
carries the eight least-significant bits. `uint16LE`, `uint32LE`,
`uint64LE` below emit exactly this layout.

## Container offset arithmetic: the load-bearing fiddly bit

A container with fields `f₁..fₖ` is encoded as a *fixed-size prefix*
followed by a *variable-size body region*. Each fixed-size field
contributes its full bytes to the prefix; each variable-size field
contributes a `BYTES_PER_LENGTH_OFFSET = 4`-byte little-endian
`uint32` *offset* (pointing into the body region) to the prefix and
its full bytes to the body region. The first variable field's
offset equals the prefix width; subsequent offsets advance by the
size of the previous body. The same offset-table layout is used by
`vector` and `list` of variable-size element types, see
`serializeVarElemsAux`.

Per spec *§Serialization, Variable-size types* and the worked
example.

## `Bitlist` trailing-delimiter bit (an SSZ subtlety with fork history)

The `bitlist` of `n` data bits is encoded as `n + 1` bits LSB-packed
into bytes: the data bits, then a single `1` bit marking the end. So
an *empty* bitlist serializes to a single `0x01` byte (just the
delimiter); the spec is explicit and at least one major client has
shipped a fork-causing bug here. Per spec *§Serialization, Bitlist*.
The decoder side recovers `n` from the position of the
most-significant `1` in the last byte (see `Spec/Deserialize.lean`).

## `Bitvector` (no trailing bit)

A `bitvector` of length `n` packs exactly `n` bits LSB-first into
`⌈n/8⌉` bytes; padding bits in the final byte are zero. No
delimiter, the length is part of the schema, not on the wire. Per
spec *§Serialization, Bitvector*.

## Empty `List` (zero bytes)

An empty list serializes as the empty `ByteArray`. The decoder
recovers length `0` because the buffer is empty / the variable
region is empty. Per spec *§Serialization, List*.

## Lean idioms used here, annotated on first appearance

* `mutual ... end`: a block of mutually recursive definitions whose
  termination is checked jointly. Same shape `Spec/Interp.lean` uses
  for the same reason: list traversals must be inlined as helpers
  descending on the list, called by the `SSZType`-driven recursion,
  because passing the recursive function through a higher-order
  argument hides the descent from Lean 4.29.1's structural-recursion
  checker.
* `ByteArray.empty.push b`: single-byte append; `ByteArray.append`
  (`++`) concatenates. Lean compiles `push` to in-place mutation
  when the refcount is 1.
* `BitVec.toNat`: interpret a bitvector as a natural number; used
  to feed `natToLEBytes` for `uintN` widths beyond 64.
* `Subtype.val` (`.val` projection): extract the underlying
  `Array` from `{ xs // p xs }`; the proof component is irrelevant
  for serialization.
-/

set_option autoImplicit false

namespace SizzLean.Spec


/-! ### Layout helpers (recurse on `SSZType` structure only)

`isFixedSize` decides whether a shape's serialized byte length is a
function of the schema alone; `fixedByteSize` returns that length
when so. Both must mutually recurse over `List SSZType` (because
`container fs` is fixed iff every `fs` is), same higher-order-recursion
trap `Spec/Interp.lean` already worked around with mutual helpers,
so the same shape is repeated here. -/

mutual

/-- Whether an SSZ shape has a fixed serialized byte length determined
purely by the schema. The spec calls this *fixed-size* (versus
*variable-size*); the offset-table machinery in `serializeFieldsAux`
keys off this predicate. -/
def SSZType.isFixedSize : SSZType → Bool
  | .uintN _      => true
  | .bool         => true
  | .vector t _   => SSZType.isFixedSize t
  | .list _ _     => false
  | .bitvector _  => true
  | .bitlist _    => false
  | .container fs => SSZType.allFixedSize fs

/-- `isFixedSize` lifted over a field list. -/
def SSZType.allFixedSize : List SSZType → Bool
  | []      => true
  | t :: ts => SSZType.isFixedSize t && SSZType.allFixedSize ts

end

/-- Whether an SSZ shape is a *basic* type, one of the byte-level
primitives `uintN`, `bool`. Per the SSZ Merkleization spec, basic-element
collections pack into 32-byte chunks; composite-element collections
merkleize per-element `hash_tree_root`s. The two paths differ even when
the composite element is fixed-size (e.g. `Vector[FixedTestStruct, 4]`),
so this predicate is the right dispatch on the Merkleization side. -/
def SSZType.isBasicType : SSZType → Bool
  | .uintN _    => true
  | .bool       => true
  | _           => false

mutual

/-- Serialized byte length of a fixed-size shape; returns `0` on
variable-size shapes (callers must guard with `isFixedSize`). The
arithmetic mirrors the spec's *§Serialization* per-type byte counts. -/
def SSZType.fixedByteSize : SSZType → Nat
  | .uintN n      => (n + 7) / 8
  | .bool         => 1
  | .vector t n   => SSZType.fixedByteSize t * n
  | .list _ _     => 0
  | .bitvector n  => (n + 7) / 8
  | .bitlist _    => 0
  | .container fs => SSZType.fixedByteSizeFields fs

/-- Sum of `fixedByteSize` over a field list. -/
def SSZType.fixedByteSizeFields : List SSZType → Nat
  | []      => 0
  | t :: ts => SSZType.fixedByteSize t + SSZType.fixedByteSizeFields ts

end

/-- Width a single field contributes to a container's fixed-size
prefix: its full bytes if fixed, else `BYTES_PER_LENGTH_OFFSET`
(the offset placeholder). -/
def SSZType.fixedSectionSize (t : SSZType) : Nat :=
  if t.isFixedSize then t.fixedByteSize else BYTES_PER_LENGTH_OFFSET

/-- Byte offset where a container's variable-body region starts,
i.e., the total fixed-prefix width. -/
def SSZType.fixedSectionSizeFields : List SSZType → Nat
  | []      => 0
  | t :: ts => t.fixedSectionSize + SSZType.fixedSectionSizeFields ts

/-! ### Little-endian primitive encoders

These are package-internal helpers, the user-facing API is
`SSZType.serialize`, but exposed as plain `def` (not `private`) so the
Layer 2 proofs in `Proofs/Roundtrip.lean` can `unfold` / `simp` them
through their public name when discharging the `.uintN N` arms of
`decode_encode`. `unfold` can see through `private`, but `simp` cannot
without a public name. -/

/-- `UInt32` → 4 little-endian bytes. -/
def uint32LE (x : UInt32) : ByteArray :=
  ByteArray.empty
    |>.push x.toUInt8
    |>.push (x >>> 8).toUInt8
    |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8

/-- `UInt16` → 2 little-endian bytes. -/
def uint16LE (x : UInt16) : ByteArray :=
  ByteArray.empty
    |>.push x.toUInt8
    |>.push (x >>> 8).toUInt8

/-- `UInt64` → 8 little-endian bytes. -/
def uint64LE (x : UInt64) : ByteArray :=
  ByteArray.empty
    |>.push x.toUInt8
    |>.push (x >>> 8).toUInt8
    |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8
    |>.push (x >>> 32).toUInt8
    |>.push (x >>> 40).toUInt8
    |>.push (x >>> 48).toUInt8
    |>.push (x >>> 56).toUInt8

/-- `Nat` → `width` little-endian bytes (truncating). Used for the
`BitVec n`-backed fallback at `uintN` widths beyond 64 and for
generic offset emission. Recurses structurally on `width`.

`protected`: the Layer 2 roundtrip proof for the `uintN 128 / 256`
arms in `Proofs/UIntWide.lean` reasons through this writer's
per-byte recursion, so it must be reachable, but it is
proof-internal, not part of the general `SizzLean.Spec` surface.
`protected` keeps a bare `open SizzLean.Spec` from pulling it into
scope; the proof file names it with an explicit
`open SizzLean.Spec (natToLEBytes)`. -/
protected def natToLEBytes : (width : Nat) → (n : Nat) → ByteArray → ByteArray
  | 0,     _, acc => acc
  | k + 1, m, acc =>
      SizzLean.Spec.natToLEBytes k (m / 256) (acc.push (Nat.toUInt8 (m % 256)))

/-- `BitVec n` → `⌈n/8⌉` little-endian bytes. -/
private def bitvecToLE (n : Nat) (b : BitVec n) : ByteArray :=
  SizzLean.Spec.natToLEBytes ((n + 7) / 8) b.toNat .empty

/-! ### Bit packing (LSB-first within each byte)

Per spec *§Serialization, Bitvector / Bitlist*: bit at index 0 of
the input goes to bit 0 (the LSB) of byte 0; bit 8 goes to bit 0 of
byte 1; etc. -/

/-- Pack 0–8 bits into a single byte LSB-first. Excess bits beyond
position 7 are dropped; callers chunk to length ≤ 8. Public so the
Layer 2 bit-packing inverse proof in `Proofs/BitPack.lean` can
reach it. -/
def bitsToByte : List Bool → Nat → UInt8 → UInt8
  | [],            _, acc => acc
  | true  :: rest, k, acc => bitsToByte rest (k+1) (acc ||| ((1 : UInt8) <<< Nat.toUInt8 k))
  | false :: rest, k, acc => bitsToByte rest (k+1) acc

/-- LSB-first byte packing of an arbitrary-length bit list. Bytes are
emitted in order: byte 0 carries bits 0..7, byte 1 carries bits 8..15,
and so on. The pattern peels off 8 bits per recursive step (so
recursion is structurally decreasing), with a tail clause for any
final 1..7-bit fragment. -/
def packBitsLE : List Bool → ByteArray
  | [] => .empty
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      let byte := bitsToByte [b0, b1, b2, b3, b4, b5, b6, b7] 0 0
      (ByteArray.empty.push byte) ++ packBitsLE rest
  | bs => -- 1..7 bits remaining; bitsToByte tolerates short input
      ByteArray.empty.push (bitsToByte bs 0 0)

/-- `BitVec n` → packed bytes (LSB-first, no delimiter). -/
def bitvecToBytes (n : Nat) (bv : BitVec n) : ByteArray :=
  packBitsLE ((List.range n).map (fun i => bv.getLsbD i))

/-- `Bitlist` → packed bytes plus the trailing-`1` delimiter bit. An
empty input produces a single `0x01` byte. -/
def bitlistToBytes (bs : Array Bool) : ByteArray :=
  packBitsLE (bs.toList ++ [true])

/-! ### The serializer

A single `mutual` block: `serialize` recurses structurally on
`s : SSZType`; the list-traversing helpers
(`serializeFixedElems`, `serializeVarElemsAux`, `serializeFieldsAux`)
recurse structurally on their `List` argument. Cross-calls descend
on subterms, same shape `Spec/Interp.lean` uses, so Lean 4.29.1's
structural-recursion checker accepts the block without
`termination_by` annotations. -/

mutual

/-- Total SSZ serializer.

The `vector` / `list` / `progList` cases dispatch on
`isFixedSize t`: fixed-size element types concatenate via
`serializeFixedElems`; variable-size types build the offset table
via `serializeVarElemsAux`. The `container` case sums field
contributions through `serializeFieldsAux`, which handles fixed and
variable fields together via the same offset-table machinery. -/
def SSZType.serialize : (s : SSZType) → s.interp → ByteArray
  | .uintN 8,      x  =>
      -- The `let x' : UInt8 := x` idiom appears throughout this file.
      -- `x : SSZType.interp (.uintN 8)` is definitionally `UInt8`, but
      -- the elaborator does not aggressively unfold `interp` across
      -- the sibling mutual block in `Spec/Interp.lean`. Annotating
      -- the local binding with the expected type forces a defeq check
      -- which the kernel discharges by reducing `interp` one arm, the
      -- minimal nudge that lets later operations on `x'` resolve their
      -- typeclass instances (`push`, `>>>`, `if then else`, …).
      let x' : UInt8 := x
      -- `ByteArray.empty.push x'` is dot notation: Lean infers
      -- `ByteArray.push : ByteArray → UInt8 → ByteArray` and inserts
      -- `ByteArray.empty` as the first argument.
      ByteArray.empty.push x'
  | .uintN 16,            x  =>
      let x' : UInt16 := x
      uint16LE x'
  | .uintN 32,            x  =>
      let x' : UInt32 := x
      uint32LE x'
  | .uintN 64,            x  =>
      let x' : UInt64 := x
      uint64LE x'
  | .uintN 128,           x  =>
      -- `interp (.uintN 128) = BitVec 128` (the catch-all arm of
      -- `interp` in `Spec/Interp.lean`). Force the defeq via `let`
      -- so the typeclass machinery sees `BitVec 128` for `.toNat`.
      let x' : BitVec 128 := x
      SizzLean.Spec.natToLEBytes 16 x'.toNat .empty
  | .uintN 256,           x  =>
      -- Used by `ExecutionPayload.base_fee_per_gas` (Bellatrix+).
      let x' : BitVec 256 := x
      SizzLean.Spec.natToLEBytes 32 x'.toNat .empty
  | .uintN _,             _  =>
      -- Non-spec `uintN` widths (only {8,16,32,64,128,256} valid).
      -- Returning `.empty` keeps `serialize` total.
      .empty
  | .bool,                b  =>
      let b' : Bool := b
      -- The `if b' then 1 else 0` form expects `b' : Bool` with
      -- `Decidable Bool` available (it is, trivially); `1` and `0` are
      -- elaborated at the expected `UInt8` from `push`'s signature.
      ByteArray.empty.push (if b' then 1 else 0)
  | .vector t _,          v  =>
      -- `v : SSZType.interp (.vector t n)` unfolds to `Vector t.interp n`.
      -- `v.toList : List t.interp` via dot notation on `Vector.toList`.
      if t.isFixedSize then
        SSZType.serializeFixedElems t v.toList
      else
        let xs : List t.interp := v.toList
        let varOff : Nat := xs.length * BYTES_PER_LENGTH_OFFSET
        let (offs, bodies) := SSZType.serializeVarElemsAux t xs varOff
        offs ++ bodies
  | .list t _,            xs =>
      -- `xs : { ys : Array t.interp // ys.size ≤ cap }`; `xs.val` is
      -- the underlying `Array t.interp` (subtype projection, the
      -- proof component is discarded for serialization).
      if t.isFixedSize then
        SSZType.serializeFixedElems t xs.val.toList
      else
        let ys : List t.interp := xs.val.toList
        let varOff : Nat := ys.length * BYTES_PER_LENGTH_OFFSET
        let (offs, bodies) := SSZType.serializeVarElemsAux t ys varOff
        offs ++ bodies
  | .bitvector n,         bv => bitvecToBytes n bv
  | .bitlist _,           bs => bitlistToBytes bs.val
  | .container fs, vs =>
      -- `vs : SSZType.interp (.container fs)` unfolds to
      -- `SSZType.interpFields fs`, definitionally a right-nested
      -- `Prod` chain ending in `PUnit`. `serializeFieldsAux` walks
      -- it cons-by-cons via `.1` / `.2` projections.
      let (fix, var) : ByteArray × ByteArray :=
        SSZType.serializeFieldsAux fs vs (SSZType.fixedSectionSizeFields fs)
      fix ++ var

/-- Concatenate per-element serializations (fixed-size element type). -/
def SSZType.serializeFixedElems : (t : SSZType) → List t.interp → ByteArray
  | _, []      => .empty
  | t, x :: xs => SSZType.serialize t x ++ SSZType.serializeFixedElems t xs

/-- Build a parallel pair `(offsetTable, bodies)` for a variable-size
element type. The third argument is the running offset within the
body region (initially the byte position right after the offset
table). Caller concatenates `offs ++ bodies`. -/
def SSZType.serializeVarElemsAux :
    (t : SSZType) → List t.interp → Nat → ByteArray × ByteArray
  | _, [],      _      => (.empty, .empty)
  | t, x :: xs, varOff =>
      let xBytes := SSZType.serialize t x
      let offBytes := uint32LE (Nat.toUInt32 varOff)
      let (offs, bodies) := SSZType.serializeVarElemsAux t xs (varOff + xBytes.size)
      (offBytes ++ offs, xBytes ++ bodies)

/-- Plain `container` serializer with mixed fixed/variable fields.
Returns `(fixedPrefix, variableBody)`; the third argument is the
running offset within the variable body, seeded at the total
fixed-prefix width by the call site.

In the `t :: ts` arm, `vs : SSZType.interpFields (t :: ts)` unfolds
to `SSZType.interp t × SSZType.interpFields ts`, so `vs.1` and `vs.2`
are the field head and tail respectively. Lean recovers their
types from `Prod.fst`/`Prod.snd`'s signatures applied to the
unfolded `Prod`. The same defeq mechanism that powers the `let x' :`
coercions in `serialize` makes these projections typecheck. -/
def SSZType.serializeFieldsAux :
    (fs : List SSZType) → SSZType.interpFields fs → Nat → ByteArray × ByteArray
  | [],      _,  _      => (.empty, .empty)
  | t :: ts, vs, varOff =>
      let xBytes : ByteArray := SSZType.serialize t vs.1
      if t.isFixedSize then
        let (fix, var) := SSZType.serializeFieldsAux ts vs.2 varOff
        (xBytes ++ fix, var)
      else
        let offBytes : ByteArray := uint32LE (Nat.toUInt32 varOff)
        let (fix, var) := SSZType.serializeFieldsAux ts vs.2 (varOff + xBytes.size)
        (offBytes ++ fix, xBytes ++ var)

end

end SizzLean.Spec
