import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.Constants
import SizzLean.Spec.SSZError
import SizzLean.Spec.Serialize

/-!
# `SizzLean.Spec.Deserialize`: total SSZ decoder

The decode side of consensus-specs *§Deserialization*. Returns
`Except SSZError (s.interp × Nat)`; the `Nat` is the count of bytes
consumed from the start of the buffer. The roundtrip theorem
(`Proofs/Roundtrip.lean`) is stated against this signature so a
longer buffer can be parsed and the remainder reasoned about.

## Lean idioms used here, annotated on first appearance

* `Except ε α`: sum type for a fallible computation; `.ok` carries
  success, `.error` an `SSZError`.
* `ByteArray.extract b s e`: slice `b[s..e]`. Used to hand a
  sub-range to a recursive call without changing the call signature.
* `dite` (`if h : p then ... else ...`): dependent `if` whose
  branches see the proof of `p` (or `¬ p`) as `h`. Used here to
  thread a bound check `n + k ≤ b.size` into the proof-carrying
  `ByteArray.get` call.
* `Subtype.mk` (`⟨arr, h⟩`): construct a `{ x // p x }` from a
  value `arr` and a proof `h : p arr`.

## Spec-side terms used here

* *Offset table*: the `uint32`-LE prefix of a variable-size container
  / variable-size-element list pointing at body positions.
* *Trailing-delimiter bit*: a `bitlist`'s last `1`-bit, marking the
  data end (subsequent bits are padding zeros). See
  `deserializeBitlist`.
-/

set_option autoImplicit false
-- The dependent match in `SSZType.deserialize` (each arm refining
-- `s.interp` against `interp`'s own per-constructor recursion) drives
-- the elaborator past the 200k default. Bumped here, not globally, so
-- only this file pays the cost.
set_option maxHeartbeats 5000000

namespace SizzLean.Spec

/-! ### Little-endian primitive readers

The `b[i]` notation is `GetElem`-typeclass indexing: with `b : ByteArray`
and `i : Nat`, Lean synthesises `GetElem ByteArray Nat UInt8 (· < ·.size)`
from core. The bracket-prime form `b[i]'h` supplies the bound proof
`h : i < b.size` directly, skipping the `decide`-by-default elaboration
on each access. The proofs here are discharged by `omega` from the outer
`if h : off + k ≤ b.size` guard. -/

/-- Read a single byte, `none` if out of bounds.

Package-internal but plain `def` (not `private`) so the Layer 2 proofs
in `Proofs/Roundtrip.lean` can `simp` it through its public name when
discharging the `.uintN N` arms of `decode_encode`. -/
def readUInt8At (b : ByteArray) (off : Nat) : Option UInt8 :=
  -- `dite` (`if h :`) splits on `Decidable (off < b.size)` and binds the
  -- proof `h` in the true branch; `b[off]` then synthesises the bound
  -- proof from `h` via the elaborator's local-context search.
  if h : off < b.size then .some b[off] else .none

/-- Read a little-endian `UInt16`. -/
def readUInt16LE (b : ByteArray) (off : Nat) : Option UInt16 :=
  if h : off + 2 ≤ b.size then
    -- `.toUInt16` is dot notation on `UInt8`; Lean resolves
    -- `UInt8.toUInt16 : UInt8 → UInt16`. The widening is zero-extending.
    let b0 : UInt16 := (b[off]'(by omega)).toUInt16
    let b1 : UInt16 := (b[off + 1]'(by omega)).toUInt16
    .some (b0 ||| (b1 <<< 8))
  else .none

/-- Read a little-endian `UInt32`. -/
def readUInt32LE (b : ByteArray) (off : Nat) : Option UInt32 :=
  if h : off + 4 ≤ b.size then
    let b0 : UInt32 := (b[off]'(by omega)).toUInt32
    let b1 : UInt32 := (b[off + 1]'(by omega)).toUInt32
    let b2 : UInt32 := (b[off + 2]'(by omega)).toUInt32
    let b3 : UInt32 := (b[off + 3]'(by omega)).toUInt32
    .some (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  else .none

/-- Read a little-endian `UInt64`. -/
def readUInt64LE (b : ByteArray) (off : Nat) : Option UInt64 :=
  if h : off + 8 ≤ b.size then
    let g (i : Nat) (h' : off + i < b.size) : UInt64 := (b[off + i]'h').toUInt64
    .some (g 0 (by omega) |||
          (g 1 (by omega) <<< 8)  ||| (g 2 (by omega) <<< 16) ||| (g 3 (by omega) <<< 24) |||
          (g 4 (by omega) <<< 32) ||| (g 5 (by omega) <<< 40) ||| (g 6 (by omega) <<< 48) |||
          (g 7 (by omega) <<< 56))
  else .none

/-- Read `width` little-endian bytes from `b` starting at `off` as a
`Nat`. Used for `uintN 128 / 256` widths where the value is stored
as a `BitVec n`. Returns `none` if the buffer is too short.

Horner-style accumulation reading from the *most-significant* byte
down to the *least-significant*: byte `b[off + width - 1]` is read
first (folded into `acc`), then `b[off + width - 2]`, …, finally
`b[off + 0]`. The recursion is structurally on `k = width`,
counting down. -/
private def readNatLE (b : ByteArray) (off width : Nat) : Option Nat :=
  if off + width > b.size then .none
  else
    let rec go : (k acc : Nat) → Nat
      | 0,     acc => acc
      | k + 1, acc =>
          -- Read `b[off + k]` (the byte with positional weight 256^k).
          let idx := off + k
          if h : idx < b.size then
            go k (acc * 256 + (b[idx]'h).toNat)
          else
            -- guarded by the outer size check; defensive
            acc * 256
    .some (go width 0)

/-! ### Variable-size container helper: pre-extract field offsets

`Spec/Serialize.lean`'s `serializeFieldsAux` writes a `uint32`-LE
offset into the fixed prefix for each variable-size field; the
deserializer needs to read those offsets *first* so it can later
slice each variable field's body out of the variable region. This
helper walks the field list once, accumulating one `Nat` per
variable-size field in declaration order. Fixed-size fields
contribute nothing to the result list but advance the running
prefix offset. -/

/-- Pre-extract variable-field offsets from the fixed prefix of a
container's serialized form. Returns one offset per variable-size
field in `fs`, in declaration order. -/
private def extractFieldOffsets (b : ByteArray) :
    (fs : List SSZType) → (off : Nat) → Except SSZError (List Nat)
  | [],      _   => .ok []
  | t :: ts, off =>
      if t.isFixedSize then
        extractFieldOffsets b ts (off + t.fixedByteSize)
      else
        match readUInt32LE b off with
        | .none => .error .tooShort
        | .some o =>
            match extractFieldOffsets b ts (off + BYTES_PER_LENGTH_OFFSET) with
            | .ok rest  => .ok (o.toNat :: rest)
            | .error e  => .error e

/-- Same shape as `extractFieldOffsets` but for the offset table at
the head of a *variable-size-element collection* (`vector` / `list`
/ `progList` whose element type is variable-size). The collection's
wire form is `[ off₀ off₁ … off_{n-1} | body₀ body₁ … ]`, where each
`off_i` is a `uint32`-LE and the count `n` is recovered from
`off₀ / 4` (the first body starts where the offset table ends).
`extractCollOffsets` reads `count` offsets starting at `off`. -/
private def extractCollOffsets (b : ByteArray) :
    (count : Nat) → (off : Nat) → Except SSZError (List Nat)
  | 0,     _   => .ok []
  | k + 1, off =>
      match readUInt32LE b off with
      | .none => .error .tooShort
      | .some o =>
          match extractCollOffsets b k (off + BYTES_PER_LENGTH_OFFSET) with
          | .ok rest  => .ok (o.toNat :: rest)
          | .error e  => .error e

/-! ### Bit unpacking (LSB-first inversion of `packBitsLE`)

Public defs (not `private`) so the Layer 2 bit-packing inverse
proof in `Proofs/BitPack.lean` can reach them. -/

/-- Read the LSB-first bits of one byte (positions 0..7). -/
def byteToBits (b : UInt8) : List Bool :=
  (List.range 8).map fun i => ((b >>> Nat.toUInt8 i) &&& 1) = 1

/-- Unpack a `ByteArray` to a `(8 × bytes.size)`-long `List Bool`,
LSB-first within each byte. Recurses structurally on `count`. -/
def unpackBitsLEAux (b : ByteArray) : (count off : Nat) → List Bool
  | 0,     _   => []
  | k + 1, off => byteToBits (b.get! off) ++ unpackBitsLEAux b k (off + 1)

/-- Convert a `List Bool` (LSB-first, treating `bs[0]` as bit 0) to
the `Nat` it encodes. Used to feed `BitVec.ofNat` for the
`bitvector` decode path. -/
def bitsToNat : List Bool → Nat
  | []        => 0
  | b :: rest => (if b then 1 else 0) + 2 * bitsToNat rest

/-- Find the position (0..7) of the most-significant `1` in `byte`,
returning `none` if `byte = 0`. Used to recover the `bitlist` data
length from its trailing-`1`-bit delimiter. Recurses structurally on
the descending search index. -/
def msbPosAux (byte : UInt8) : Nat → Option Nat
  | 0     => if (byte &&& 1) = 1 then .some 0 else .none
  | k + 1 =>
      if ((byte >>> Nat.toUInt8 (k+1)) &&& 1) = 1 then .some (k+1)
      else msbPosAux byte k

def msbPos (byte : UInt8) : Option Nat := msbPosAux byte 7

/-- `bitvector n` decoder. `protected`: the Layer 2 roundtrip proof
in `Proofs/BitPack.lean` reasons through its branches, so it must be
reachable, but it is proof-internal, not part of the general
`SizzLean.Spec` surface. `protected` keeps a bare `open
SizzLean.Spec` from pulling it into scope; the proof file names it
with an explicit `open SizzLean.Spec (deserializeBitvector)`. -/
protected def deserializeBitvector (n : Nat) (b : ByteArray) :
    Except SSZError (BitVec n × Nat) :=
  -- Per SSZ spec: bitvectors must have `n > 0`. The
  -- `ssz_generic/bitvector/invalid/bitvec_0` test asserts the
  -- zero-length case is invalid.
  if hn : n = 0 then .error .outOfRange
  else
    let need := (n + 7) / 8
    if h : b.size = need then
      -- Validate that high bits in the last byte (beyond bit `n-1`)
      -- are zero, the SSZ spec requires unused trailing padding
      -- bits to be zero. The
      -- `ssz_generic/bitvector/invalid/bitvec_<N>_max_<extra>` cases
      -- exercise this.
      let unusedBits := need * 8 - n
      if unusedBits > 0 then
        have hpos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
        have hneed : need ≥ 1 := by
          show (n + 7) / 8 ≥ 1; omega
        have hsize : b.size ≥ 1 := by rw [h]; exact hneed
        have hlt : b.size - 1 < b.size := by omega
        let lastByte := b[b.size - 1]'hlt
        let mask : UInt8 := (1 <<< Nat.toUInt8 unusedBits) - 1
        let shifted : UInt8 := lastByte >>> Nat.toUInt8 (8 - unusedBits)
        if shifted &&& mask ≠ 0 then .error .invalidOffset
        else
          let bits := (unpackBitsLEAux b need 0).take n
          .ok (BitVec.ofNat n (bitsToNat bits), need)
      else
        let bits := (unpackBitsLEAux b need 0).take n
        .ok (BitVec.ofNat n (bitsToNat bits), need)
    else if b.size < need then .error .tooShort
    else .error .trailingBytes

/-- `bitlist cap` decoder.

Empty buffer ⇒ `bitlistMissingDelimiter` (no delimiter at all).
Last byte = `0x00` ⇒ same error.
Otherwise: the position of the most-significant `1` in the last byte
is the bit-position of the delimiter; bits before it are data.
`protected` for the same reason as `deserializeBitvector`:
proof-internal, reached only by the explicit `open` in
`Proofs/BitPack.lean`, never by a bare `open SizzLean.Spec`. -/
protected def deserializeBitlist (cap : Nat) (b : ByteArray) :
    Except SSZError ({ bs : Array Bool // bs.size ≤ cap } × Nat) :=
  if h : b.size = 0 then .error .bitlistMissingDelimiter
  else
    have hlt : b.size - 1 < b.size := by omega
    let last := b[b.size - 1]'hlt
    match msbPos last with
    | .none     => .error .bitlistMissingDelimiter
    | .some pos =>
        let totalBits := (b.size - 1) * 8 + pos
        if totalBits > cap then .error .outOfRange
        else
          let bits := (unpackBitsLEAux b b.size 0).take totalBits
          let arr := bits.toArray
          if hsz : arr.size ≤ cap then .ok (⟨arr, hsz⟩, b.size)
          else .error .outOfRange

/-! ### The deserializer

Mutual block matching `Spec/Serialize.lean` shape:
`deserialize` recurses on `s : SSZType`; the list-traversing helpers
recurse on `count : Nat` (for fixed-element loops) or on
`fs : List SSZType` (for fields and unions). Cross-calls descend on
subterms or on `Nat` predecessors. -/

mutual

/-- Total SSZ deserializer. -/
def SSZType.deserialize : (s : SSZType) → ByteArray → Except SSZError (s.interp × Nat)
  | .uintN 8,  b =>
      match readUInt8At b 0 with
      | .some x => .ok (x, 1)
      | .none   => .error .tooShort
  | .uintN 16, b =>
      match readUInt16LE b 0 with
      | .some x => .ok (x, 2)
      | .none   => .error .tooShort
  | .uintN 32, b =>
      match readUInt32LE b 0 with
      | .some x => .ok (x, 4)
      | .none   => .error .tooShort
  | .uintN 64, b =>
      match readUInt64LE b 0 with
      | .some x => .ok (x, 8)
      | .none   => .error .tooShort
  | .uintN 128, b =>
      -- 16 little-endian bytes → `BitVec 128`. The `interp` arm for
      -- `.uintN n` (n ∉ {8,16,32,64}) reduces to `BitVec n`, so the
      -- `BitVec.ofNat 128 _` typechecks at `interp (.uintN 128)`.
      match readNatLE b 0 16 with
      | .some n => .ok (BitVec.ofNat 128 n, 16)
      | .none   => .error .tooShort
  | .uintN 256, b =>
      -- 32 little-endian bytes → `BitVec 256`. Used by
      -- `ExecutionPayload.base_fee_per_gas` (Bellatrix+).
      match readNatLE b 0 32 with
      | .some n => .ok (BitVec.ofNat 256 n, 32)
      | .none   => .error .tooShort
  | .uintN _,  _ => .error .tooShort -- non-spec uintN width (only {8,16,32,64,128,256} valid)
  | .bool,     b =>
      -- Per SSZ spec: `bool` is exactly `0x00` (false) or `0x01` (true).
      -- Any other byte value is invalid (rejects `byte_0x80`, `byte_2`, etc.
      -- from `ssz_generic/boolean/invalid/`).
      match readUInt8At b 0 with
      | .some 0 => .ok (false, 1)
      | .some 1 => .ok (true,  1)
      | .some _ => .error .invalidOffset  -- not a legal bool byte
      | .none   => .error .tooShort
  | .vector t n, b =>
      -- Per SSZ spec: vectors must have `n > 0`. The
      -- `ssz_generic/basic_vector/invalid/vec_*_0` test cases assert
      -- the zero-length case is invalid.
      if n = 0 then .error .outOfRange
      else if t.isFixedSize then
        let sz := t.fixedByteSize
        match SSZType.deserializeFixedElems t n b 0 sz with
        | .error e         => .error e
        | .ok (xs, used)   =>
            let arr := xs.toArray
            if h : arr.size = n then .ok (⟨arr, h⟩, used)
            else .error .tooShort
      else
        -- Variable-size element vector: the offset table has exactly
        -- `n` entries. First offset must equal `n * 4`.
        if b.size < n * BYTES_PER_LENGTH_OFFSET then .error .tooShort
        else
          match extractCollOffsets b n 0 with
          | .error e => .error e
          | .ok offs =>
              match SSZType.deserializeVarElems t offs b.size b with
              | .error e       => .error e
              | .ok xs =>
                  let arr := xs.toArray
                  if h : arr.size = n then .ok (⟨arr, h⟩, b.size)
                  else .error .tooShort
  | .list t cap, b =>
      if t.isFixedSize then
        let sz := t.fixedByteSize
        if sz = 0 then .error .tooShort -- guard against pathological zero-size
        else
          let count := b.size / sz
          if count > cap then .error .outOfRange
          else if count * sz ≠ b.size then .error .trailingBytes
          else
            match SSZType.deserializeFixedElems t count b 0 sz with
            | .error e        => .error e
            | .ok (xs, used)  =>
                let arr := xs.toArray
                if h : arr.size ≤ cap then .ok (⟨arr, h⟩, used)
                else .error .outOfRange
      else
        -- Variable-size element list: count is recovered from the
        -- first offset (`firstOff / 4` = number of offsets). An
        -- empty list has zero bytes and zero elements.
        if b.size = 0 then
          .ok (⟨#[], by simp⟩, 0)
        else
          match readUInt32LE b 0 with
          | .none => .error .tooShort
          | .some firstOff =>
              let firstOffN := firstOff.toNat
              if firstOffN % BYTES_PER_LENGTH_OFFSET ≠ 0 then .error .invalidOffset
              else
                let count := firstOffN / BYTES_PER_LENGTH_OFFSET
                if count > cap then .error .outOfRange
                else
                  match extractCollOffsets b count 0 with
                  | .error e => .error e
                  | .ok offs =>
                      match SSZType.deserializeVarElems t offs b.size b with
                      | .error e => .error e
                      | .ok xs   =>
                          let arr := xs.toArray
                          if h : arr.size ≤ cap then .ok (⟨arr, h⟩, b.size)
                          else .error .outOfRange
  | .bitvector n, b => SizzLean.Spec.deserializeBitvector n b
  | .bitlist cap, b => SizzLean.Spec.deserializeBitlist cap b
  | .container fs, b =>
      if SSZType.allFixedSize fs then
        SSZType.deserializeFixedFields fs b 0
      else
        -- Variable-size container: pre-extract offsets, then decode
        -- each field using either prefix bytes (fixed-size fields)
        -- or offset-bounded slices (variable-size fields).
        let prefixSize := SSZType.fixedSectionSizeFields fs
        if b.size < prefixSize then .error .tooShort
        else
          match extractFieldOffsets b fs 0 with
          | .error e  => .error e
          | .ok offs  =>
              -- The first variable-field offset (if any) must equal
              -- the total prefix size, i.e. the variable body
              -- region starts right after the prefix.
              match offs.head? with
              | .some firstOff =>
                  if firstOff ≠ prefixSize then .error .invalidOffset
                  else
                    match SSZType.deserializeVarFields fs b 0 offs b.size with
                    | .error e => .error e
                    | .ok v    => .ok (v, b.size)
              | .none =>
                  -- No variable-size fields (degenerate case;
                  -- `allFixedSize` should have been true)
                  SSZType.deserializeFixedFields fs b 0
/-- Read `count` fixed-size elements of type `t`, each `elemSize`
bytes wide, from `b` starting at `off`. Recurses structurally on
`count : Nat`. The cross-call to `deserialize t` does not change
`t`, but each iteration's input buffer (extracted slice) is
strictly smaller, Lean's structural-recursion check on `count`
suffices for termination here.

The implementation threads an explicit accumulator (`acc`,
`accSz`, defaulted) so the recursive call sits in tail position;
the natural

```
match SSZType.deserializeFixedElems t k b (off + sz) sz with
| .ok (xs, total)  => .ok (x :: xs, sz + total)
```

spelling holds `x` and `sz` on the stack across each recursive
call, which overflows the OS-default 8 MB stack for
`Vector[uint8, 131072]` (the mainnet `BlobSidecar.blob` field,
131072 frames). The accumulator form is constant-stack; we
`List.reverse` the accumulator at the base case, which is itself
tail-recursive in Lean core. -/
def SSZType.deserializeFixedElems :
    (t : SSZType) → (count : Nat) → ByteArray → (off elemSize : Nat) →
    (acc : List t.interp := []) → (accSz : Nat := 0) →
    Except SSZError (List t.interp × Nat)
  | _, 0,     _, _,   _,  acc, accSz =>
      .ok (acc.reverse, accSz)
  | t, k + 1, b, off, sz, acc, accSz =>
      let chunk := b.extract off (off + sz)
      match SSZType.deserialize t chunk with
      | .error e        => .error e
      | .ok (x, used)   =>
          if used ≠ sz then .error .trailingBytes
          else
            SSZType.deserializeFixedElems t k b (off + sz) sz
              (x :: acc) (accSz + sz)

/-- Read each fixed-size container field in declaration order. The
result type is `interpFields fs`, definitionally a right-nested
`Prod` chain ending in `PUnit`. -/
def SSZType.deserializeFixedFields :
    (fs : List SSZType) → ByteArray → (off : Nat) →
    Except SSZError (SSZType.interpFields fs × Nat)
  | [],      _, _   => .ok (PUnit.unit, 0)
  | t :: ts, b, off =>
      let sz := t.fixedByteSize
      let chunk := b.extract off (off + sz)
      match SSZType.deserialize t chunk with
      | .error e        => .error e
      | .ok (x, used)   =>
          if used ≠ sz then .error .trailingBytes
          else
            match SSZType.deserializeFixedFields ts b (off + sz) with
            | .error e          => .error e
            | .ok (rest, total) => .ok ((x, rest), sz + total)

/-- Variable-size container field walker.

The mixed-field container decode path: `fs` walks alongside two
positions: `prefixOff` (the running position in the fixed-prefix
region) and `varOffs` (the still-unused tail of pre-extracted
variable-field offsets). For each field:

* If `t.isFixedSize`, decode from `prefixOff..prefixOff + t.fixedByteSize`,
  advance `prefixOff`.
* Otherwise, pop the head offset from `varOffs`; the field's body
  runs from that offset to the next offset (or `bufEnd` if this
  was the last variable field). Decode, advance `prefixOff` by
  `BYTES_PER_LENGTH_OFFSET`.

Structurally recursive on `fs`. -/
def SSZType.deserializeVarFields :
    (fs : List SSZType) → ByteArray → (prefixOff : Nat) →
    (varOffs : List Nat) → (bufEnd : Nat) →
    Except SSZError (SSZType.interpFields fs)
  | [],      _, _,        _,       _      => .ok PUnit.unit
  | t :: ts, b, prefixOff, varOffs, bufEnd =>
      if t.isFixedSize then
        let sz := t.fixedByteSize
        let chunk := b.extract prefixOff (prefixOff + sz)
        match SSZType.deserialize t chunk with
        | .error e        => .error e
        | .ok (x, used)   =>
            if used ≠ sz then .error .trailingBytes
            else
              match SSZType.deserializeVarFields ts b (prefixOff + sz) varOffs bufEnd with
              | .error e  => .error e
              | .ok rest  => .ok (x, rest)
      else
        match varOffs with
        | []                 => .error .invalidOffset
        | curOff :: restOffs =>
            let nextOff := restOffs.head?.getD bufEnd
            if curOff > nextOff || nextOff > bufEnd then .error .invalidOffset
            else
              let body := b.extract curOff nextOff
              match SSZType.deserialize t body with
              | .error e      => .error e
              | .ok (x, _)    =>
                  match SSZType.deserializeVarFields ts b
                      (prefixOff + BYTES_PER_LENGTH_OFFSET) restOffs bufEnd with
                  | .error e  => .error e
                  | .ok rest  => .ok (x, rest)

/-- Variable-size element collection walker.

Used by `.vector` / `.list` when the element type
`t` is variable-size. Given a pre-extracted list of body offsets
(one per element) plus the buffer end, decode each element from
its `offs[k]..offs[k+1]` slice (with `bufEnd` as the implicit
sentinel after the last offset).

Structurally recursive on `offs`. -/
def SSZType.deserializeVarElems :
    (t : SSZType) → (offs : List Nat) → (bufEnd : Nat) → ByteArray →
    Except SSZError (List t.interp)
  | _, [],              _,      _ => .ok []
  | t, curOff :: rest,  bufEnd, b =>
      let nextOff := rest.head?.getD bufEnd
      if curOff > nextOff || nextOff > bufEnd then .error .invalidOffset
      else
        let body := b.extract curOff nextOff
        match SSZType.deserialize t body with
        | .error e   => .error e
        | .ok (x, _) =>
            match SSZType.deserializeVarElems t rest bufEnd b with
            | .error e => .error e
            | .ok xs   => .ok (x :: xs)

end

/-! ### Round-trip examples: three concrete shapes.

Each `example` closes its own goal by `decide` /
`native_decide`, exercising both encoder and decoder end-to-end. -/

/-! ### Round-trip examples: wrapped through total `Bool`-returning
helpers so type-class synthesis sees concrete types (not the opaque
`s.interp` projections). Each helper extracts the round-tripped
payload as a known type and compares it against the original; the
`example` then closes by `native_decide` ("at least three small
concrete shapes round-trip
by `decide` or `native_decide`"). -/

/-- Round-trip a `Bool` through `.bool`; returns `true` iff the
recovered value and consumed-byte count match the input.

Wrapping the round-trip in a `Bool`-returning helper sidesteps a
typeclass-synthesis quirk: when stating
`SSZType.deserialize .bool (SSZType.serialize .bool x) = .ok (x, n)`
directly, Lean leaves `SSZType.interp .bool` un-reduced (the mutual
`interp` block isn't `@[reducible]`), so it can't find a `Decidable`
instance for the equation. Reducing the round-trip to a concrete
`Bool` here lets `native_decide` see ordinary `Bool` arithmetic. -/
private def roundTripBool (x : Bool) : Bool :=
  match SSZType.deserialize .bool (SSZType.serialize .bool x) with
  | .ok (y, n) =>
      -- `y : SSZType.interp .bool` from the `.ok (y, n)` destructure
      -- (the result type of `deserialize .bool _` is
      -- `Except SSZError (SSZType.interp .bool × Nat)`). The `let yb`
      -- triggers the same defeq reduction trick used in `Serialize.lean`,
      -- without it, `decide (y = x)` can't synthesise `DecidableEq`
      -- because `interp .bool` stays opaque to typeclass search.
      let yb : Bool := y
      decide (yb = x) && decide (n = (SSZType.serialize .bool x).size)
  | .error _   => false

/-- Round-trip a `UInt32` through `.uintN 32`. -/
private def roundTripUInt32 (x : UInt32) : Bool :=
  match SSZType.deserialize (.uintN 32) (SSZType.serialize (.uintN 32) x) with
  | .ok (y, n) =>
      let yu : UInt32 := y -- same defeq-coercion idiom; see roundTripBool
      decide (yu = x) && decide (n = (SSZType.serialize (.uintN 32) x).size)
  | .error _   => false

/-- Round-trip a `Vector Bool 3` through `.vector .bool 3`. -/
private def roundTripVecBool3 (v : Vector Bool 3) : Bool :=
  match SSZType.deserialize (.vector .bool 3) (SSZType.serialize (.vector .bool 3) v) with
  | .ok (y, n) =>
      let yv : Vector Bool 3 := y -- same defeq-coercion idiom
      decide (yv = v) && decide (n = (SSZType.serialize (.vector .bool 3) v).size)
  | .error _   => false

/-- Round-trip `.bool` with `true`. -/
example : roundTripBool true = true := by native_decide

/-- Round-trip `.uintN 32` with `42 : UInt32`. -/
example : roundTripUInt32 42 = true := by native_decide

/-- Round-trip `.vector .bool 3` with `#v[true, false, true]`. -/
example : roundTripVecBool3 #v[true, false, true] = true := by native_decide

/-! ### Round-trip examples for the wide-integer and variable-size paths

The `uintN 128 / 256` integer arms, variable-size containers, and
variable-size element lists each get a closed-form `native_decide`
round-trip. A bug in the corresponding encoder/decoder would
surface here at build time. -/

/-- Round-trip `BitVec 256` through `.uintN 256`. Used by
`ExecutionPayload.base_fee_per_gas` (Bellatrix+). -/
private def roundTripUInt256 (x : BitVec 256) : Bool :=
  match SSZType.deserialize (.uintN 256) (SSZType.serialize (.uintN 256) x) with
  | .ok (y, n) =>
      let yb : BitVec 256 := y
      decide (yb = x) && decide (n = (SSZType.serialize (.uintN 256) x).size)
  | .error _   => false

example : roundTripUInt256 (BitVec.ofNat 256 0x1234) = true := by native_decide
example : roundTripUInt256 (BitVec.ofNat 256 0) = true := by native_decide

/-- Round-trip a variable-size container `[bool, list bool 8, uintN 32]`.
The middle field is variable-size (a `.list .bool cap`), exercising the
offset-table path. -/
private def roundTripVarContainer
    (a : Bool) (bs : { xs : Array Bool // xs.size ≤ 8 }) (c : UInt32) : Bool :=
  let s : SSZType := .container [.bool, .list .bool 8, .uintN 32]
  let v : SSZType.interpFields [.bool, .list .bool 8, .uintN 32] :=
    (a, bs, c, PUnit.unit)
  match SSZType.deserialize s (SSZType.serialize s v) with
  | .ok (y, n) =>
      let yv : SSZType.interpFields [.bool, .list .bool 8, .uintN 32] := y
      decide (yv.1 = a) && decide (yv.2.1.val = bs.val) && decide (yv.2.2.1 = c) &&
        decide (n = (SSZType.serialize s v).size)
  | .error _   => false

example : roundTripVarContainer true ⟨#[true, false, true], by decide⟩ 0xDEADBEEF = true := by
  native_decide
example : roundTripVarContainer false ⟨#[], by decide⟩ 0 = true := by native_decide

end SizzLean.Spec
