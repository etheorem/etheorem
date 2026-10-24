/-!
# `EthCLLib.TheoremVectors.Snappy`: the snappy block-format writer

The `.ssz_snappy` parts of the upstream pyspec case layout hold the
snappy block-format compression of a part's SSZ bytes
(`THEOREM_VECTORS_ARCHITECTURE.md` §13.7). That section's suffix rule is
`.ssz_snappy` preferred, a raw `.ssz` beside it accepted. The mirror
tasks of this stage write the compressed form and call this module, the
one snappy writer in the tree. Snappy stays out of Lean's SSZ; the
format code owns the encoding, the way it owns the YAML grammar.

The writer emits the all-literals encoding alone: one varint preamble,
then one literal element that carries the whole input. It does no match
finding, no chunk splitting, and it emits no copy elements. The form is
valid for every decoder of the block format. The task sets no ratio
goal.

The reference decoder is `github.com/golang/snappy`'s `Decode` on a
block (`decode_other.go`, `decode.go`), the authority the output must
satisfy, and `cramjam.snappy.decompress_raw` accepts the same form. The
rules, in that decoder's terms:

- the preamble is the uncompressed length as a base-128 varint: 7 data
  bits per byte, low group first, the high bit as the continuation
  mark. The decoder reads 5 bytes at most and rejects lengths above
  `0xffffffff`, so a caller keeps the input below that bound;
- a literal element opens with a tag byte whose low 2 bits are `00`.
  For `n - 1 < 60` the tag's high 6 bits carry `n - 1`. From 61 bytes
  on, the tag is `(59 + k) << 2` for the least `k` in 1..4 that holds
  `n - 1`, and `k` little-endian bytes follow with that value;
- the empty input encodes as the preamble `0x00` alone, with no
  element. The decoder's element loop never runs, and the decoded
  length 0 matches.

## Lean idioms annotated

- `uvarint` recurses on `n / 128`, a subterm structural recursion
  cannot see, so it carries `termination_by n`; `omega` closes the
  goal, and it reads a division by a literal.
-/

set_option autoImplicit false

namespace EthCLLib.TheoremVectors

/-- The base-128 varint of `n`, least significant group first, in the
layout of Go's `binary.Uvarint`. The value is the block's uncompressed
length. Any length below `2^32` fits in 5 bytes, and the decoder
rejects a length above `0xffffffff`. -/
private def uvarint (n : Nat) : ByteArray :=
  if n < 128 then
    ByteArray.mk #[UInt8.ofNat n]
  else
    ByteArray.mk #[0x80 + UInt8.ofNat (n % 128)] ++ uvarint (n / 128)
termination_by n
decreasing_by omega

/-- The `k` little-endian bytes of `m`, least significant byte first. -/
private def leBytes (m : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | k + 1 => ByteArray.mk #[UInt8.ofNat (m % 256)] ++ leBytes (m / 256) k

/-- The least count in 1..4 of bytes that holds `m`, for a literal
length above 60. The tag byte names this count. -/
private def extraBytes (m : Nat) : Nat :=
  if m < 256 then 1
  else if m < 65536 then 2
  else if m < 16777216 then 3
  else 4

/-- The head of the one literal element for `n` literal bytes, `n` at
least 1: the tag byte, then the extra length bytes a length above 60
spends. -/
private def literalHead (n : Nat) : ByteArray :=
  if n ≤ 60 then
    ByteArray.mk #[UInt8.ofNat ((n - 1) * 4)]
  else
    let m := n - 1
    let k := extraBytes m
    ByteArray.mk #[UInt8.ofNat ((59 + k) * 4)] ++ leBytes m k

/-- The snappy block-format encoding of `src`, all-literals form: the
varint preamble for the size, then one literal element carrying the
whole input. The empty input encodes as the single byte `0x00`. A
caller keeps the size below `2^32`, the length bound the reference
decoder accepts. -/
def Snappy.encode (src : ByteArray) : ByteArray :=
  let n := src.size
  if n == 0 then
    ByteArray.mk #[0x00]
  else
    uvarint n ++ literalHead n ++ src

/-! ## Pins -/

/-- `n` bytes of `0x41`, the constant fill the length-boundary pins use. -/
private def fill41 (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n 0x41)

/-- A mixed-byte input, the shape the constant fills do not cover. -/
private def mixed : ByteArray :=
  ByteArray.mk #[0xde, 0xad, 0xbe, 0xef, 0x00, 0xff, 0x01, 0x80]

-- the empty input: the preamble alone, no element
#guard Snappy.encode ByteArray.empty == ByteArray.mk #[0x00]

-- one byte, the smallest literal
#guard Snappy.encode (fill41 1) == (ByteArray.mk #[0x01, 0x00]).append (fill41 1)

-- a length below 60: the short tag carries `n - 1` directly (`4 << 2 = 0x10`)
#guard Snappy.encode (fill41 5) == (ByteArray.mk #[0x05, 0x10]).append (fill41 5)

-- exactly 60: the last length the short tag holds (`59 << 2 = 0xec`)
#guard Snappy.encode (fill41 60) == (ByteArray.mk #[0x3c, 0xec]).append (fill41 60)

-- exactly 61: the first 1-extra-byte length (`60 << 2 = 0xf0`, `60` LE)
#guard Snappy.encode (fill41 61) == (ByteArray.mk #[0x3d, 0xf0, 0x3c]).append (fill41 61)

-- 300: a two-byte preamble and a 2-extra-byte literal (`61 << 2 = 0xf4`, `299` LE)
#guard Snappy.encode (fill41 300) ==
  (ByteArray.mk #[0xac, 0x02, 0xf4, 0x2b, 0x01]).append (fill41 300)

-- mixed bytes under the short tag, the tail equal to the input itself
#guard Snappy.encode mixed == (ByteArray.mk #[0x08, 0x1c]).append mixed

-- the 3- and 4-extra-byte literal heads, pinned at the head so the
-- pins stay free of multi-megabyte inputs
#guard literalHead 16777216 == ByteArray.mk #[0xf8, 0xff, 0xff, 0xff]
#guard literalHead 16777217 == ByteArray.mk #[0xfc, 0x00, 0x00, 0x00, 0x01]

-- the format description's own worked example: 2097150 = 0x1ffffe
#guard uvarint 2097150 == ByteArray.mk #[0xfe, 0xff, 0x7f]
-- the 5-byte preamble regime, head-only so the pin stays small
#guard uvarint 268435456 == ByteArray.mk #[0x80, 0x80, 0x80, 0x80, 0x01]

end EthCLLib.TheoremVectors
