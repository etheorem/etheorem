import LeanRlp.Spec.Item
import LeanRlp.Spec.Scalar

/-!
# `LeanRlp.Spec.Encode`: the RLP encoder

The encoder is total and returns a plain `ByteArray` (ARCHITECTURE.md
§2.1). It recurses over an `Item` tree: a byte string below 0x80
encodes as itself, a longer one gets a string header, and a list
gets a list header over the concatenation of its items.

`encodeHeader` writes the header for a payload of `len` bytes. The
short form is one byte in `[base, base + 55]`; the long form is
`base + 55` followed by the minimal big-endian length, which is what
`Spec.Scalar` supplies. One definition serves strings and lists.
The length of a list header is `Item.encodedSizeList`, so the size
function of `Spec.Item` is the encoder's only source of byte counts.

The encoder assumes every payload is below 2^64 bytes and
performs no run-time check (ARCHITECTURE.md §2.1). The round-trip
theorems of PLAN.md Stage 3 take `Item.Encodable` as a hypothesis.

`encodeListOf` recurses once per list element and appends onto the
fresh item encoding, so a flat list of millions of elements costs
one native stack frame per element and quadratic byte copies. The
`.list` arm reads `encodedSizeList` at every nesting level, so size
computation is depth times size. Real execution-layer lists hold
hundreds of elements, and PLAN.md Stage 7 owns the performance
work. The decoder's element loop is tail-recursive and carries no
such exposure.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

/-- The header for a payload of `len` bytes. `base` is `0x80` for
string headers and `0xc0` for list headers. The short form is one
byte in `[base, base + 55]`; the long form is `base + 55` followed
by the minimal big-endian length. -/
def encodeHeader (base : UInt8) (len : Nat) : ByteArray :=
  if len ≤ 55 then
    ByteArray.empty.push (UInt8.ofNat (base.toNat + len))
  else
    ByteArray.empty.push (UInt8.ofNat (base.toNat + 55 + lenOfLen len)) ++
      minimalBE len

/-- A byte string below `0x80` encodes as itself; any other string
gets a string header over its bytes. -/
def encodeBytes (b : ByteArray) : ByteArray :=
  if isSingleLowByte b then b else encodeHeader 0x80 b.size ++ b

mutual
/-- The RLP encoding of an item (ARCHITECTURE.md §2.1). Total. -/
def encode : Item → ByteArray
  | .bytes b => encodeBytes b
  | .list items =>
    encodeHeader 0xc0 (encodedSizeList items) ++ encodeListOf items

/-- The encodings of a list's items, concatenated: the list
payload. -/
def encodeListOf : List Item → ByteArray
  | [] => ByteArray.empty
  | t :: ts => encode t ++ encodeListOf ts
end

end LeanRlp.Spec
