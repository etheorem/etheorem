import LeanRlp.Spec.Decode
import LeanRlp.Spec.Encode
import LeanRlp.Spec.Item

/-!
# `LeanRlpTests.Known`: known-answer gates (PLAN.md Stage 1)

Five sections: the encode examples of the RLP specification, the
decode and round-trip examples, the five item-layer non-canonical
inputs of ARCHITECTURE.md §7 with their `DecodeError`
constructors and the structural rejections (`truncated`,
`listOverrun`, `trailingBytes`, `tooDeep`), the long forms and the
limits, and the tail-call gate. The gates run under `decide`; six
of them use `native_decide`: the five whose kernel evaluation
exceeds its heartbeat budget (the 1024-byte string gate, the
300-byte string gate, the two-length-byte list header gate, and
the two depth gates at the default bound), and the tail-call gate,
which exercises the decoder in compiled form on a flat list of
10^6 elements. That is the documented fallback of
ARCHITECTURE.md §10.

The scalar-layer row of the §7 table is a Stage 4 gate, with its own
`SchemaError`.

Build with `lake build LeanRlpTests` or `just rlp-test`.
-/

set_option autoImplicit false

namespace LeanRlpTests

open LeanRlp.Spec

/-- The byte array of a literal byte list. -/
def bytes (xs : List UInt8) : ByteArray := xs.toByteArray

/-- The specification's 56-character example string. It takes the
long form with a one-byte length field. -/
def lorem : String :=
  "Lorem ipsum dolor sit amet, consectetur adipisicing elit"

/-- `nestItem n` is `n + 1` nested one-element lists, ending in the
empty list. Each list's header grows with its payload, so the
encoding is `c(n) c(n-1) … c1 c0`, `n + 1` bytes while the payloads
stay below 56. The depth gates encode it with the `Spec` encoder. -/
def nestItem : Nat → Item
  | 0 => .list []
  | n + 1 => .list [nestItem n]

/-! ## The RLP specification's examples: encode -/

-- The empty string takes the short string header.
example : encode (.bytes (bytes [])) = bytes [0x80] := by decide

-- The byte `0x00` is below `0x80`, so it encodes as itself. The
-- scalar reading of `0x00`, the empty string, is a Stage 4 concern.
example : encode (.bytes (bytes [0x00])) = bytes [0x00] := by decide

-- Bytes below `0x80` encode as themselves.
example : encode (.bytes (bytes [0x0f])) = bytes [0x0f] := by decide
example : encode (.bytes (bytes [0x7f])) = bytes [0x7f] := by decide

-- A byte from `0x80` on needs the string header.
example : encode (.bytes (bytes [0x80])) = bytes [0x81, 0x80] := by decide

-- "dog"
example : encode (.bytes (bytes [0x64, 0x6f, 0x67])) =
    bytes [0x83, 0x64, 0x6f, 0x67] := by decide

-- ["cat", "dog"]
example : encode (.list [.bytes (bytes [0x63, 0x61, 0x74]),
    .bytes (bytes [0x64, 0x6f, 0x67])]) =
    bytes [0xc8, 0x83, 0x63, 0x61, 0x74, 0x83, 0x64, 0x6f, 0x67] := by decide

-- The empty list.
example : encode (.list []) = bytes [0xc0] := by decide

-- The integer 1024 is the two-byte string `04 00`.
example : encode (.bytes (bytes [0x04, 0x00])) =
    bytes [0x82, 0x04, 0x00] := by decide

-- The nested list of the specification:
-- [ [], [[]], [ [], [[]] ] ].
example : encode (.list [.list [], .list [.list []],
    .list [.list [], .list [.list []]]]) =
    bytes [0xc7, 0xc0, 0xc1, 0xc0, 0xc3, 0xc0, 0xc1, 0xc0] := by decide

-- The 56-character string: long form, one length byte (`b8 38`).
example : encode (.bytes lorem.toByteArray) =
    bytes [0xb8, 0x38] ++ lorem.toByteArray := by decide

-- A 1024-byte string: long form, two length bytes (`b9 04 00`).
example : encode (.bytes (List.toByteArray (List.replicate 1024 0x61))) =
    bytes [0xb9, 0x04, 0x00] ++ List.toByteArray (List.replicate 1024 0x61) := by
  native_decide

/-! ## The RLP specification's examples: decode -/

example : decode (bytes [0x80]) = .ok (.bytes (bytes [])) := by decide
example : decode (bytes [0x00]) = .ok (.bytes (bytes [0x00])) := by decide
example : decode (bytes [0x0f]) = .ok (.bytes (bytes [0x0f])) := by decide
example : decode (bytes [0x83, 0x64, 0x6f, 0x67]) =
    .ok (.bytes (bytes [0x64, 0x6f, 0x67])) := by decide
example : decode (bytes [0xc0]) = .ok (.list []) := by decide
example : decode (bytes [0xc8, 0x83, 0x63, 0x61, 0x74, 0x83, 0x64, 0x6f, 0x67]) =
    .ok (.list [.bytes (bytes [0x63, 0x61, 0x74]),
      .bytes (bytes [0x64, 0x6f, 0x67])]) := by decide
example : decode (bytes [0xc7, 0xc0, 0xc1, 0xc0, 0xc3, 0xc0, 0xc1, 0xc0]) =
    .ok (.list [.list [], .list [.list []],
      .list [.list [], .list [.list []]]]) := by decide

-- Round trips, decided with the hand-written `DecidableEq Item`.
example : decode (encode (.list [.bytes (bytes [0x63, 0x61, 0x74]),
    .bytes (bytes [0x64, 0x6f, 0x67])])) =
    .ok (.list [.bytes (bytes [0x63, 0x61, 0x74]),
      .bytes (bytes [0x64, 0x6f, 0x67])]) := by decide
example : decode (encode (nestItem 3)) = .ok (nestItem 3) := by decide
example : decode (encode (.bytes lorem.toByteArray)) =
    .ok (.bytes lorem.toByteArray) := by decide

-- `decodePrefix` reports where the item ended, so a shorter input is
-- fine; `decode` wants all of it.
example : decodePrefix (bytes [0x83, 0x64, 0x6f, 0x67, 0x80]) 0 =
    .ok (.bytes (bytes [0x64, 0x6f, 0x67]), 4) := by decide
example : decode (bytes [0x83, 0x64, 0x6f, 0x67, 0x80]) =
    .error (.trailingBytes 4) := by decide

/-! ## The non-canonical inputs of ARCHITECTURE.md §7 -/

-- One byte below `0x80` behind a string header.
example : decode (bytes [0x81, 0x05]) = .error (.nonCanonicalByte 0) := by decide

-- Long form for a 1-byte string.
example : decode (bytes [0xb8, 0x01, 0x05]) =
    .error (.nonCanonicalLength 0) := by decide

-- Long form for a 1-byte list payload.
example : decode (bytes [0xf8, 0x01, 0x05]) =
    .error (.nonCanonicalLength 0) := by decide

-- Long form with zero length: the leading zero fires first.
example : decode (bytes [0xb8, 0x00]) =
    .error (.nonCanonicalLength 0) := by decide

-- Leading zero in a long-form length: the length field `00 38`
-- declares two bytes for 56. The check fires before any payload is
-- read. A two-byte length field can only reach the `len ≤ 55`
-- branch with a leading zero, so this gate covers that branch too.
example : decode (bytes [0xb9, 0x00, 0x38]) =
    .error (.nonCanonicalLength 0) := by decide

-- The input ends inside the length field, so the cut-off check
-- runs first: both gates expect `truncated`, and the leading-zero
-- check never runs.
example : decode (bytes [0xb9, 0x01]) = .error (.truncated 0) := by decide
example : decode (bytes [0xb9, 0x00]) = .error (.truncated 0) := by decide

-- The empty input ends inside the first header.
example : decode (bytes []) = .error (.truncated 0) := by decide

-- A string header that promises more bytes than the input has.
example : decode (bytes [0x83, 0x64]) = .error (.truncated 0) := by decide

-- A long-form string header whose payload crosses the input end.
-- `b9` declares two length bytes; `02 01` reads 513.
example : decode (bytes [0xb9, 0x02, 0x01, 0x61]) =
    .error (.truncated 0) := by decide

-- Input left over after a whole item.
example : decode (bytes [0x80, 0x80]) = .error (.trailingBytes 1) := by decide

-- An element whose header promises more than the input holds
-- reports `truncated`; a crossing element reports `listOverrun`.
-- Recorded in ARCHITECTURE.md §2.1.
example : decode (bytes [0xc1, 0x88]) = .error (.truncated 1) := by decide

-- A crossing element can also report a reason from inside
-- itself: the loop decodes it in full before the comparison
-- (ARCHITECTURE.md §2.1).
example : decode (bytes [0xc1, 0x81, 0x05]) =
    .error (.nonCanonicalByte 1) := by decide

-- A list of one element that crosses the list payload's end: the
-- element header promises 8 bytes, the list payload allows 1.
example : decode (bytes ([0xc1, 0x88] ++ List.replicate 8 0x01)) =
    .error (.listOverrun 1) := by decide

-- A nest of 6 lists against a bound of 4: `tooDeep` fires at the
-- fifth list header, the first one decoded with no budget left (the
-- headers grow with their payloads, so the fifth sits at offset 4).
example : decode (encode (nestItem 5)) 4 = .error (.tooDeep 4) := by decide

-- The default bound of 1024 accepts a nest of exactly 1024 lists.
example : decode (encode (nestItem 1023)) = .ok (nestItem 1023) := by
  native_decide

-- The default bound rejects a nest of 1025 lists at the innermost
-- header.
example : decode (encode (nestItem 1024)) = .error (.tooDeep 2862) := by
  native_decide

-- A budget of zero rejects even the empty list, the only list that
-- starts no recursion.
example : decode (bytes [0xc0]) 0 = .error (.tooDeep 0) := by decide

/-! ## The long forms and the limits -/

-- The size function agrees with the encoder at the short-form
-- limit, and on a nested list.
example : (encode (.list (List.replicate 55 (.bytes (bytes [0x7f]))))).size =
    (Item.list (List.replicate 55 (Item.bytes (bytes [0x7f])))).encodedSize := by
  decide
example : (encode (.list (List.replicate 56 (.bytes (bytes [0x7f]))))).size =
    (Item.list (List.replicate 56 (Item.bytes (bytes [0x7f])))).encodedSize := by
  decide
example : (encode (nestItem 3)).size = (nestItem 3).encodedSize := by decide

-- A long-form list: 60 one-byte strings, payload 60, header
-- `f8 3c`.
example : decode (bytes ([0xf8, 0x3c] ++ List.replicate 60 0x01)) =
    .ok (.list (List.replicate 60 (.bytes (bytes [0x01])))) := by decide

-- A long-form string with two length bytes: a 300-byte string,
-- `b9 01 2c`. The 302-byte comparison exceeds the kernel's
-- heartbeat budget, so this gate runs on the compiler.
example : decode (bytes ([0xb9, 0x01, 0x2c] ++ List.replicate 300 0x61)) =
    .ok (.bytes (bytes (List.replicate 300 0x61))) := by native_decide

-- A long-form list with a leading zero length byte, the list twin
-- of `b9 00 38`.
example : decode (bytes [0xf9, 0x00, 0x38]) =
    .error (.nonCanonicalLength 0) := by decide

-- The encoder writes the long-form list header over a payload of
-- 60 bytes.
example : encode (.list (List.replicate 60 (.bytes (bytes [0x7f])))) =
    bytes ([0xf8, 0x3c] ++ List.replicate 60 0x7f) := by decide

-- The accept side of the single-byte check: `0x81 0x80` is the
-- canonical encoding of the one-byte string `80`.
example : decode (bytes [0x81, 0x80]) = .ok (.bytes (bytes [0x80])) := by
  decide

-- A long-form list header whose length field is cut off by the
-- input end: `fa` declares three length bytes, only two follow.
example : decode (bytes [0xfa, 0x01, 0x02, 0x61]) =
    .error (.truncated 0) := by decide

-- The short-form limit on encode: a payload of 55 bytes takes the
-- short header `f7`, a payload of 56 the long header `f8 38`.
example : encode (.list (List.replicate 55 (.bytes (bytes [0x7f])))) =
    bytes ([0xf7] ++ List.replicate 55 0x7f) := by decide
example : encode (.list (List.replicate 56 (.bytes (bytes [0x7f])))) =
    bytes ([0xf8, 0x38] ++ List.replicate 56 0x7f) := by decide

-- The single-byte check inside a list: the offending header byte
-- sits at offset 1.
example : decode (bytes [0xc2, 0x81, 0x05]) =
    .error (.nonCanonicalByte 1) := by decide

-- `decodePrefix` takes the caller's depth budget: a nest of 4
-- lists against a budget of 2 fails at the third header.
example : decodePrefix (encode (nestItem 3)) 0 2 = .error (.tooDeep 2) := by
  decide

-- The encoder writes the two-length-byte list header `f9 01 00`
-- over a payload of 256 bytes.
example : encode (.list (List.replicate 256 (.bytes (bytes [0x7f])))) =
    bytes ([0xf9, 0x01, 0x00] ++ List.replicate 256 0x7f) := by
  native_decide

-- A short-list header whose payload runs past the input end.
example : decode (bytes [0xc3, 0x01]) = .error (.truncated 0) := by decide

-- An element inside a list whose header runs past the input end.
example : decode (bytes [0xc2, 0x83, 0x01, 0x01]) =
    .error (.truncated 1) := by decide

-- A crossing element that is itself a list.
example : decode (bytes [0xc1, 0xc2, 0x01, 0x01]) =
    .error (.listOverrun 1) := by decide

-- The short-string limit: 55 bytes take the header `b7`.
example : decode (bytes ([0xb7] ++ List.replicate 55 0x61)) =
    .ok (.bytes (bytes (List.replicate 55 0x61))) := by decide

-- The exact length limit: `b8 37` declares a payload of 55 bytes,
-- the largest length the short form must carry. The 55 bytes
-- follow, so only the length check fires.
example : decode (bytes ([0xb8, 0x37] ++ List.replicate 55 0x61)) =
    .error (.nonCanonicalLength 0) := by decide

-- The list twin: `f8 37` declares a 55-byte list payload, and the
-- 55 bytes follow.
example : decode (bytes ([0xf8, 0x37] ++ List.replicate 55 0x61)) =
    .error (.nonCanonicalLength 0) := by decide

-- An eight-byte length field naming a payload no input could
-- hold: the widest long form, and the case where a fixed-width
-- length would overflow.
example : decode (bytes ([0xbf] ++ List.replicate 8 0xff)) =
    .error (.truncated 0) := by decide

-- `decodePrefix` past the input end reports the offset.
example : decodePrefix (bytes [0x80]) 5 = .error (.truncated 5) := by
  decide

-- The second element of a list crosses the payload end, so
-- `listOverrun` fires at a cursor past the first element.
example : decode (bytes ([0xc3, 0x01, 0x88] ++ List.replicate 8 0x01)) =
    .error (.listOverrun 2) := by decide

-- `decodePrefix` at a nonzero offset parses the suffix.
example : decodePrefix (bytes [0x80, 0x83, 0x64, 0x6f, 0x67]) 1 =
    .ok (.bytes (bytes [0x64, 0x6f, 0x67]), 5) := by decide

/-! ## The tail-call gate

The element loop of `Spec.Decode`'s `decodeListElemsAux` is
tail-recursive on its accumulator, so a long flat list costs no
stack frame per element. The kernel never runs the loop, so a
`decide` gate cannot reach it. `native_decide` evaluates the
compiled decoder, where a self call that kept a frame per element
overflows at 10^6. The gate fails if a toolchain change ever
gives the loop a frame per element.

The checker below is tail-recursive too, so the comparison adds
no stack of its own. `DecidableEq Item` stays out of this gate:
its list comparison recurses in a non-tail call, so an item
equation at this scale overflows on its own. The smaller gates own
the item equations.

A payload of 10^6 bytes takes the widest three-byte length field:
header `fa 0f 42 40`, then 10^6 `01` bytes.
-/

/-- The gate's checker: every element is the one-byte string `01`,
and there are exactly `n` of them. Tail-recursive on the count,
like the loop it checks. -/
def flatOnes : List Item → Nat → Bool
  | [], 0 => true
  | Item.bytes b :: ts, n + 1 => b.size == 1 && b[0]! == 0x01 && flatOnes ts n
  | _, _ => false

example : (match decode (bytes ([0xfa, 0x0f, 0x42, 0x40] ++
      List.replicate 1000000 0x01)) with
    | .ok (.list xs) => flatOnes xs 1000000
    | _ => false) = true := by
  native_decide

end LeanRlpTests
