import LeanRlp.Spec.Error
import LeanRlp.Spec.Item
import LeanRlp.Spec.Scalar

/-!
# `LeanRlp.Spec.Decode`: the RLP decoder

One total, strict decoder (ARCHITECTURE.md §2.1). `decodeHeader`
reads the header byte itself, makes every canonical check, and
reports the kind and the payload span as a `Header`. `decode`
parses a whole input. `decodePrefix` parses one item and reports
where it ended.

The mutual recursion under them is the pair `decodeItem` and
`decodeListElemsAux`: the item node and the list-element loop. The
element loop is tail-recursive on an accumulator, so a long flat
list costs no native stack frame per element;
`LeanRlpTests.Known` gates the claim at 10^6 elements. The
nesting of `decodeItem` stays the only stack exposure, bounded by
the depth budget.

Termination is structural on a fuel argument: each item node and
each list element uses one unit. The theorems about the decoder
live in `Proofs/Fuel.lean`, so this file holds definitions only.
There,
`decode_fuelSufficient` certifies the fuel the public entry points
pass, so `outOfFuel` is a dead branch for them
(`decode_not_outOfFuel`, `decodePrefix_not_outOfFuel`).
The decoder also carries a depth bound: a nest deeper than the bound
fails with `tooDeep`, before it can exhaust the native stack. The
default bound is `defaultMaxDepth`, 1024, recorded as a discrepancy
against the reference oracle, which carries no limit
(ARCHITECTURE.md §2.1).

PLAN.md Stage 3 proves strictness:
`decode b = .ok t → encode t = b` (ARCHITECTURE.md §5), so every
decoded item will be canonical, at every entry point, at no
run-time cost.

ARCHITECTURE.md §7 lists the non-canonical inputs. The five
item-layer rows are Stage 1 gates, each expected to fail with its
`DecodeError` constructor.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

/-- The decoder's default depth bound. Execution-layer structures
nest a handful of levels and the fixtures sit far below it, so the
bound is no practical restriction. The reference oracle carries no limit, so
the bound is a recorded discrepancy (ARCHITECTURE.md §2.1). -/
def defaultMaxDepth : Nat := 1024

/-- The fuel the public entry points pass for a decode at `offset`:
two units per remaining input byte, plus two. Each item node and
each list element spends one unit, and every decoded item covers at
least one input byte (`decodeItem_end_gt` in `Proofs/Fuel.lean`),
so two units per byte suffice. The slack keeps the degenerate
one-call cases out of the zero-fuel branch
(`decode_fuelSufficient`). -/
def fuelFor (input : ByteArray) (offset : Nat) : Nat :=
  2 * (input.size - offset) + 2

/-- What `decodeHeader` read: the item's kind and its payload span.
A byte below `0x80` is a whole item, and `byte` carries it. A
header result always names a payload fully inside the input
(`decodeHeader_ok_bytes`, `decodeHeader_ok_list` in
`Proofs/Fuel.lean`). -/
inductive Header where
  | byte (v : UInt8)
  | bytes (start len : Nat)
  | list (start len : Nat)
  deriving DecidableEq, Repr

/-- Read a long-form header of `llen` length bytes at `offset`, and
make every canonical check: a leading zero byte and a length of 55
or below are `nonCanonicalLength`. `mk` wraps the payload span into
the header kind: `Header.bytes` for a string, `Header.list` for a
list. The result names a payload that is bounds-checked against the
input. -/
-- The length is read inline at each use: a `let` here would force
-- the proofs through zeta-reduction, which has no stable simp-only
-- name on this toolchain. The reads are at most eight bytes.
def decodeLongHeader (input : ByteArray) (offset llen : Nat)
    (mk : Nat → Nat → Header) : Except DecodeError Header :=
  if input.size < offset + 1 + llen then
    .error (.truncated offset)
  else if input[offset + 1]! = 0 ∨ beNat input (offset + 1) llen ≤ 55 then
    .error (.nonCanonicalLength offset)
  else if input.size < offset + 1 + llen + beNat input (offset + 1) llen then
    .error (.truncated offset)
  else
    .ok (mk (offset + 1 + llen) (beNat input (offset + 1) llen))

/-- Read the header or single-byte form at `offset`, and make every
canonical check (ARCHITECTURE.md §2.1). An `offset` past the input
end is `truncated`. -/
-- The header byte is read inline at each use, for the same
-- proof reason as the length reads of `decodeLongHeader`.
def decodeHeader (input : ByteArray) (offset : Nat) :
    Except DecodeError Header :=
  if input.size ≤ offset then
    .error (.truncated offset)
  else if input[offset]! < 0x80 then
    -- single-byte form: the item is its own payload
    .ok (.byte input[offset]!)
  else if input[offset]! ≤ 0xb7 then
    -- short string, 0x80..0xb7: the length is in the header byte
    if input.size < offset + 1 + (input[offset]!.toNat - 0x80) then
      .error (.truncated offset)
    else if input[offset]!.toNat - 0x80 == 1 && input[offset + 1]! < 0x80 then
      .error (.nonCanonicalByte offset)
    else
      .ok (.bytes (offset + 1) (input[offset]!.toNat - 0x80))
  else if input[offset]! ≤ 0xbf then
    -- long string, 0xb8..0xbf: the length takes 1..8 bytes
    decodeLongHeader input offset (input[offset]!.toNat - 0xb7) Header.bytes
  else if input[offset]! ≤ 0xf7 then
    -- short list, 0xc0..0xf7: the length is in the header byte
    if input.size < offset + 1 + (input[offset]!.toNat - 0xc0) then
      .error (.truncated offset)
    else
      .ok (.list (offset + 1) (input[offset]!.toNat - 0xc0))
  else
    -- long list, 0xf8..0xff: the length takes 1..8 bytes
    decodeLongHeader input offset (input[offset]!.toNat - 0xf7) Header.list

mutual
/-- Decode one item at `offset`. `fuel` counts down: one unit per
item node and one per list element. `depth` is the nesting budget
left: decoding a list spends one, and a list at budget zero is
`tooDeep`, before the recursion can exhaust the native stack
(ARCHITECTURE.md §2.1). The recursion is forced structural on the
fuel, so the kernel can reduce it: without the hint, the equation
compiler rejects the structural form over the depth subtraction
and picks well-founded recursion, which the kernel cannot
evaluate. -/
def decodeItem (input : ByteArray) (offset fuel depth : Nat) :
    Except DecodeError (Item × Nat) :=
  match fuel with
  | 0 => .error (.outOfFuel offset)
  | fuel + 1 =>
    match decodeHeader input offset with
    | .error e => .error e
    | .ok (.byte v) => .ok (.bytes (ByteArray.empty.push v), offset + 1)
    | .ok (.bytes start len) =>
      .ok (.bytes (input.extract start (start + len)), start + len)
    | .ok (.list start len) =>
      if depth = 0 then
        .error (.tooDeep offset)
      else
        match decodeListElemsAux input start (start + len) fuel (depth - 1) [] with
        | .error e => .error e
        | .ok items => .ok (.list items, start + len)
termination_by structural fuel

/-- The element loop of `decodeItem`, tail-recursive on an
accumulator. One fuel unit per element. An element that crosses
`stop` is `listOverrun`, and the decoder notices only after the
element decodes in full. The fuel bounds the number of element
decodes, and the input size bounds each read. The accumulator
keeps the compiled loop a tail call, so a long flat list costs no
native stack frame per element, and the nesting of `decodeItem`
stays bounded by the depth budget. -/
def decodeListElemsAux (input : ByteArray) (cursor stop fuel depth : Nat)
    (acc : List Item) : Except DecodeError (List Item) :=
  match fuel with
  | 0 => if stop ≤ cursor then .ok acc.reverse else .error (.outOfFuel cursor)
  | fuel + 1 =>
    if stop ≤ cursor then
      .ok acc.reverse
    else
      match decodeItem input cursor fuel depth with
      | .error e => .error e
      | .ok (t, next) =>
        if stop < next then
          .error (.listOverrun cursor)
        else
          decodeListElemsAux input next stop fuel depth (t :: acc)
termination_by structural fuel
end

/-- Parse one item at `offset` and report where it ended. The input
may remain after the item. -/
def decodePrefix (input : ByteArray) (offset : Nat) (maxDepth := defaultMaxDepth) :
    Except DecodeError (Item × Nat) :=
  decodeItem input offset (fuelFor input offset) maxDepth

/-- Decode a whole input (ARCHITECTURE.md §2.1). Strict: the input
must be exactly one canonical item; anything after it is
`trailingBytes`. -/
def decode (input : ByteArray) (maxDepth := defaultMaxDepth) :
    Except DecodeError Item :=
  match decodeItem input 0 (fuelFor input 0) maxDepth with
  | .error e => .error e
  | .ok (t, stop) => if stop = input.size then .ok t else .error (.trailingBytes stop)

end LeanRlp.Spec
