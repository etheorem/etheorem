import LeanRlp.Spec.Scalar

/-!
# `LeanRlp.Spec.Item`: the RLP item tree

The untyped value layer of the codec: an `Item` is either a byte
string or a list of items. Every execution-layer structure encodes
to an `Item` tree first and to bytes second, and the codec names no
execution-layer type; a consumer derives or writes instances for its
own types in its own package (ARCHITECTURE.md §3).

The module also holds five things the rest of the codec shares:

* `Item.encodedSize`: the byte length of `encode`, computed without
  encoding. The encoder reads it for list headers, so the byte count
  of a record has one home; theorem 4 of ARCHITECTURE.md §5 states
  that it equals `(encode t).size`.
* `Item.Encodable`: every byte-string payload in the tree, and every
  list payload, is shorter than 2^64 bytes. The bound covers list
  payloads because a list payload of 2^64 bytes overflows the
  long-form header byte. The round-trip theorems take `Encodable` as
  a hypothesis, and the encoder performs no run-time check
  (ARCHITECTURE.md §2.1).
* `DecidableEq Item`: equality does not derive, because the type
  nests through `List`; this is the hand-written instance
  (ARCHITECTURE.md §2.1). The known-answer gates decide item
  equations with it.
* `isSingleLowByte`: the single-byte-form test that the size
  function and the encoder share.
* `Repr Item`: printing, for the gates and the Stage 2 runner.
  `ByteArray` has no `Repr` on the pinned toolchain, so the byte
  array and the item each carry a hand-written instance.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

/-- An RLP item: a byte string, or a list of items. -/
inductive Item where
  | bytes (b : ByteArray)
  | list (items : List Item)

/-- True when `b` takes the single-byte form: exactly one byte,
below `0x80`. The encoder writes such a string as itself, and the
size function counts one byte for it. -/
def isSingleLowByte (b : ByteArray) : Bool :=
  b.size == 1 && b[0]! < 0x80

mutual
/-- The byte length of `encode t`, computed without encoding. The
encoder reads it for list headers, and theorem 4 (ARCHITECTURE.md
§5) states that it equals `(encode t).size`. -/
def Item.encodedSize : Item → Nat
  | .bytes b =>
    if isSingleLowByte b then 1 else 1 + lenOfLen b.size + b.size
  | .list items =>
    let n := encodedSizeList items
    1 + lenOfLen n + n

/-- The total byte length of a list payload: the encodings of the
list's items, concatenated. -/
def encodedSizeList : List Item → Nat
  | [] => 0
  | t :: ts => Item.encodedSize t + encodedSizeList ts
end

mutual
/-- Every byte-string payload and every list payload in the tree is
below 2^64 bytes, so every header the encoder writes is the short
form or the bounded long form (ARCHITECTURE.md §2.1). The list
payload needs the bound as much as strings do: a list payload of
2^64 bytes overflows the long-form header byte. -/
def Item.Encodable : Item → Prop
  | .bytes b => b.size < 2 ^ 64
  | .list items => encodableListOf items ∧ encodedSizeList items < 2 ^ 64

/-- `Encodable` over a list: every item in the list carries the
bound. -/
def encodableListOf : List Item → Prop
  | [] => True
  | t :: ts => t.Encodable ∧ encodableListOf ts
end

mutual
/-- Equality on `Item` does not derive, because the type nests
through `List` (ARCHITECTURE.md §2.1). This is the hand-written
instance, mutual with the list comparison below it. -/
instance instDecidableEqItem : DecidableEq Item
  | .bytes x, .bytes y =>
    if h : x = y then .isTrue (by rw [h])
    else .isFalse (fun h' => h (Item.bytes.inj h'))
  | .list xs, .list ys =>
    match decEqListOfItem xs ys with
    | .isTrue h => .isTrue (by rw [h])
    | .isFalse h => .isFalse (fun h' => h (Item.list.inj h'))
  | .bytes _, .list _ => .isFalse (by intro h; cases h)
  | .list _, .bytes _ => .isFalse (by intro h; cases h)

/-- The list comparison of the item equality. The `Item` instance
calls it directly, and core's `DecidableEq (List α)` serves any
other list use. -/
def decEqListOfItem (xs ys : List Item) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => .isTrue rfl
  | x :: xs, y :: ys =>
    match instDecidableEqItem x y with
    | .isTrue hxy =>
      match decEqListOfItem xs ys with
      | .isTrue hxs => .isTrue (by rw [hxy, hxs])
      | .isFalse hxs => .isFalse (fun h => hxs (List.cons.inj h).2)
    | .isFalse hxy => .isFalse (fun h => hxy (List.cons.inj h).1)
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
end

/-- Prints a byte array as its byte list. Core has no `Repr
ByteArray` on the pinned toolchain. Scoped to this namespace, like
the `Item` printer below it. -/
scoped instance : Repr ByteArray :=
  ⟨fun b _ => repr b.data.toList⟩

mutual
/-- Prints an item tree, with application parentheses at
precision `prec`. The deriving handler cannot see through `List`,
so this printer is hand-written. -/
def reprItemPrec : Item → Nat → Std.Format
  | .bytes b, prec =>
    Repr.addAppParen (Std.Format.text "Item.bytes " ++ reprArg b) prec
  | .list xs, prec =>
    Repr.addAppParen (Std.Format.text "Item.list " ++
      Std.Format.bracket "[" (reprListPrec xs 0) "]") prec

/-- The comma-separated printer for a list of items. -/
def reprListPrec : List Item → Nat → Std.Format
  | [], _ => Std.Format.text ""
  | [x], _ => reprItemPrec x 0
  | x :: xs, _ => reprItemPrec x 0 ++ Std.Format.text ", " ++ reprListPrec xs 0
end

/-- Prints an item tree. Scoped to this namespace. -/
scoped instance : Repr Item :=
  ⟨fun t prec => reprItemPrec t prec⟩

end LeanRlp.Spec
