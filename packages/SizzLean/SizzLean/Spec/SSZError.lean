/-!
# `SizzLean.Spec.SSZError`: decode error taxonomy

The error carrier returned by every `deserialize` failure path. Per
ARCHITECTURE.md §3.3,
`deserialize : SSZType → ByteArray → Except SSZError (s.interp × Nat)`;
this file declares the `SSZError` inductive.

The taxonomy is intentionally minimal, only the failure modes
the decoder actually distinguishes. New tags can be added as
later work discovers new failure modes; the `Repr` derivation
keeps debugging output ergonomic and `DecidableEq` lets
downstream tests match on errors via `decide`.

## Lean idioms used here

* `inductive ... where`: sum type declaration; constructors enumerate
  the named cases.
* `deriving Repr, DecidableEq`: auto-synthesised printing and
  equality-decision instances. `Repr` produces a `Std.Format`-based
  pretty-printer Lean uses for `#eval` / error messages and for the
  default printer of `Except SSZError α`. `DecidableEq` produces
  `instance : DecidableEq SSZError`, what the round-trip `example`
  blocks (in `Spec/Deserialize.lean`) lean on, indirectly, to close
  the inner `Except`-equation by `decide` / `native_decide`. The
  derivation succeeds here (unlike `SSZType`) because all arms are
  nullary; no nested-inductive composition is needed.
-/

set_option autoImplicit false

namespace SizzLean.Spec

/-- Failure modes produced by `SSZType.deserialize`.

* `tooShort`: the input buffer ran out before a fixed-size field or
  declared offset region could be read in full.
* `invalidOffset`: an offset in a variable-size container or list
  prefix was non-monotone, fell outside the buffer, or was below the
  fixed-section minimum.
* `invalidSelector`: a `union` (or `compatUnion`) selector byte did
  not name a declared variant.
* `trailingBytes`: the wire encoding consumed strictly fewer bytes
  than the buffer provided, where the schema requires exact
  consumption.
* `bitlistMissingDelimiter`: a `bitlist` (or `progBitlist`) decoder
  could not find the trailing-`1`-bit sentinel: the last byte of the
  encoding was `0x00`, or the encoding was empty.
* `outOfRange`: a length-derived count exceeded the type's static
  capacity (e.g. an offset-table size implied more list elements
  than `cap`).

Tags are added on demand. Decoders introducing a new failure mode
should extend this inductive rather than reusing an unrelated tag. -/
inductive SSZError where
  | tooShort                : SSZError
  | invalidOffset           : SSZError
  | invalidSelector         : SSZError
  | trailingBytes           : SSZError
  | bitlistMissingDelimiter : SSZError
  | outOfRange              : SSZError
  deriving Repr, DecidableEq

end SizzLean.Spec
