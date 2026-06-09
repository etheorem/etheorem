import SizzLean.Spec.Type
import SizzLean.Spec.Serialize

/-!
# `SizzLean.Spec.Supported`: the predicate guarding Layer 2 theorems

The three central theorems (`decode_encode`,
`serialize_injective`, `encode_size_le_max`) are stated
*universally over `SSZType`*, but `Spec/Serialize.lean` and
`Spec/Deserialize.lean` cover only a subset of the `SSZType`
universe. For constructors outside that subset the theorems are
not just unproved but actually false (encode returns `.empty`,
decode returns `.error`, so roundtrip cannot hold).

Each theorem is therefore guarded by a `Supported s` hypothesis
that names exactly the constructors with real implementations.

## Why three predicates, not one

* `Supported`: the broadest predicate, used by Roundtrip and
  Injective. Covers uncapped types (`progBitlist`, `progList t`)
  because roundtrip and injectivity make sense for them, they have
  no static *size* bound but the encode/decode pair still inverts
  cleanly.
* `SupportedFieldsFixed`: pointwise `Supported ∧ isFixedSize` over
  a `List SSZType`. Needed by the `container` case: the decoder
  handles all-fixed-size field lists; mixed/variable field lists
  fall through to `.error`.
* `SupportedBounded`: strict subset of `Supported` that *excludes*
  uncapped types (`progBitlist`, `progList`). Used only by
  `encode_size_le_max` in `Proofs/SizeBound.lean`, where uncapped
  collections have no sensible finite upper bound. Separation
  rather than reshaping `maxByteLength` to `Option Nat` keeps the
  three theorem statements parallel.

## Why `Prop`, not `Bool`

A `Bool`-valued function would buy decidability (`decide` could
discharge `Supported s` for a closed `s`), but in proofs we always
take it as a *hypothesis* and case-split: each constructor of the
`Supported` inductive carries its sub-witnesses directly, while a
`Bool` would need `simp [isSupported]` + `cases s` to extract the
same information. The `Prop` form keeps induction hypotheses clean.
`DecidableEq SSZType` is also absent (see the note in
`Spec/Type.lean`), which would block lifting a `Bool` predicate to
`Decidable Supported` automatically.
-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual
/-- The implemented constructors and their structural support
witnesses. Each constructor of this inductive corresponds to a
constructor of `SSZType` that has a real `serialize` and
`deserialize` implementation in `Spec/Serialize.lean` and
`Spec/Deserialize.lean`. -/
inductive SSZType.Supported : SSZType → Prop
  | uintN8         : SSZType.Supported (.uintN 8)
  | uintN16        : SSZType.Supported (.uintN 16)
  | uintN32        : SSZType.Supported (.uintN 32)
  | uintN64        : SSZType.Supported (.uintN 64)
  | bool           : SSZType.Supported .bool
  | bitvector      : ∀ {n : Nat}, SSZType.Supported (.bitvector n)
  | bitlist        : ∀ {cap : Nat}, SSZType.Supported (.bitlist cap)
  /-- `vector` decode handles only fixed-size element types; the
  variable-size offset-table read is not implemented. The
  `isFixedSize = true` witness mirrors `listFixed`. -/
  | vectorFixed    : ∀ {t : SSZType} {n : Nat},
                     SSZType.Supported t → t.isFixedSize = true →
                     SSZType.Supported (.vector t n)
  /-- `list` decode is implemented for fixed-size element types.
  The `isFixedSize = true` witness on `t` is what makes the
  Roundtrip proof discharge for this arm. -/
  | listFixed      : ∀ {t : SSZType} {cap : Nat},
                     SSZType.Supported t → t.isFixedSize = true →
                     SSZType.Supported (.list t cap)
  /-- `container` decode is only implemented for all-fixed-size
  field lists. -/
  | containerFixed : ∀ {fs : List SSZType},
                     SSZType.SupportedFieldsFixed fs →
                     SSZType.Supported (.container fs)

/-- Pointwise `Supported ∧ isFixedSize` over a field list. Used by
`container`. The second conjunct (`isFixedSize`) is what makes the
container decode case typecheck: `deserialize`'s `.container` arm
guards on `allFixedSize fs` and falls back to `.error` otherwise. -/
inductive SSZType.SupportedFieldsFixed : List SSZType → Prop
  | nil  : SSZType.SupportedFieldsFixed []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.Supported t → t.isFixedSize = true →
           SSZType.SupportedFieldsFixed ts →
           SSZType.SupportedFieldsFixed (t :: ts)
end

mutual
/-- Strict subset of `Supported`. Every `Supported` shape in the
current `SSZType` universe also has a finite static size bound, so
`SupportedBounded` is extensionally equal to `Supported`; the two
predicates are kept distinct because `encode_size_le_max` proofs
phrase their hypothesis as "bounded", and the indirection costs
nothing. The split also leaves room: any uncapped form (e.g. a
`progressiveList` arm for EIP-7916) would add a constructor to
`Supported` but not to `SupportedBounded`, so the predicates would
diverge without renaming the existing theorems. -/
inductive SSZType.SupportedBounded : SSZType → Prop
  | uintN8         : SSZType.SupportedBounded (.uintN 8)
  | uintN16        : SSZType.SupportedBounded (.uintN 16)
  | uintN32        : SSZType.SupportedBounded (.uintN 32)
  | uintN64        : SSZType.SupportedBounded (.uintN 64)
  | bool           : SSZType.SupportedBounded .bool
  | bitvector      : ∀ {n : Nat}, SSZType.SupportedBounded (.bitvector n)
  | bitlist        : ∀ {cap : Nat}, SSZType.SupportedBounded (.bitlist cap)
  | vectorFixed    : ∀ {t : SSZType} {n : Nat},
                     SSZType.SupportedBounded t → t.isFixedSize = true →
                     SSZType.SupportedBounded (.vector t n)
  | listFixed      : ∀ {t : SSZType} {cap : Nat},
                     SSZType.SupportedBounded t → t.isFixedSize = true →
                     SSZType.SupportedBounded (.list t cap)
  | containerFixed : ∀ {fs : List SSZType},
                     SSZType.SupportedBoundedFieldsFixed fs →
                     SSZType.SupportedBounded (.container fs)

/-- Pointwise `SupportedBounded ∧ isFixedSize`, for `container`. -/
inductive SSZType.SupportedBoundedFieldsFixed : List SSZType → Prop
  | nil  : SSZType.SupportedBoundedFieldsFixed []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.SupportedBounded t → t.isFixedSize = true →
           SSZType.SupportedBoundedFieldsFixed ts →
           SSZType.SupportedBoundedFieldsFixed (t :: ts)
end

end SizzLean.Spec
