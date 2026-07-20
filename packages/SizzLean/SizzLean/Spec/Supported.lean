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
  a `List SSZType`. Needed by the `containerFixed` case: the
  decoder's all-fixed-size path handles these field lists directly.
* `SupportedFields`: pointwise `Supported`, no `isFixedSize`
  constraint. Needed by the `containerVar` case: the decoder's
  offset-table path (`SSZType.deserializeVarFields`) handles fixed
  and variable fields alike.
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
  /-- The two wide spec widths (`uint128` / `uint256`), implemented
  through the `Nat`-based `natToLEBytes` / `readNatLE` codec rather
  than the fully-unrolled fixed-width writers of the narrow arms. -/
  | uintN128       : SSZType.Supported (.uintN 128)
  | uintN256       : SSZType.Supported (.uintN 256)
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
  /-- `container` decode is implemented for all-fixed-size
  field lists. -/
  | containerFixed : ∀ {fs : List SSZType},
                     SSZType.SupportedFieldsFixed fs →
                     SSZType.Supported (.container fs)
  /-- `container` decode is also implemented for field lists with
  at least one variable-size field, via the offset-table path
  (`SSZType.deserializeVarFields`). The `Bool` argument mirrors
  `allFixedSize fs`; unlike `containerFixed`'s `isFixedSize = true`
  witness per field, this predicate carries no positional
  constraint (the offset table handles fixed and variable fields
  alike). -/
  | containerVar   : ∀ {fs : List SSZType},
                     SSZType.SupportedFields fs →
                     SSZType.allFixedSize fs = false →
                     SSZType.Supported (.container fs)

/-- Pointwise `Supported ∧ isFixedSize` over a field list. Used by
`containerFixed`. The second conjunct (`isFixedSize`) is what makes
the container decode case typecheck: `deserialize`'s `.container`
arm guards on `allFixedSize fs` and falls back to `.error` otherwise. -/
inductive SSZType.SupportedFieldsFixed : List SSZType → Prop
  | nil  : SSZType.SupportedFieldsFixed []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.Supported t → t.isFixedSize = true →
           SSZType.SupportedFieldsFixed ts →
           SSZType.SupportedFieldsFixed (t :: ts)

/-- Pointwise `Supported`, no `isFixedSize` constraint. Used by
`containerVar`: the offset-table decode path handles fixed and
variable fields alike, so every field just needs to be individually
`Supported`. -/
inductive SSZType.SupportedFields : List SSZType → Prop
  | nil  : SSZType.SupportedFields []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.Supported t →
           SSZType.SupportedFields ts →
           SSZType.SupportedFields (t :: ts)
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
  | uintN128       : SSZType.SupportedBounded (.uintN 128)
  | uintN256       : SSZType.SupportedBounded (.uintN 256)
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
  /-- Mirrors `Supported.containerVar`: every field of a
  mixed-field container is itself bounded (whether fixed or
  variable, `list` / `bitlist` fields are still capped, hence
  bounded), so the container as a whole has a finite static size
  bound too. -/
  | containerVar   : ∀ {fs : List SSZType},
                     SSZType.SupportedBoundedFields fs →
                     SSZType.allFixedSize fs = false →
                     SSZType.SupportedBounded (.container fs)

/-- Pointwise `SupportedBounded ∧ isFixedSize`, for `containerFixed`. -/
inductive SSZType.SupportedBoundedFieldsFixed : List SSZType → Prop
  | nil  : SSZType.SupportedBoundedFieldsFixed []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.SupportedBounded t → t.isFixedSize = true →
           SSZType.SupportedBoundedFieldsFixed ts →
           SSZType.SupportedBoundedFieldsFixed (t :: ts)

/-- Pointwise `SupportedBounded`, no `isFixedSize` constraint, for
`containerVar`. -/
inductive SSZType.SupportedBoundedFields : List SSZType → Prop
  | nil  : SSZType.SupportedBoundedFields []
  | cons : ∀ {t : SSZType} {ts : List SSZType},
           SSZType.SupportedBounded t →
           SSZType.SupportedBoundedFields ts →
           SSZType.SupportedBoundedFields (t :: ts)
end

end SizzLean.Spec
