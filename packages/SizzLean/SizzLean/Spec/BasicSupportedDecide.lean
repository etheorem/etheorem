import SizzLean.Spec.BasicSupported

/-!
# `SizzLean.Spec.BasicSupportedDecide`: `BasicSupported` is decidable

`BasicSupported` gates the three central theorems and the user-facing
`SSZ.roundtrip` / `SSZ.serialize_injective`. A proof of it for a real
schema is a tree of constructors as deep as the schema. The Fulu
`BeaconState` has 38 fields and nests five containers down, so writing
that tree by hand for every consensus type does not scale.

This file makes the predicate decidable. `checkBasicSupported` is a
`Bool` recursion over the shape. It is sound
(`basicSupported_of_checkBasicSupported`) and complete
(`checkBasicSupported_of_basicSupported`), and the two together give a
`Decidable` instance. On any closed shape, `by decide` now discharges
`BasicSupported`:

```
example : SSZType.BasicSupported (SSZRepr.shape (T := MyContainer)) := by decide
```

## Why one check covers two constructors

The predicate splits each composite by fixed-size-ness: `vectorFixed` /
`vectorVar`, `listFixed` / `listVar`, `containerFixed` / `containerVar`.
The check does not. Both halves of each pair ask that every child be
`BasicSupported`, and `isFixedSize` picks the half. So the check reads
the side conditions only: `0 < n` on the vectors and the bitvector, and
`0 < t.fixedByteSize` on a list of fixed-size elements.

## Why the kernel can run it

`checkBasicSupported`, `isFixedSize`, and `fixedByteSize` all recurse
structurally, so `decide` evaluates them in the kernel without a
compiler axiom. The instance is `decidable_of_iff` over the `Bool`, so
the kernel reduces the check and never searches for a constructor tree.
-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual

/-- Decide `BasicSupported s` by recursion on `s`. Each arm states the
side condition the matching constructor carries. The `uintN` arm lists
the six widths the codec implements. -/
def SSZType.checkBasicSupported : SSZType → Bool
  | .uintN n      => n == 8 || n == 16 || n == 32 || n == 64 || n == 128 || n == 256
  | .bool         => true
  | .vector t n   => decide (0 < n) && SSZType.checkBasicSupported t
  | .list t _     =>
      SSZType.checkBasicSupported t && (!t.isFixedSize || decide (0 < t.fixedByteSize))
  | .bitvector n  => decide (0 < n)
  | .bitlist _    => true
  | .container fs => SSZType.checkBasicSupportedFields fs

/-- `checkBasicSupported` over a container's field list, pointwise. -/
def SSZType.checkBasicSupportedFields : List SSZType → Bool
  | []      => true
  | t :: ts => SSZType.checkBasicSupported t && SSZType.checkBasicSupportedFields ts

end

/-- A pointwise-supported field list whose fields are all fixed-size is
the `containerFixed` witness. -/
theorem SSZType.basicSupportedFieldsFixed_of_basicSupportedFields :
    ∀ {fs : List SSZType}, SSZType.BasicSupportedFields fs →
      SSZType.allFixedSize fs = true → SSZType.BasicSupportedFieldsFixed fs
  | [], _, _ => .nil
  | _ :: _, .cons h_t h_ts, h_fixed => by
      simp only [SSZType.allFixedSize, Bool.and_eq_true] at h_fixed
      exact .cons h_t h_fixed.1
        (SSZType.basicSupportedFieldsFixed_of_basicSupportedFields h_ts h_fixed.2)

/-- Every `containerFixed` field list is also a `containerVar` field
list: drop the fixed-size witnesses. -/
theorem SSZType.basicSupportedFields_of_basicSupportedFieldsFixed :
    ∀ {fs : List SSZType}, SSZType.BasicSupportedFieldsFixed fs →
      SSZType.BasicSupportedFields fs
  | _, .nil => .nil
  | _, .cons h_t _ h_ts =>
      .cons h_t (SSZType.basicSupportedFields_of_basicSupportedFieldsFixed h_ts)

mutual

/-- Soundness: a passing check is a `BasicSupported` witness. Structural
recursion on the shape. At each composite the witness picks its
constructor by `isFixedSize`, which the check never had to read. -/
theorem SSZType.basicSupported_of_checkBasicSupported :
    ∀ (s : SSZType), SSZType.checkBasicSupported s = true → SSZType.BasicSupported s
  | .uintN n, h => by
      simp only [SSZType.checkBasicSupported, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) <;> constructor
  | .bool, _ => .bool
  | .vector t n, h => by
      simp only [SSZType.checkBasicSupported, Bool.and_eq_true, decide_eq_true_eq] at h
      have h_t := SSZType.basicSupported_of_checkBasicSupported t h.2
      cases h_fixed : t.isFixedSize
      · exact .vectorVar h.1 h_t h_fixed
      · exact .vectorFixed h.1 h_t h_fixed
  | .list t cap, h => by
      simp only [SSZType.checkBasicSupported, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_true_eq] at h
      have h_t := SSZType.basicSupported_of_checkBasicSupported t h.1
      cases h_fixed : t.isFixedSize
      · exact .listVar h_t h_fixed
      · rcases h.2 with h_var | h_pos
        · simp [h_fixed] at h_var
        · exact .listFixed h_t h_fixed h_pos
  | .bitvector n, h => by
      simp only [SSZType.checkBasicSupported, decide_eq_true_eq] at h
      exact .bitvector h
  | .bitlist _, _ => .bitlist
  | .container fs, h => by
      simp only [SSZType.checkBasicSupported] at h
      have h_fs := SSZType.basicSupportedFields_of_checkBasicSupportedFields fs h
      cases h_fixed : SSZType.allFixedSize fs
      · exact .containerVar h_fs h_fixed
      · exact .containerFixed
          (SSZType.basicSupportedFieldsFixed_of_basicSupportedFields h_fs h_fixed)

/-- Soundness over a field list. -/
theorem SSZType.basicSupportedFields_of_checkBasicSupportedFields :
    ∀ (fs : List SSZType), SSZType.checkBasicSupportedFields fs = true →
      SSZType.BasicSupportedFields fs
  | [], _ => .nil
  | t :: ts, h => by
      simp only [SSZType.checkBasicSupportedFields, Bool.and_eq_true] at h
      exact .cons (SSZType.basicSupported_of_checkBasicSupported t h.1)
        (SSZType.basicSupportedFields_of_checkBasicSupportedFields ts h.2)

end

mutual

/-- Completeness: every `BasicSupported` witness passes the check.
Structural recursion on the witness, so the decision procedure rejects
no shape the proofs cover. -/
theorem SSZType.checkBasicSupported_of_basicSupported :
    ∀ {s : SSZType}, SSZType.BasicSupported s → SSZType.checkBasicSupported s = true
  | _, .uintN8 | _, .uintN16 | _, .uintN32 | _, .uintN64
  | _, .uintN128 | _, .uintN256 | _, .bool | _, .bitlist => by
      simp [SSZType.checkBasicSupported]
  | _, .vectorFixed h_pos h_t _ | _, .vectorVar h_pos h_t _ => by
      simp [SSZType.checkBasicSupported, h_pos, SSZType.checkBasicSupported_of_basicSupported h_t]
  | _, .listFixed h_t _ h_pos => by
      simp [SSZType.checkBasicSupported, h_pos, SSZType.checkBasicSupported_of_basicSupported h_t]
  | _, .listVar h_t h_var => by
      simp [SSZType.checkBasicSupported, h_var, SSZType.checkBasicSupported_of_basicSupported h_t]
  | _, .bitvector h_pos => by
      simp [SSZType.checkBasicSupported, h_pos]
  | _, .containerFixed h_fs => by
      simp only [SSZType.checkBasicSupported]
      exact SSZType.checkBasicSupportedFields_of_basicSupportedFields
        (SSZType.basicSupportedFields_of_basicSupportedFieldsFixed h_fs)
  | _, .containerVar h_fs _ => by
      simp only [SSZType.checkBasicSupported]
      exact SSZType.checkBasicSupportedFields_of_basicSupportedFields h_fs

/-- Completeness over a field list. -/
theorem SSZType.checkBasicSupportedFields_of_basicSupportedFields :
    ∀ {fs : List SSZType}, SSZType.BasicSupportedFields fs →
      SSZType.checkBasicSupportedFields fs = true
  | _, .nil => rfl
  | _, .cons h_t h_ts => by
      simp [SSZType.checkBasicSupportedFields,
        SSZType.checkBasicSupported_of_basicSupported h_t,
        SSZType.checkBasicSupportedFields_of_basicSupportedFields h_ts]

end

/-- `BasicSupported` is decidable, through the `Bool` check. The kernel
reduces `checkBasicSupported s` on a closed shape, so `by decide` closes
`BasicSupported s` with no compiler axiom. -/
instance SSZType.decBasicSupported (s : SSZType) : Decidable (SSZType.BasicSupported s) :=
  decidable_of_iff (SSZType.checkBasicSupported s = true)
    ⟨SSZType.basicSupported_of_checkBasicSupported s,
     SSZType.checkBasicSupported_of_basicSupported⟩

/-- The etheorem#61 shape from `Spec/BasicSupported.lean`, now by
`decide` instead of a hand-built constructor tree. -/
example : SSZType.BasicSupported (.container [.uintN 64, .list (.uintN 64) (2 ^ 40)]) := by
  decide

/-- The check rejects what the predicate rejects: a zero-width
bitvector, a zero-length vector, and an unimplemented integer width. -/
example : ¬ SSZType.BasicSupported (.bitvector 0) := by decide
example : ¬ SSZType.BasicSupported (.vector (.uintN 8) 0) := by decide
example : ¬ SSZType.BasicSupported (.uintN 24) := by decide

end SizzLean.Spec
