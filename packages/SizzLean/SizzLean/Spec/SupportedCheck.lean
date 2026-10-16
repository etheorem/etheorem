import SizzLean.Spec.Supported

/-!
# `SizzLean.Spec.SupportedCheck`: `Supported` by evaluation

`Supported` is a `Prop`, and this module does not change that. Proofs take
`Supported s` as a hypothesis and split it into cases. Each constructor carries
the witnesses for its parts, and a case split exposes them. `SSZType` has no
`DecidableEq` instance. That blocks an automatic `Decidable (Supported s)`
instance.

A proof about a concrete schema must still supply the witness. A fork's
`BeaconState` has too many fields to write that witness as a term.
`SSZType.checkSupported` computes the same property as a `Bool`.
`supported_of_checkSupported` turns a `true` result into the witness. The term
`supported_of_checkSupported _ (by decide)` therefore proves `Supported s` for a
closed `s`.

This module proves soundness only. A `true` result gives the witness. A `false` result
proves nothing.

The check follows the constructors of `Supported`:

* A `uintN` passes at the six spec widths: 8, 16, 32, 64, 128, and 256.
* A `bool`, a `bitvector`, and a `bitlist` always pass.
* A vector or a list passes when its element type passes. The witness uses the
  `Fixed` or the `Var` constructor, as the element's `isFixedSize` selects.
* A container passes when every field passes. `allFixedSize` selects
  `containerFixed` or `containerVar` in the same way.
-/

set_option autoImplicit false

namespace SizzLean.Spec

mutual
/-- `Supported` as a `Bool`. -/
def SSZType.checkSupported : SSZType → Bool
  | .uintN n => n == 8 || n == 16 || n == 32 || n == 64 || n == 128 || n == 256
  | .bool => true
  | .bitvector _ => true
  | .bitlist _ => true
  | .vector t _ => t.checkSupported
  | .list t _ => t.checkSupported
  | .container fs => SSZType.checkSupportedFields fs

/-- `SupportedFields` as a `Bool`: every field passes `checkSupported`. -/
def SSZType.checkSupportedFields : List SSZType → Bool
  | [] => true
  | t :: ts => t.checkSupported && SSZType.checkSupportedFields ts
end

/-- An all-fixed field list of supported fields is `SupportedFieldsFixed`. The
`containerFixed` arm needs this form, and `allFixedSize` carries the per-field
`isFixedSize` facts it adds. -/
theorem SSZType.supportedFieldsFixed_of_supportedFields :
    ∀ (fs : List SSZType), SSZType.SupportedFields fs →
      SSZType.allFixedSize fs = true → SSZType.SupportedFieldsFixed fs
  | [], _, _ => .nil
  | t :: ts, h, hfix => by
      cases h with
      | cons ht hts =>
          simp only [SSZType.allFixedSize, Bool.and_eq_true] at hfix
          exact .cons ht hfix.1
            (SSZType.supportedFieldsFixed_of_supportedFields ts hts hfix.2)

mutual
/-- **Soundness.** A shape that passes the check is `Supported`. -/
theorem SSZType.supported_of_checkSupported :
    ∀ (s : SSZType), s.checkSupported = true → s.Supported
  | .uintN n, h => by
      simp only [SSZType.checkSupported, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((((h | h) | h) | h) | h) | h <;> subst h
      · exact .uintN8
      · exact .uintN16
      · exact .uintN32
      · exact .uintN64
      · exact .uintN128
      · exact .uintN256
  | .bool, _ => .bool
  | .bitvector _, _ => .bitvector
  | .bitlist _, _ => .bitlist
  | .vector t _, h => by
      have ht := SSZType.supported_of_checkSupported t (by simpa [SSZType.checkSupported] using h)
      cases hf : t.isFixedSize
      · exact .vectorVar ht hf
      · exact .vectorFixed ht hf
  | .list t _, h => by
      have ht := SSZType.supported_of_checkSupported t (by simpa [SSZType.checkSupported] using h)
      cases hf : t.isFixedSize
      · exact .listVar ht hf
      · exact .listFixed ht hf
  | .container fs, h => by
      have hfs := SSZType.supportedFields_of_checkSupportedFields fs
        (by simpa [SSZType.checkSupported] using h)
      cases hf : SSZType.allFixedSize fs
      · exact .containerVar hfs hf
      · exact .containerFixed (SSZType.supportedFieldsFixed_of_supportedFields fs hfs hf)

/-- **Soundness, over a field list.** -/
theorem SSZType.supportedFields_of_checkSupportedFields :
    ∀ (fs : List SSZType), SSZType.checkSupportedFields fs = true →
      SSZType.SupportedFields fs
  | [], _ => .nil
  | t :: ts, h => by
      simp only [SSZType.checkSupportedFields, Bool.and_eq_true] at h
      exact .cons (SSZType.supported_of_checkSupported t h.1)
        (SSZType.supportedFields_of_checkSupportedFields ts h.2)
end

/-- A mixed container: a `uint64`, a list of `uint64`, and a fixed
two-field container. -/
example : SSZType.Supported
    (.container [.uintN 64, .list (.uintN 64) 8, .container [.bool, .uintN 256]]) :=
  SSZType.supported_of_checkSupported _ (by decide)

/-- An odd width fails the check. -/
example : (SSZType.uintN 7).checkSupported = false := by decide

end SizzLean.Spec
