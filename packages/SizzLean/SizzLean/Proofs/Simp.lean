import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# `SizzLean.Proofs.Simp`: the `@[ssz_simp]` simp set (registration)

ARCHITECTURE.md §4 names a tagged simp set (`ssz_simp`) as part of
the Layer 2 tactic vocabulary: every encode/decode equation in Spec
gets tagged, then `simp [ssz_simp]` unfolds the recursion uniformly
inside induction-on-`SSZType` cases.

This file is split in two:

* **`Proofs/Simp.lean`** (this file): pure attribute registration
  via `register_simp_attr`. Imports only the Lean core macro module.
  Stays in its own file because the `register_simp_attr` macro
  expands to `public meta initialize`, and the resulting attribute
  is only visible to *importers* of this file, not later code in
  the same file. So we register here, and apply `attribute [...]`
  to spec declarations in `Proofs/SimpAttrs.lean`.
* **`Proofs/SimpAttrs.lean`**: bulk-applies `@[ssz_simp]` to the
  serializer/deserializer mutual block plus `interp` helpers and
  `isFixedSize` / `allFixedSize` / `fixedByteSize`. Imports both
  this file and `Spec/{Serialize,Deserialize,Interp}.lean`.

This two-file split is a Lean 4.29.1 module-system quirk; once the
proofs are written, the user calls `simp [ssz_simp]` and gets the
combined set regardless of where it was assembled.
-/

set_option autoImplicit false

/-- Tagged simp set for SSZ encode/decode equations. Tag a `def` with
`@[ssz_simp]` to add all of its auto-generated equation lemmas; call
`simp [ssz_simp]` (or `simp_all [ssz_simp]`) to use the set during
proofs. See `Proofs/SimpAttrs.lean` for what's currently tagged. -/
register_simp_attr ssz_simp
