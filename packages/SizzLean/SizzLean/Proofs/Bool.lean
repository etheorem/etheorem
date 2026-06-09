import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.SimpAttrs

/-!
# `SizzLean.Proofs.Bool`: `decode_encode` and size bound for `.bool`

Two-line proofs each: `cases x <;> (unfold; rfl)` for the
roundtrip; `cases x <;> (unfold; decide)` for the size bound.
Pulled into its own module to keep the `Proofs/Roundtrip.lean`
dispatcher trivial.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Spec

/-- Roundtrip for `.bool`.

Two ground cases (`true`, `false`); each reduces to `.ok (·, 1)` by
unfolding the dispatch and letting the kernel evaluate the LE-byte
write and read. -/
theorem decode_encode_bool : ∀ (x : Bool),
    SSZType.deserialize .bool (SSZType.serialize .bool x) =
      .ok (x, (SSZType.serialize .bool x).size) := by
  intro x
  cases x <;> (unfold SSZType.deserialize SSZType.serialize; rfl)

/-- Per-bool size bound. Both `true` and `false` serialize to a
1-byte `ByteArray`, and `maxByteLength .bool = 1`, so `1 ≤ 1`
closes each case. -/
theorem encode_size_le_max_bool : ∀ (x : Bool),
    (SSZType.serialize .bool x).size ≤ SSZType.maxByteLength .bool := by
  intro x
  cases x <;> (unfold SSZType.serialize SSZType.maxByteLength; decide)

end SizzLean.Proofs
