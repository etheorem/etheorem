import LeanRlp.Proofs.Canonical
import LeanRlp.Proofs.Fuel
import LeanRlp.Proofs.Roundtrip
import LeanRlp.Proofs.Schema
import LeanRlp.Proofs.Size

/-!
# `LeanRlp.Proofs.Axioms`: the axiom gate

Holds each theorem under `Proofs/` to `propext`,
`Classical.choice`, and `Quot.sound` at most: one `#guard_msgs`
command per theorem, so a new dependency in any proof fails the
build. LeanRlp declares no opaque constant and no axiom of its own
(ARCHITECTURE.md §3), and this file is the enforcement.

The fuel and header theorems of `Proofs.Fuel` are gated. Stage 3
adds the command for each theorem of ARCHITECTURE.md §5 as its
proof lands, and Stage 4 the two schema laws.
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

-- The messages below quote `#print axioms` output verbatim, so a
-- new axiom in any gated proof fails the build with the diff.

/-- info: 'LeanRlp.Proofs.decodeHeader_ok_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decodeHeader_ok_bytes

/-- info: 'LeanRlp.Proofs.decodeHeader_ok_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decodeHeader_ok_list

/-- info: 'LeanRlp.Proofs.decodeHeader_not_outOfFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decodeHeader_not_outOfFuel

/-- info: 'LeanRlp.Proofs.decodeItem_end_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decodeItem_end_gt

/-- info: 'LeanRlp.Proofs.decode_fuelSufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decode_fuelSufficient

/-- info: 'LeanRlp.Proofs.decodePrefix_not_outOfFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decodePrefix_not_outOfFuel

/-- info: 'LeanRlp.Proofs.decode_not_outOfFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanRlp.Proofs.decode_not_outOfFuel

end LeanRlp.Proofs
