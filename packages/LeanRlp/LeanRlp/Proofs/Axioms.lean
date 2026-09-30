import LeanRlp.Proofs.Canonical
import LeanRlp.Proofs.Roundtrip
import LeanRlp.Proofs.Schema
import LeanRlp.Proofs.Size

/-!
# `LeanRlp.Proofs.Axioms`: the axiom gate

Holds each of the nine theorems of ARCHITECTURE.md §5 to `propext`,
`Classical.choice`, and `Quot.sound` at most. LeanRlp declares no
opaque constant and no axiom of its own (ARCHITECTURE.md §3), so
this file is the enforcement: it re-checks the axiom profile on
every build, and a new dependency in any proof fails the gate.

Stage 3 writes the gate as one `#guard_msgs` command per theorem.
This scaffolding file imports the proof modules only, so the gate's
shape is visible before the theorems exist.

Filled in PLAN.md Stage 3 (the gate) and Stage 4 (the schema laws).
-/

set_option autoImplicit false

namespace LeanRlp.Proofs

end LeanRlp.Proofs
