import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Generators.Fulu`: the Fulu generator file

The generator list for Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header names
the fork's binding; the `characterized` clause selects the contract
theorems, and the `probe` clause is the stage-1 sizing pass over every
public theorem of the fork's proof namespace (the plan's stage 1; see
`Command.lean`'s module docstring). No witness is searched at this stage:
each theorem's run reads its statement, classifies it, and writes the
outcome line the report folds.

Stage 2 drops the `probe` clause and the generator grows named lines,
seeds, and `presets` here.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Fulu.fulu

theorem_vectors characterized
theorem_vectors probe
