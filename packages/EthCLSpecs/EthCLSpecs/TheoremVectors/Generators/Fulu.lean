import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Fulu
import EthCLSpecs.TheoremVectors.Bindings.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Generators.Fulu`: the Fulu generator file

The generator list for Fulu (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the `survey` clause reads and lists every public
theorem of the fork's proof namespace, phase A alone (§14.3).

Stage 2 scopes the generator to Gloas, whose acceptance theorems the plan
pins; Fulu's discovery clauses, named lines, and seeds land in stage 9,
once the stage 1 report shows which of its theorems are in scope.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Fulu.fulu

theorem_vectors survey
