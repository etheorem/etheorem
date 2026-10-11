import EthCLLib.TheoremVectors.Command
import EthCLSpecs.Proofs.Heze
import EthCLSpecs.TheoremVectors.Bindings.Heze

/-!
# `EthCLSpecs.TheoremVectors.Generators.Heze`: the Heze generator file

The generator list for Heze (`THEOREM_VECTORS_ARCHITECTURE.md` §14, §4.2). The header
names the fork's binding; the `survey` clause reads and lists every public
theorem of the fork's proof namespace, phase A alone (§14.3).

Stage 2 scopes the generator to Gloas. Most Heze theorems take a `Store`,
so the block-input rule (§1.2) puts them out of scope; Heze's discovery
clauses, named lines, and seeds land in stage 9 with the other forks.
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.Heze.heze

theorem_vectors survey
