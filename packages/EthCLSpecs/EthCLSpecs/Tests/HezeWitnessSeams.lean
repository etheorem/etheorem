import EthCLSpecs.Proofs.Heze.InclusionDichotomy

/-!
# `EthCLSpecs.Tests.HezeWitnessSeams`: the execution engine of the Heze witnesses

The witness modules (`HezeDichotomyWitness`, `HezeNetworkWitness`) run the Heze handlers
with one execution engine. `strictEngine` applies the EIP-7805 rule with no valid omission:
the answer is `true` exactly when every listed transaction is in the payload. Its payload
check accepts every payload. `strictEngine_lawful` proves that it meets
`LawfulInclusionList` with `isValidOmission := fun _ _ => False`.

`strictEngine` adds no global instance. Its scoped instance `strictEngineInstance` takes
effect in a witness module through `open scoped EthCLSpecs.Tests.HezeWitnessSeams`. The
engine reads no hash, so it fits the FFI hasher of the dichotomy witness and the pure-Lean
hasher of the network witness.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.Proofs (LawfulInclusionList)

namespace EthCLSpecs.Tests.HezeWitnessSeams

open EthCLSpecs.Heze (Preset ExecutionPayload ExecutionRequests Transaction)

variable [Preset]

/-- The EIP-7805 rule with no valid omission. -/
@[reducible] def strictEngine : ExecutionEngine ExecutionPayload Transaction ExecutionRequests where
  isInclusionListSatisfied p ilTxs := ilTxs.all fun tx => p.transactions.toArray.contains tx
  verifyAndNotifyNewPayload _ _ _ _ := true

/-- `strictEngine` as an instance of high priority. `open scoped
EthCLSpecs.Tests.HezeWitnessSeams` installs it in a witness module. -/
scoped instance (priority := high) strictEngineInstance :
    ExecutionEngine ExecutionPayload Transaction ExecutionRequests :=
  strictEngine

/-- `strictEngine` satisfies the rule with no valid omission. -/
theorem strictEngine_lawful :
    LawfulInclusionList ExecutionPayload Transaction ExecutionRequests
      (fun p => p.transactions.toArray) (fun _ _ => False) :=
  ⟨fun p ilTxs => by
    show (ilTxs.all fun tx => p.transactions.toArray.contains tx) = true ↔ _
    simp only [Array.all_eq_true_iff_forall_mem, Array.contains_iff_mem, or_false]⟩

end EthCLSpecs.Tests.HezeWitnessSeams
