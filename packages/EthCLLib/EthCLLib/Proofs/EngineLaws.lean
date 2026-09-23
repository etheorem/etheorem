import EthCLLib.Spec.Engine

/-!
# `EthCLLib.Proofs.EngineLaws`: the inclusion-list rule of the execution layer

`ExecutionEngine.isInclusionListSatisfied` is an Engine-API call. The model does not run
the EVM, so it does not compute the answer. EIP-7805 gives the rule that the EL applies. A
payload satisfies an inclusion list when each listed transaction is in the payload, or when
the EL can omit the transaction. The EL can omit a transaction when the block has no gas
left for it, or when the transaction is not valid on the post-state.

`LawfulInclusionList` states that rule as an assumption on an `ExecutionEngine` instance.
It is a `Prop` structure that a theorem takes as an explicit hypothesis, so the optimistic
default instance does not change. The rule has two parameters. `txs` gives the
transactions of a payload. `isValidOmission` tells when the EL can omit a transaction. A
theorem that assumes the rule names both in its signature. A structure suits the rule
better than a class. Instance search would have to match the function `txs` up to
reducible unfolding, and no instance exists to find.

The rule does not make `isValidOmission` narrow. For example, the optimistic engine
satisfies it with `isValidOmission _ _ := True` (the `example` below checks this). A
conclusion of the form "`tx` is in the
payload or `isValidOmission payload tx`" is only as strong as the predicate that the
reader supplies.

The rule is a proof assumption, so it lives in `EthCLLib.Proofs`. The fork bodies do not
use it.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (ExecutionEngine)

/-- The EIP-7805 inclusion rule for an `ExecutionEngine`. The EL answer for `ilTxs` is
`true` exactly when each transaction of `ilTxs` is in `txs p` or satisfies
`isValidOmission p`. -/
structure LawfulInclusionList (Payload Tx Requests : Type) [ExecutionEngine Payload Tx Requests]
    (txs : Payload → Array Tx) (isValidOmission : Payload → Tx → Prop) : Prop where
  /-- The EL answer agrees with the rule. -/
  satisfied_iff (p : Payload) (ilTxs : Array Tx) :
    ExecutionEngine.isInclusionListSatisfied (Requests := Requests) p ilTxs = true ↔
      ∀ tx ∈ ilTxs, tx ∈ txs p ∨ isValidOmission p tx

/-- The optimistic default engine satisfies the rule with `isValidOmission _ _ := True`,
for any `txs`. Its answer is always `true`, and every transaction meets `True`. -/
example {Payload Tx Requests : Type} (txs : Payload → Array Tx) :
    @LawfulInclusionList Payload Tx Requests EthCLLib.Spec.instExecutionEngineOptimistic txs
      (fun _ _ => True) :=
  ⟨fun _ _ => by simp [ExecutionEngine.isInclusionListSatisfied]⟩

end EthCLLib.Proofs
