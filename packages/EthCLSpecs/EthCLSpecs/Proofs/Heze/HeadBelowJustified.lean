import EthCLSpecs.Proofs.Heze.HeadAvoidsFull

/-!
# `EthCLSpecs.Proofs.Heze.HeadBelowJustified`: the head lies below the justified node

`get_head` (gloas `fork-choice.md:572-595`) starts its walk at the pending node of the
justified root. Each step moves to a child, so the head that it returns lies below that node.
`getHead_run_below_justified` states this in the node tree of `HeadAvoidsFull.lean`.

The proof keeps `NodeBelow` from the start node as a loop invariant of `fuelLoop`
(`fuelLoop_run_inv`). A `.next` step adds one edge (`headLoopBody_run_next_edge`). A `.done`
step returns the current node (`headLoopBody_run_done`). The fuel-out value is the start node,
which is below itself.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok fuelLoop_run_inv)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Config Store ForkChoiceNode getHead)

section
variable {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]

/-- The head that `getHead` returns lies below the pending node of the justified root. -/
theorem getHead_run_below_justified (store runnerStore s' : Store map) (head : ForkChoiceNode)
    (hrun : (getHead (StoreTransition := ForkChoiceStoreRun (Store map)) store).run runnerStore
      = .ok (head, s')) :
    NodeBelow store (.pending store.justifiedCheckpoint.root) head := by
  rw [getHead_eq_fuelLoop_headLoopBody] at hrun
  obtain ⟨blocks, s1, -, hloop⟩ := run_bind_eq_ok _ _ _ _ hrun
  refine fuelLoop_run_inv (fun n => NodeBelow store (.pending store.justifiedCheckpoint.root) n)
    (fun n => NodeBelow store (.pending store.justifiedCheckpoint.root) n) _ _ ?_ ?_ .refl
    _ _ _ _ _ .refl hloop
  · intro n c t t' hn hst
    exact .step n c hn (headLoopBody_run_next_edge store t t' blocks n c hst)
  · intro n d t t' hn hst
    rw [headLoopBody_run_done store t t' blocks n d hst]
    exact hn

end

end EthCLSpecs.Proofs.Heze
