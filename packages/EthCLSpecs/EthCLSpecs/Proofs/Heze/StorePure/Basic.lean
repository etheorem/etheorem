import EthCLLib.Proofs.Run
import EthCLLib.Proofs.LawfulFcMap
import EthCLSpecs.Heze.ForkChoice

/-!
# `EthCLSpecs.Proofs.Heze.StorePure.Basic`: the store holds only uncached boxes

A fork-choice store holds states in two maps, `blockStates` and `checkpointStates`. A state
there is a box (`SSZ.Box`), and a box has two flavours: cached and uncached. `StorePure s`
says that every state in either map is `pureState` of a plain value. Under it, a theorem
about a stored state can bind the plain value `v : BeaconState` and name the box
`pureState v`, as `SPECS_ARCHITECTURE.md` §11.1.1 asks.

The fields are stated over the map's own values: a lookup is `o.map pureState` for some
`o : Option BeaconState`. So no field binds a box, and the plain-value check of the proof
coverage needs no marker for them. `BlockStatesPure s` is the `blockStates` half alone.

`Proofs/Heze/StorePure.lean` proves that the anchor store meets `StorePure` and that every
handler keeps it. This module holds only the predicates and the lookup lemmas.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Store BeaconState Root Checkpoint)

section
variable [EthCLSpecs.Heze.Preset] [HasherTag] {map : MapKind} [FcMap map]

/-- Every state in `blockStates` is the uncached box of a plain value. `SlotInv` carries
this half alone, because only `checkpointStates` needs a second map law. -/
def BlockStatesPure (s : Store map) : Prop :=
  ∀ k : Root, ∃ o : Option BeaconState, FcMap.lookup s.blockStates k = o.map pureState

/-- Every state that the store holds is the uncached box of a plain value. -/
structure StorePure (s : Store map) : Prop where
  blockStates : BlockStatesPure s
  checkpointStates : ∀ c : Checkpoint, ∃ o : Option BeaconState,
    FcMap.lookup s.checkpointStates c = o.map pureState

/-- A state in `blockStates` at `k` is `pureState` of a value. The form for a caller that
knows only that the lookup succeeds. -/
theorem BlockStatesPure.lookup {s : Store map} (h : BlockStatesPure s) (k : Root)
    (hk : (FcMap.lookup s.blockStates k).isSome = true) :
    ∃ v : BeaconState, FcMap.lookup s.blockStates k = some (pureState v) := by
  obtain ⟨o, ho⟩ := h k
  cases o with
  | none =>
    rw [ho] at hk
    cases hk
  | some v => exact ⟨v, ho⟩

/-- A state that the store holds at `k` is `pureState` of a value. -/
theorem StorePure.blockStates_some {s : Store map} (h : StorePure s) (k : Root)
    (hk : (FcMap.lookup s.blockStates k).isSome = true) :
    ∃ v : BeaconState, FcMap.lookup s.blockStates k = some (pureState v) :=
  h.blockStates.lookup k hk

/-- A checkpoint state that the store holds at `c` is `pureState` of a value. -/
theorem StorePure.checkpointStates_some {s : Store map} (h : StorePure s) (c : Checkpoint)
    (hc : (FcMap.lookup s.checkpointStates c).isSome = true) :
    ∃ v : BeaconState, FcMap.lookup s.checkpointStates c = some (pureState v) := by
  obtain ⟨o, ho⟩ := h.checkpointStates c
  cases o with
  | none =>
    rw [ho] at hc
    cases hc
  | some v => exact ⟨v, ho⟩

end

end EthCLSpecs.Proofs.Heze
