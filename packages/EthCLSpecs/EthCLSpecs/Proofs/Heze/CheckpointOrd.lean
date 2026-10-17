import EthCLSpecs.Heze.ForkChoice
import EthCLLib.Proofs.LawfulFcMap

/-!
# `EthCLSpecs.Proofs.Heze.CheckpointOrd`: the order on `Checkpoint` is lawful

The fork-choice store keys `checkpointStates` by `Checkpoint`. `treeMap` meets the map laws
(`LawfulFcMap`) at a key type whose `compare` is a transitive order that returns `.eq` only
on equal keys (`instLawfulFcMapTreeMap`). This module proves both facts for the `Ord`
instance that the container deriving handler emits for `Checkpoint`.

The derived `compare` reads the epoch, then the root: `(compare e e').then
((compare r r').then .eq)`. That is extensionally the core comparator
`compareLex (compareOn epoch) (compareOn root)` (`Checkpoint.compare_eq_compareLex`). Core
proves transitivity for that comparator. The root order is lawful by
`instTransOrdVectorUInt8` and `instLawfulEqOrdVectorUInt8` (`FiniteMap.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Heze (Preset Checkpoint)

section
variable [Preset]

/-- The derived `compare` on `Checkpoint` is the lexicographic comparator on the epoch and
then the root. -/
theorem Checkpoint.compare_eq_compareLex :
    (compare : Checkpoint → Checkpoint → Ordering)
      = compareLex (compareOn (·.epoch)) (compareOn (·.root)) := by
  funext a b
  cases a
  cases b
  rename_i e1 r1 e2 r2
  show EthCLSpecs.Heze.instOrdCheckpoint.ord _ _ = _
  unfold EthCLSpecs.Heze.instOrdCheckpoint.ord
  simp only [compareLex, compareOn]
  -- The derived comparator ends the chain with `.then .eq`, which is the identity.
  cases compare r1 r2 <;> rfl

/-- The order on `Checkpoint` is transitive. Core proves it for the lexicographic
comparator, and `Checkpoint.compare_eq_compareLex` moves it to the derived one. -/
instance instTransOrdCheckpoint : Std.TransOrd Checkpoint :=
  show Std.TransCmp (compare : Checkpoint → Checkpoint → Ordering) from
    Checkpoint.compare_eq_compareLex ▸ inferInstance

/-- The order on `Checkpoint` returns `.eq` only on equal checkpoints: both the epochs and
the roots compare equal. -/
instance instLawfulEqOrdCheckpoint : Std.LawfulEqOrd Checkpoint where
  eq_of_compare {a b} h := by
    rw [Checkpoint.compare_eq_compareLex] at h
    simp only [compareLex_eq_eq, compareOn] at h
    cases a
    cases b
    simp only at h
    rw [Std.LawfulEqOrd.eq_of_compare h.1, Std.LawfulEqOrd.eq_of_compare h.2]

/-- So `treeMap` meets the map laws at `Checkpoint`. -/
example : EthCLLib.Proofs.LawfulFcMap EthCLLib.Spec.treeMap Checkpoint := inferInstance

end

end EthCLSpecs.Proofs.Heze
