import EthCLSpecs.Proofs.Heze.JustificationAndFinalization

/-!
# `EthCLSpecs.Proofs.Heze.JustificationBits`: what the weigh step does to the bits

`weigh_justification_and_finalization` shifts the four justification bits by one. Then it sets
bit 1 when the target of the previous epoch passes, and bit 0 when the target of the current
epoch passes (`weighBits`). So after the step, bit 0 records the current test, bit 1 records
the previous test or the old bit 0, and bits 2 and 3 are the old bits 1 and 2
(`weighBits_get`).

Read at the end of epoch `E`, bit `k` is the test of epoch `E - k`. The FFG refinement
(`FFGRefines.lean`) keeps this reading along a run.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec

/-- The bits after the weigh step: the shift, then bit 1 for the previous test `jp`, then
bit 0 for the current test `jc`. -/
def weighBits (b : Bitvector 4) (jp jc : Bool) : Bitvector 4 :=
  let bits1 : Bitvector 4 := { data := b.data <<< 1 }
  let bits2 := if jp then bitSet bits1 1 true else bits1
  if jc then bitSet bits2 0 true else bits2

/-- The four bits after the weigh step. -/
theorem weighBits_get (b : Bitvector 4) (jp jc : Bool) :
    bitGet (weighBits b jp jc) 0 = jc ∧ bitGet (weighBits b jp jc) 1 = (jp || bitGet b 0) ∧
    bitGet (weighBits b jp jc) 2 = bitGet b 1 ∧ bitGet (weighBits b jp jc) 3 = bitGet b 2 := by
  obtain ⟨⟨f⟩⟩ := b
  revert f
  cases jp <;> cases jc <;> decide

end EthCLSpecs.Proofs.Heze
