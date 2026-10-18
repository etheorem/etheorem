import EthCLSpecs.Fulu.Operations

/-!
# `EthCLSpecs.Proofs.Fulu.AttesterSlashing`: the slashing test of two attestation data

`is_slashable_attestation_data` (`electra/beacon-chain.md`, inherited by Fulu) accepts two
attestation data in two cases:

- a double vote: two different data with one target epoch;
- a surround vote: the first vote surrounds the second. Its source is earlier, and its target
  is later.

`isSlashableAttestationData_iff` states the test as these two cases. The double vote compares
the fields of the two data, as the pyspec's `data_1 != data_2` does. So two different data
with one target epoch are a double vote (`isSlashableAttestationData_of_ne`).

The container derives `BEq` field by field. `LawfulBEq` for `Checkpoint` and
`AttestationData` turns `d₁ != d₂` into `d₁ ≠ d₂`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Checkpoint AttestationData isSlashableAttestationData)

deriving instance ReflBEq, LawfulBEq for Checkpoint
deriving instance ReflBEq, LawfulBEq for AttestationData

variable [Preset]

/-- The slashing test of two attestation data: a double vote (different data, one target
epoch) or a surround vote. -/
@[characterizes EthCLSpecs.Fulu.isSlashableAttestationData]
theorem isSlashableAttestationData_iff (d₁ d₂ : AttestationData) :
    isSlashableAttestationData d₁ d₂ = true ↔
      (d₁ ≠ d₂ ∧ d₁.target.epoch = d₂.target.epoch) ∨
      (d₁.source.epoch < d₂.source.epoch ∧ d₂.target.epoch < d₁.target.epoch) := by
  simp [isSlashableAttestationData]

/-- Two different data with one target epoch are a double vote. -/
theorem isSlashableAttestationData_of_ne (d₁ d₂ : AttestationData) (h : d₁ ≠ d₂)
    (he : d₁.target.epoch = d₂.target.epoch) :
    isSlashableAttestationData d₁ d₂ = true :=
  (isSlashableAttestationData_iff d₁ d₂).mpr (Or.inl ⟨h, he⟩)

end EthCLSpecs.Proofs.Fulu
