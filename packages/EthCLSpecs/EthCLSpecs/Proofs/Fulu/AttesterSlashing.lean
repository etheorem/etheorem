import EthCLSpecs.Fulu.Operations

/-!
# `EthCLSpecs.Proofs.Fulu.AttesterSlashing`: the slashing test of two attestation data

`is_slashable_attestation_data` (`electra/beacon-chain.md`, inherited by Fulu) accepts two
attestation data in two cases:

- a double vote: two data with different roots and one target epoch;
- a surround vote: the first vote surrounds the second. Its source is earlier, and its target
  is later.

`isSlashableAttestationData_iff` states the test as these two cases. The double vote compares
roots. So two different data with one target epoch are a double vote, or the two
data are an SSZ root collision (`isSlashableAttestationData_of_ne`). The Heze file names the
collision `HtrCollision`. This file writes it out, so that it imports nothing from Heze.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset AttestationData isSlashableAttestationData)

variable [Preset] [HasherTag]

/-- The slashing test of two attestation data: a double vote (different roots, one target
epoch) or a surround vote. -/
@[characterizes EthCLSpecs.Fulu.isSlashableAttestationData]
theorem isSlashableAttestationData_iff (d₁ d₂ : AttestationData) :
    isSlashableAttestationData d₁ d₂ = true ↔
      (htr d₁ ≠ htr d₂ ∧ d₁.target.epoch = d₂.target.epoch) ∨
      (d₁.source.epoch < d₂.source.epoch ∧ d₂.target.epoch < d₁.target.epoch) := by
  simp [isSlashableAttestationData]

/-- Two different data with one target epoch are a double vote, or their roots collide. -/
theorem isSlashableAttestationData_of_ne (d₁ d₂ : AttestationData) (h : d₁ ≠ d₂)
    (he : d₁.target.epoch = d₂.target.epoch) :
    (∃ x y : AttestationData, x ≠ y ∧ htr x = htr y) ∨
      isSlashableAttestationData d₁ d₂ = true := by
  by_cases hr : htr d₁ = htr d₂
  · exact Or.inl ⟨d₁, d₂, h, hr⟩
  · exact Or.inr ((isSlashableAttestationData_iff d₁ d₂).mpr (Or.inl ⟨hr, he⟩))

end EthCLSpecs.Proofs.Fulu
