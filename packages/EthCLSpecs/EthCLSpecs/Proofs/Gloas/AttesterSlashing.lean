import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Proofs.Gloas.AttesterSlashing`: the slashing test of two attestation data

Gloas inherits `isSlashableAttestationData` from Fulu, so the Gloas constant is a separate
elaboration of the same test. This file states the two Fulu theorems
(`Proofs/Fulu/AttesterSlashing.lean`) at the Gloas constant: the test is a double vote or a
surround vote, and two different data with one target epoch are a double vote or an SSZ root
collision. The collision is written out, so that this file imports nothing from Heze.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLSpecs.Gloas (Preset AttestationData isSlashableAttestationData)

variable [Preset] [HasherTag]

/-- The slashing test of two attestation data: a double vote (different roots, one target
epoch) or a surround vote. -/
@[characterizes EthCLSpecs.Gloas.isSlashableAttestationData]
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

end EthCLSpecs.Proofs.Gloas
