import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Proofs.Gloas.AttesterSlashing`: the slashing test of two attestation data

Gloas inherits `isSlashableAttestationData` from Fulu, so the Gloas constant is a separate
elaboration of the same test. This file states the two Fulu theorems
(`Proofs/Fulu/AttesterSlashing.lean`) at the Gloas constant: the test is a double vote or a
surround vote, and two different data with one target epoch are a double vote.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLSpecs.Gloas (Preset Checkpoint AttestationData isSlashableAttestationData)

deriving instance ReflBEq, LawfulBEq for Checkpoint
deriving instance ReflBEq, LawfulBEq for AttestationData

variable [Preset]

/-- The slashing test of two attestation data: a double vote (different data, one target
epoch) or a surround vote. -/
@[characterizes EthCLSpecs.Gloas.isSlashableAttestationData]
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

end EthCLSpecs.Proofs.Gloas
