import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.IsPayloadInclusionListSatisfied`: the FOCIL read helper

Heze's `isPayloadInclusionListSatisfied` is the read side of the FOCIL gate.
It looks up the recorded inclusion-list satisfaction bit at `root`, then
returns that bit only when the payload is verified. An unverified payload
returns `false`. A missing record is the spec's membership `assert`.

This module states the complete `.run` equation at
`ForkChoiceStoreRun (Store map)`. The explicit argument `store` is the map
that is read. `runnerStore` is the runner state. Success leaves
`runnerStore` unchanged. A reject returns the error alone and has no
post-state.

The lookup precedes `isPayloadVerified`. That order is the spec's: the
membership assert fires even when the payload is unverified. The four
corollaries name the missing-record reject, an unverified recorded value,
a recorded `false`, and a recorded `true` with a verified payload.

The helper does not write the store. Verdict production lives in
`recordPayloadInclusionListSatisfaction`. Pairing of `payloads[root]` with
the satisfaction entry is a later handler postcondition.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Store isPayloadInclusionListSatisfied isPayloadVerified Root)

/-- Complete `.run` equation of `isPayloadInclusionListSatisfied` at
`ForkChoiceStoreRun (Store map)`. A missing satisfaction key is the spec's
membership assert. A recorded value is returned only when the payload is
verified. Otherwise the result is `false`. Success pairs that Boolean with
the incoming `runnerStore`. -/
@[characterizes EthCLSpecs.Heze.isPayloadInclusionListSatisfied]
theorem isPayloadInclusionListSatisfied_run
    {map : MapKind} [Preset] [HasherTag] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      (isPayloadInclusionListSatisfied
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore =
        match FcMap.lookup store.payloadInclusionListSatisfaction root with
        | none =>
            .error (.assert "root in store.payload_inclusion_list_satisfaction")
        | some satisfied =>
            .ok (
              if isPayloadVerified store root then satisfied else false,
              runnerStore) := by
  intro store runnerStore root
  simp [isPayloadInclusionListSatisfied, FcMap.getOrAssert]
  cases hlookup : FcMap.lookup store.payloadInclusionListSatisfaction root with
  | none =>
    rfl
  | some satisfied =>
    by_cases hverified : isPayloadVerified store root = true
    · simp [hverified]
      rfl
    · simp [hverified]
      rfl

/-- A missing satisfaction record is the spec's membership assert. -/
theorem isPayloadInclusionListSatisfied_run_error_of_missing_record
    {map : MapKind} [Preset] [HasherTag] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadInclusionListSatisfaction root = none →
      (isPayloadInclusionListSatisfied
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .error (.assert "root in store.payload_inclusion_list_satisfaction") := by
  intro store runnerStore root hlookup
  rw [isPayloadInclusionListSatisfied_run]
  simp [hlookup]

/-- A recorded satisfaction bit with an unverified payload returns `false`.
The runner state is unchanged. -/
theorem isPayloadInclusionListSatisfied_run_eq_false_of_unverified
    {map : MapKind} [Preset] [HasherTag] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root) (satisfied : Bool),
      FcMap.lookup store.payloadInclusionListSatisfaction root = some satisfied →
      isPayloadVerified store root = false →
      (isPayloadInclusionListSatisfied
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (false, runnerStore) := by
  intro store runnerStore root satisfied hlookup hverified
  rw [isPayloadInclusionListSatisfied_run]
  simp [hlookup, hverified]

/-- A recorded `false` returns `false`, whether or not the payload is
verified. The runner state is unchanged. -/
theorem isPayloadInclusionListSatisfied_run_eq_false_of_recorded_unsatisfied
    {map : MapKind} [Preset] [HasherTag] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadInclusionListSatisfaction root = some false →
      (isPayloadInclusionListSatisfied
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (false, runnerStore) := by
  intro store runnerStore root hlookup
  rw [isPayloadInclusionListSatisfied_run]
  simp [hlookup]

/-- A recorded `true` with a verified payload returns `true`. The runner
state is unchanged. -/
theorem isPayloadInclusionListSatisfied_run_eq_true_of_recorded_satisfied
    {map : MapKind} [Preset] [HasherTag] [FcMap map] :
    ∀ (store runnerStore : Store map) (root : Root),
      FcMap.lookup store.payloadInclusionListSatisfaction root = some true →
      isPayloadVerified store root = true →
      (isPayloadInclusionListSatisfied
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store root).run runnerStore
        = .ok (true, runnerStore) := by
  intro store runnerStore root hlookup hverified
  rw [isPayloadInclusionListSatisfied_run]
  simp [hlookup, hverified]

end EthCLSpecs.Proofs.Heze
