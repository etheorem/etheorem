import EthCLSpecs.Gloas.ForkChoice
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.StateFree

/-!
# `EthCLSpecs.Proofs.Gloas.AttestationScore`: the score is a sum of balances

`get_attestation_score(store, node, state)` (phase0 `fork-choice.md:320`, unchanged in
Gloas) sums the effective balance of the active, unslashed validators whose latest message
supports a descendant of `node`. A validator with no message, or in
`equivocating_indices`, adds nothing. `EthCLSpecs.Gloas.getAttestationScore` folds this sum
with `checkedAdd`, because pyspec's `Gwei(sum(...))` raises past `2^64`.

This module restates the fold. `supports` is the test of one index: a latest message that
is not an equivocator's, and whose supported node `isAncestor` puts under `node`.
`getAttestationScore_run_ok` then states the contract. A successful run keeps the runner
state and returns the `Nat` sum of the balances of the counted indices. The checked fold
makes the `toNat` exact.

`supports` reads no runner state (`supports_stateFree`). So `supportsVal`, its value at the
store itself, is the value at every runner state.

The theorems take the state as a plain value and pass the score its uncached box
`pureState state`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs (ForkChoiceStoreRun run_pure run_bind_eq_ok StateFree
  toNat_add_of_not_lt pureState)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedAdd)
open scoped EthCLLib.Spec
open EthCLSpecs.Gloas (Preset Store State BeaconState ForkChoiceNode Gwei ValidatorIndex
  getAttestationScore getSupportedNode isAncestor getAncestor getParentPayloadStatus
  getActiveValidatorIndices currentEpochOf)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- The test of the score fold at one unslashed index `i`. The index counts when it has a
latest message, is not an equivocator, and the supported node of its message is under
`node`. -/
def supports (store : Store map) (node : ForkChoiceNode) (i : ValidatorIndex) :
    ForkChoiceStoreRun (Store map) Bool :=
  match FcMap.lookup store.latestMessages i with
  | none => pure false
  | some lm =>
    if store.equivocatingIndices.contains i then pure false
    else do
      let supported ← getSupportedNode (StoreTransition := ForkChoiceStoreRun (Store map))
        store lm
      isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store supported node

/-- `supports` reads `store` and not the runner state. -/
theorem supports_stateFree (store : Store map) (node : ForkChoiceNode) (i : ValidatorIndex) :
    StateFree (supports store node i) := by
  unfold supports
  simp only [getSupportedNode, isAncestor, getAncestor, getParentPayloadStatus]
  free_solve

/-- The value of `supports`, from a run at `store`. A failed run gives `false`. -/
def supportsVal (store : Store map) (node : ForkChoiceNode) (i : ValidatorIndex) : Bool :=
  match (supports store node i).run store with
  | .ok (b, _) => b
  | .error _ => false

/-- A successful run of `supports` keeps the runner state and returns `supportsVal`. -/
theorem supports_run_ok (store : Store map) (node : ForkChoiceNode) (i : ValidatorIndex)
    {t t' : Store map} {b : Bool} (h : (supports store node i).run t = .ok (b, t')) :
    t' = t ∧ supportsVal store node i = b := by
  obtain ⟨ht, hall⟩ := (supports_stateFree store node i).run_eq h
  refine ⟨ht, ?_⟩
  simp only [supportsVal, hall store]

/-- The effective balance of validator `i` of `state`. -/
abbrev bal (state : State) (i : ValidatorIndex) : Gwei :=
  ((sszGet state validators)[i.toNat]!).effectiveBalance

/-- Whether `state` has slashed validator `i`. -/
abbrev slashedB (state : State) (i : ValidatorIndex) : Bool :=
  ((sszGet state validators)[i.toNat]!).slashed

/-- One step of the score fold, written with `supports`. -/
def scoreStep (store : Store map) (node : ForkChoiceNode) (state : State) (acc : Gwei)
    (i : ValidatorIndex) : ForkChoiceStoreRun (Store map) Gwei :=
  if slashedB state i then pure acc
  else do
    let b ← supports store node i
    if b then checkedAdd acc (bal state i) "get_attestation_score: sum"
    else pure acc

/-- The score is the fold of `scoreStep` over the active indices. -/
theorem getAttestationScore_eq (store : Store map) (node : ForkChoiceNode)
    (state : BeaconState) :
    getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map)) store node
        (pureState state) =
      (getActiveValidatorIndices (pureState state) (currentEpochOf (pureState state))).foldlM
        (scoreStep store node (pureState state)) 0 := by
  simp only [getAttestationScore]
  congr 1
  funext acc i
  simp only [scoreStep, supports, slashedB, bal]
  split
  · rfl
  · cases hl : FcMap.lookup store.latestMessages i with
    | none => simp
    | some lm =>
      by_cases he : i ∈ store.equivocatingIndices
      · simp [he]
      · simp [he]

/-- Whether the score counts index `i`: unslashed, and `supports` holds. -/
def counted (store : Store map) (node : ForkChoiceNode) (state : State) (i : ValidatorIndex) :
    Bool :=
  !slashedB state i && supportsVal store node i

/-- The `Nat` sum of the effective balances of a list of indices. -/
def balanceTotal (state : State) (l : List ValidatorIndex) : Nat :=
  l.foldr (fun i acc => (bal state i).toNat + acc) 0

/-- One successful step keeps the runner state and adds the balance of a counted index. -/
theorem scoreStep_run_ok (store : Store map) (node : ForkChoiceNode) (state : BeaconState)
    (acc : Gwei) (i : ValidatorIndex) {t t' : Store map} {w : Gwei}
    (h : (scoreStep store node (pureState state) acc i).run t = .ok (w, t')) :
    t' = t ∧ w.toNat = acc.toNat +
      (if counted store node (pureState state) i then (bal (pureState state) i).toNat
        else 0) := by
  unfold scoreStep at h
  by_cases hs : slashedB (pureState state) i
  · rw [if_pos hs, run_pure] at h
    injection h with h
    injection h with h1 h2
    subst h1 h2
    simp [counted, hs]
  · rw [if_neg hs] at h
    obtain ⟨b, t1, hsup, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨ht1, hval⟩ := supports_run_ok store node i hsup
    subst ht1
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, run_pure] at hrest
      injection hrest with hrest
      injection hrest with h1 h2
      subst h1 h2
      simp [counted, hs, hval]
    | true =>
      simp only [if_true, checkedAdd] at hrest
      split at hrest
      · simp [EthCLLib.Proofs.ForkChoiceStoreRun.throwArithmetic_run] at hrest
      · rename_i hno
        rw [run_pure] at hrest
        injection hrest with hrest
        injection hrest with h1 h2
        subst h1 h2
        simp [counted, hs, hval, toNat_add_of_not_lt _ _ hno]

/-- A successful fold keeps the runner state and adds the balances of the counted indices. -/
theorem scoreFold_run_ok (store : Store map) (node : ForkChoiceNode) (state : BeaconState) :
    ∀ (l : List ValidatorIndex) (acc : Gwei) (t t' : Store map) (w : Gwei),
      (l.foldlM (scoreStep store node (pureState state)) acc).run t = .ok (w, t') →
      t' = t ∧ w.toNat = acc.toNat +
        balanceTotal (pureState state) (l.filter (counted store node (pureState state))) := by
  intro l
  induction l with
  | nil =>
    intro acc t t' w h
    rw [List.foldlM_nil, run_pure] at h
    injection h with h
    injection h with h1 h2
    subst h1 h2
    simp [balanceTotal]
  | cons i is ih =>
    intro acc t t' w h
    rw [List.foldlM_cons] at h
    obtain ⟨a, t1, hstep, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    obtain ⟨ht1, ha⟩ := scoreStep_run_ok store node state acc i hstep
    rw [ht1] at hrest
    obtain ⟨ht', hw⟩ := ih a t t' w hrest
    refine ⟨ht', ?_⟩
    rw [hw, ha]
    by_cases hc : counted store node (pureState state) i
    · simp [hc, balanceTotal]; omega
    · simp [hc]

/-- The contract of `get_attestation_score`. A successful run keeps the runner state and
returns the `Nat` sum of the effective balances of the active indices that `counted`
keeps. A run past `2^64` raises instead, so the `toNat` is exact. -/
@[characterizes EthCLSpecs.Gloas.getAttestationScore]
theorem getAttestationScore_run_ok (store : Store map) (node : ForkChoiceNode)
    (state : BeaconState) {t t' : Store map} {w : Gwei}
    (h : (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
      store node (pureState state)).run t = .ok (w, t')) :
    t' = t ∧ w.toNat = balanceTotal (pureState state)
      ((getActiveValidatorIndices (pureState state)
          (currentEpochOf (pureState state))).toList.filter
        (counted store node (pureState state))) := by
  rw [getAttestationScore_eq, ← Array.foldlM_toList] at h
  have := scoreFold_run_ok store node state _ 0 t t' w h
  simpa using this

end

end EthCLSpecs.Proofs.Gloas
