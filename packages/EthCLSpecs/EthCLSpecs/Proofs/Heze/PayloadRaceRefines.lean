import EthCLSpecs.Proofs.Heze.AttestationScore
import EthCLSpecs.Proofs.Heze.HeadAvoidsFull
import EthCLSpecs.Proofs.Heze.PayloadRace

/-!
# `EthCLSpecs.Proofs.Heze.PayloadRaceRefines`: the score is the race weight

`PayloadRace.lean` models the race between the EMPTY and the FULL node of a block `r` with
an abstract weight, `sideWeight`. This module ties that weight to the executable score.

`storeSide store r` gives each validator index the side of `r` that the store supports. The
side is `full` when the latest message is under `full r`, and `empty` when it is under
`empty r`. Otherwise the side is `neither`. A validator with no message, or an
equivocator, sits on `neither`. `raceValidators state` lists the active unslashed
validators of `state`, with their effective balances.

`score_full_refines` and `score_empty_refines` state the result. A successful score run of
`full r` or `empty r` returns `sideWeight` of that side. Honesty and vote slots are free
parameters of `raceValidators`, because `sideWeight` reads neither.

The EMPTY equation needs exclusivity (`supportsVal_full_empty_exclusive`). One supported
node is never under both children of `pending r`. `is_ancestor` (`gloas/fork-choice.md:355`)
reads the same block and walks `get_ancestor` (`:337`) to the same slot for both. The walk
returns one status, and `FULL ≠ EMPTY`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun run_bind_eq_ok pureState)
open EthCLLib.Spec (HasherTag MapKind FcMap)
open EthCLSpecs.Heze (Preset Store State BeaconState Root ForkChoiceNode Gwei ValidatorIndex
  getAttestationScore isAncestor getActiveValidatorIndices currentEpochOf)
open EthCLSpecs.Proofs.Heze.PayloadRace (Side Validator sideWeight balanceSum)

section
variable {map : MapKind} [Preset] [HasherTag] [FcMap map]

/-- One supported node `n` is never under both children of `pending r`. -/
theorem isAncestor_full_empty_exclusive (store : Store map) (n : ForkChoiceNode) (r : Root)
    {t t₁ t₂ : Store map}
    (h₁ : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n
      (ForkChoiceNode.full r)).run t = .ok (true, t₁))
    (h₂ : (isAncestor (StoreTransition := ForkChoiceStoreRun (Store map)) store n
      (ForkChoiceNode.empty r)).run t = .ok (true, t₂)) : False := by
  simp only [isAncestor, ForkChoiceNode.full, ForkChoiceNode.empty] at h₁ h₂
  -- Both runs read `blocks[r]` and walk to the same slot, so they meet the same block and
  -- the same ancestor.
  obtain ⟨b₁, u₁, hb₁, h₁⟩ := run_bind_eq_ok _ _ _ _ h₁
  obtain ⟨b₂, u₂, hb₂, h₂⟩ := run_bind_eq_ok _ _ _ _ h₂
  rw [hb₁] at hb₂
  injection hb₂ with hb₂
  injection hb₂ with hb hu
  subst hb hu
  obtain ⟨a₁, v₁, ha₁, h₁⟩ := run_bind_eq_ok _ _ _ _ h₁
  obtain ⟨a₂, v₂, ha₂, h₂⟩ := run_bind_eq_ok _ _ _ _ h₂
  rw [ha₁] at ha₂
  injection ha₂ with ha₂
  injection ha₂ with ha hv
  subst ha hv
  by_cases hc : (a₁.root != r) = true
  · rw [if_pos hc] at h₁
    cases h₁
  · rw [if_neg hc] at h₁ h₂
    injection h₁ with h₁
    injection h₁ with e1
    injection h₂ with h₂
    injection h₂ with e2
    simp only [Bool.or_eq_true, beq_iff_eq] at e1 e2
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact payloadStatus_empty_ne_full (e2.symm.trans e1)
    · exact payloadStatus_empty_ne_pending e2
    · exact payloadStatus_full_ne_pending e1
    · exact payloadStatus_full_ne_pending e1

/-- No index supports both children of `pending r`. -/
theorem supportsVal_full_empty_exclusive (store : Store map) (r : Root) (i : ValidatorIndex)
    (h₁ : supportsVal store (ForkChoiceNode.full r) i = true)
    (h₂ : supportsVal store (ForkChoiceNode.empty r) i = true) : False := by
  unfold supportsVal at h₁ h₂
  split at h₁ <;> rename_i b₁ s₁ hr₁
  · split at h₂ <;> rename_i b₂ s₂ hr₂
    · subst h₁ h₂
      unfold supports at hr₁ hr₂
      split at hr₁
      · cases hr₁
      · rename_i lm hl
        rw [hl] at hr₂
        simp only at hr₂
        split at hr₁
        · cases hr₁
        · rename_i he
          rw [if_neg he] at hr₂
          obtain ⟨n₁, u₁, hn₁, hr₁⟩ := run_bind_eq_ok _ _ _ _ hr₁
          obtain ⟨n₂, u₂, hn₂, hr₂⟩ := run_bind_eq_ok _ _ _ _ hr₂
          rw [hn₁] at hn₂
          injection hn₂ with hn₂
          injection hn₂ with hn hu
          subst hn hu
          exact isAncestor_full_empty_exclusive store n₁ r hr₁ hr₂
    · simp at h₂
  · simp at h₁

/-- The side of `r` that the store gives validator index `n`. -/
def storeSide (store : Store map) (r : Root) (n : Nat) : Side :=
  if supportsVal store (ForkChoiceNode.full r) (UInt64.ofNat n) then .full
  else if supportsVal store (ForkChoiceNode.empty r) (UInt64.ofNat n) then .empty
  else .neither

/-- The validators of the race: the active unslashed indices of `state`, with their
effective balances. `honestOf` and `votesOf` give the two fields that the store does not
know. -/
def raceValidators (state : State) (honestOf : ValidatorIndex → Bool)
    (votesOf : ValidatorIndex → Nat → Bool) : List Validator :=
  ((getActiveValidatorIndices state (currentEpochOf state)).toList.filter
      (fun i => !slashedB state i)).map
    fun i => ⟨i.toNat, (bal state i).toNat, honestOf i, votesOf i⟩

/-- The race weight of one side, over the validators of a list of indices, is the sum of
the balances of the unslashed indices whose side the test `q` picks. -/
theorem sideSum_eq (state : BeaconState) (f : Nat → Side) (side : Side)
    (q : ValidatorIndex → Bool) (hq : ∀ i : ValidatorIndex, f i.toNat = side ↔ q i = true)
    (honestOf : ValidatorIndex → Bool) (votesOf : ValidatorIndex → Nat → Bool) :
    ∀ l : List ValidatorIndex,
      balanceSum ((((l.filter fun i => !slashedB (pureState state) i).map
          fun i => (⟨i.toNat, (bal (pureState state) i).toNat, honestOf i, votesOf i⟩ :
            Validator))).filter
          fun v => decide (f v.index = side))
        = balanceTotal (pureState state)
          (l.filter fun i => !slashedB (pureState state) i && q i) := by
  intro l
  induction l with
  | nil => rfl
  | cons i is ih =>
    by_cases hs : slashedB (pureState state) i
    · simp [hs, ih]
    · by_cases hqi : q i
      · have hf : f i.toNat = side := (hq i).2 hqi
        simp [hs, hqi, hf, balanceSum, balanceTotal] at ih ⊢
        rw [ih]
      · have hf : f i.toNat ≠ side := fun h => hqi ((hq i).1 h)
        simp [hs, hqi, hf, ih]

/-- The score of `full r` is the race weight of FULL. -/
theorem score_full_refines (store : Store map) (state : BeaconState) (r : Root)
    (honestOf : ValidatorIndex → Bool) (votesOf : ValidatorIndex → Nat → Bool)
    {t t' : Store map} {w : Gwei}
    (h : (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
      store (ForkChoiceNode.full r) (pureState state)).run t = .ok (w, t')) :
    w.toNat = sideWeight (raceValidators (pureState state) honestOf votesOf)
      (fun v => storeSide store r v.index) .full := by
  rw [(getAttestationScore_run_ok store _ state h).2]
  unfold sideWeight raceValidators
  rw [sideSum_eq state (storeSide store r) .full
    (supportsVal store (ForkChoiceNode.full r))]
  · rfl
  · intro i
    simp only [storeSide, UInt64.ofNat_toNat]
    cases hf : supportsVal store (ForkChoiceNode.full r) i <;>
      cases he : supportsVal store (ForkChoiceNode.empty r) i <;> simp

/-- The score of `empty r` is the race weight of EMPTY. -/
theorem score_empty_refines (store : Store map) (state : BeaconState) (r : Root)
    (honestOf : ValidatorIndex → Bool) (votesOf : ValidatorIndex → Nat → Bool)
    {t t' : Store map} {w : Gwei}
    (h : (getAttestationScore (StoreTransition := ForkChoiceStoreRun (Store map))
      store (ForkChoiceNode.empty r) (pureState state)).run t = .ok (w, t')) :
    w.toNat = sideWeight (raceValidators (pureState state) honestOf votesOf)
      (fun v => storeSide store r v.index) .empty := by
  rw [(getAttestationScore_run_ok store _ state h).2]
  unfold sideWeight raceValidators
  rw [sideSum_eq state (storeSide store r) .empty
    (supportsVal store (ForkChoiceNode.empty r))]
  · rfl
  · intro i
    simp only [storeSide, UInt64.ofNat_toNat]
    by_cases hf : supportsVal store (ForkChoiceNode.full r) i
    · have hne : supportsVal store (ForkChoiceNode.empty r) i = false := by
        cases he : supportsVal store (ForkChoiceNode.empty r) i
        · rfl
        · exact (supportsVal_full_empty_exclusive store r i hf he).elim
      simp [hf, hne]
    · cases he : supportsVal store (ForkChoiceNode.empty r) i <;> simp [hf]

end

end EthCLSpecs.Proofs.Heze
