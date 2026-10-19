import EthCLSpecs.Proofs.Heze.DriftTotal

/-!
# `EthCLSpecs.Proofs.Heze.DriftExit`: an exit keeps the invariant

`initiate_validator_exit` reserves exit churn for one validator and sets its exit epoch and
its withdrawable epoch (`initiateValidatorExit_run`). This module shows that it keeps
`RunInv` (`RunInv.initiateExit`). The exit enters the exit-churn ledger with the effective
balance at which the validator exits, so the ghost `W` records that balance and the ghost
`tag` records the exit churn.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

omit [HasherTag] in
/-- The registry after a write of one validator, read at an index. -/
theorem getElem?_validators_set (a : BeaconState) (j k : Nat) (v' : Validator)
    (hj : j < a.validators.val.size) :
    (a.validators.set! j v').val[k]? = if j = k then some v' else a.validators.val[k]? := by
  show (a.validators.val.setIfInBounds j v')[k]? = _
  rw [Array.getElem?_setIfInBounds]
  split
  · simp
  · rfl

omit [Preset] [HasherTag] in
/-- The length of a filter is a sum of ones. -/
theorem length_filter_eq_sum {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length = (l.map fun x => if p x then 1 else 0).sum
  | [] => rfl
  | x :: l => by
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases p x <;> simp [length_filter_eq_sum p l] <;> omega

omit [Preset] [HasherTag] in
/-- A sum over the indices below `n` of a summand that changes at `j < n` alone. -/
theorem sum_range_change (f g : Nat → Nat) (j : Nat) :
    ∀ n, j < n → (∀ k, k ≠ j → f k = g k) →
      ((List.range n).map f).sum + g j = ((List.range n).map g).sum + f j
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, he => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hjn : j = n
    · subst hjn
      have hr : ((List.range j).map f).sum = ((List.range j).map g).sum := by
        congr 1
        exact List.map_congr_left fun k hk => he k (by have := List.mem_range.mp hk; omega)
      omega
    · have := sum_range_change f g j n (by omega) he
      rw [he n (Ne.symm hjn)]
      omega

omit [HasherTag] in
/-- A write of one validator from no exit to an exit adds one to the exited count. -/
theorem exitedCount_set (a b : BeaconState) (j : Nat) (hj : j < sizeOf a)
    (hs : sizeOf b = sizeOf a) (ha : exitOf a j = farN) (hb : exitOf b j ≠ farN)
    (he : ∀ k, k ≠ j → exitOf b k = exitOf a k) : exitedCount b = exitedCount a + 1 := by
  unfold exitedCount
  rw [hs, length_filter_eq_sum, length_filter_eq_sum]
  have := sum_range_change (fun i => if decide (exitOf b i ≠ farN) then 1 else 0)
    (fun i => if decide (exitOf a i ≠ farN) then 1 else 0) j (sizeOf a) hj
    (fun k hk => by simp only [he k hk])
  simp only [ha, hb, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
    not_false_eq_true, decide_true] at this
  omega

/-- A validator with an exit epoch `x` and the withdrawable epoch `x + d`. -/
def exitVal (v : Validator) (x d : EthCLSpecs.Heze.Epoch) : Validator :=
  { v with exitEpoch := x, withdrawableEpoch := x + d }

/-- A state with its registry replaced. -/
def withValidators (a : BeaconState) (vs : SizzLean.Repr.SSZList Validator
    EthCLSpecs.Heze.Const.validatorRegistryLimit) : BeaconState :=
  { a with validators := vs }

/-- The reads of a state after a write of one validator `v'` at `j`, over the reads of the
state before. -/
structure OneWrite (a b : BeaconState) (j : Nat) (v v' : Validator) : Prop where
  hj : j < sizeOf a
  get : ∀ k, b.validators.val[k]? = if j = k then some v' else a.validators.val[k]?
  old : a.validators.val[j]? = some v
  bal : b.balances = a.balances
  size : sizeOf b = sizeOf a

omit [HasherTag] in
/-- A read that the write keeps at `j` is kept everywhere. -/
theorem OneWrite.read {a b : BeaconState} {j : Nat} {v v' : Validator} (w : OneWrite a b j v v')
    (f : Validator → Nat) (d : Nat) (hf : f v' = f v) (k : Nat) :
    (match b.validators.val[k]? with | some u => f u | none => d) =
      (match a.validators.val[k]? with | some u => f u | none => d) := by
  by_cases hk : j = k
  · subst hk
    rw [w.get j, if_pos rfl, w.old]
    exact hf
  · rw [w.get k, if_neg hk]

omit [HasherTag] in
/-- A read at an index other than `j` is kept. -/
theorem OneWrite.read_ne {a b : BeaconState} {j : Nat} {v v' : Validator} (w : OneWrite a b j v v')
    (f : Validator → Nat) (d : Nat) (k : Nat) (hk : k ≠ j) :
    (match b.validators.val[k]? with | some u => f u | none => d) =
      (match a.validators.val[k]? with | some u => f u | none => d) := by
  rw [w.get k, if_neg (Ne.symm hk)]

omit [HasherTag] in
/-- The read at `j`. -/
theorem OneWrite.read_self {a b : BeaconState} {j : Nat} {v v' : Validator} (w : OneWrite a b j v v')
    (f : Validator → Nat) (d : Nat) :
    (match b.validators.val[j]? with | some u => f u | none => d) = f v' := by
  rw [w.get j, if_pos rfl]

/-- A write of one validator keeps the reads of the total active balance, when it keeps the
slot, the effective balance, and the active gate at the current epoch. -/
theorem OneWrite.acKeep {a b : BeaconState} {j : Nat} {v v' : Validator} (w : OneWrite a b j v v')
    (hslot : b.slot = a.slot) (heb : v'.effectiveBalance = v.effectiveBalance)
    (hact : EthCLSpecs.Heze.isActiveValidator v' (EthCLSpecs.Heze.currentEpochOf (pureState a)) =
      EthCLSpecs.Heze.isActiveValidator v (EthCLSpecs.Heze.currentEpochOf (pureState a))) :
    AcKeep a b := by
  have hc : EthCLSpecs.Heze.currentEpochOf (pureState b) =
      EthCLSpecs.Heze.currentEpochOf (pureState a) := by
    show EthCLSpecs.Heze.computeEpochAtSlot b.slot = EthCLSpecs.Heze.computeEpochAtSlot a.slot
    rw [hslot]
  refine ⟨hslot, w.size, fun k => ?_, fun k _ => ?_⟩
  · unfold acB
    rw [hc, w.get k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, w.old]; exact hact
    · rw [if_neg hk]
  · unfold ebN
    rw [w.get k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, w.old]; dsimp only; rw [heb]
    · rw [if_neg hk]

end

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- The `uint64` epoch arithmetic of the restart epoch. A successful
`compute_activation_exit_epoch` returns the sum `epoch + 1 + MAX_SEED_LOOKAHEAD`
(`computeActivationExitEpoch_eq`). -/
theorem earliest_toNat (a : BeaconState) {act : UInt64}
    (hact : (EthCLSpecs.Heze.computeActivationExitEpoch (EthCLSpecs.Heze.computeEpochAtSlot a.slot)
      : Except StateTransitionError UInt64) = .ok act)
    (h : epochN a + lagN < 2 ^ 64) :
    (umax a.earliestExitEpoch act).toNat = max a.earliestExitEpoch.toNat (epochN a + lagN) := by
  rw [umax_toNat]
  congr 1
  rw [computeActivationExitEpoch_eq] at hact
  split at hact
  · cases hact
  split at hact
  · cases hact
  injection hact with hact
  subst hact
  have hc : (EthCLSpecs.Heze.computeEpochAtSlot a.slot).toNat = epochN a := rfl
  unfold lagN at h ⊢
  rw [UInt64.toNat_add, UInt64.toNat_add, hc, UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **An exit keeps the invariant.** The ghost `W` records the effective balance at which the
validator exits, and `tag` records the exit churn. -/
theorem RunInv.initiateExit {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} (i : ValidatorIndex)
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (hnd : vals.Nodup) (hshape₀ : ShapeOK st₀)
    (h : (EthCLSpecs.Heze.initiateValidatorExit (StateTransition := HezeRun) i).run
      (pureState a) = .ok ((), pureState b))
    (hCl : incN ≤ (exitChurn a).toNat)
    (hCu : (exitChurn a).toNat ≤ CX) (hinc : 0 < incN)
    (hcur : epochN st₀ ≤ epochN a) (hcurE : epochN a ≤ E)
    (hkE : E < epochN st₀ + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat)
    (hsmall : max st₀.earliestExitEpoch.toNat (E + lagN) + (exitedCount a + 1) * maddX +
      Γp * maddP < 2 ^ 62)
    (hc62 : max st₀.exitBalanceToConsume.toNat CX < 2 ^ 62)
    (hmax : ∀ k, k < sizeOf a → maxN a k ≤ maxEBN) (hmax62 : maxEBN < 2 ^ 62) :
    AcKeep a b ∧ ∃ W' tag', RunInv vals st₀ E CX CC b V W' tag' Γp B := by
  obtain ⟨v, hv, hcase⟩ := initiateValidatorExit_run i a b h
  rcases hcase with ⟨-, rfl⟩ | ⟨hfar, act, x, c, hactE, -, hres, hno, rfl⟩
  · exact ⟨AcKeep.refl _, W, tag, I⟩
  -- The names of the step.
  generalize hj : i.toNat = j at hv
  have hjs : j < sizeOf a := (Array.getElem?_eq_some_iff.mp hv).1
  generalize hC : (exitChurn a).toNat = C at hCl hCu
  have hdelay := EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay
  let v' : Validator := exitVal v x EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay
  let b := withValidators (afterExitChurn a v.effectiveBalance x c) (a.validators.set! j v')
  have w : OneWrite a b j v v' := by
    refine ⟨hjs, fun k => getElem?_validators_set a j k v' hjs, hv, rfl, ?_⟩
    show (a.validators.set! j v').val.size = a.validators.val.size
    exact SizzLean.Proofs.sszListSet!_size _ _ _
  show AcKeep a b ∧ ∃ W' tag', RunInv vals st₀ E CX CC b V W' tag' Γp B
  -- The reads that the write keeps.
  have hmx : ∀ k, maxN b k = maxN a k := fun k =>
    w.read (fun u => (EthCLSpecs.Heze.getMaxEffectiveBalance u).toNat) 0 rfl k
  have hcap : ∀ k, capN b k = capN a k := fun k => by
    unfold capN balN
    rw [w.bal, hmx]
  have heb : ∀ k, ebN b k = ebN a k := fun k => w.read (fun u => u.effectiveBalance.toNat) 0 rfl k
  have hact : ∀ k, actOf b k = actOf a k := fun k =>
    w.read (fun u => u.activationEpoch.toNat) 0 rfl k
  have hsl : ∀ k, slashedOf b k = slashedOf a k := fun k => by
    unfold slashedOf
    rw [w.get k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, w.old]; rfl
    · rw [if_neg hk]
  have hexit_ne : ∀ k, k ≠ j → exitOf b k = exitOf a k := fun k hk =>
    w.read_ne (fun u => u.exitEpoch.toNat) _ k hk
  have hwdr_ne : ∀ k, k ≠ j → wdrOf b k = wdrOf a k := fun k hk =>
    w.read_ne (fun u => u.withdrawableEpoch.toNat) _ k hk
  have hexit_j : exitOf b j = x.toNat := w.read_self (fun u => u.exitEpoch.toNat) _
  have hwdr_j : wdrOf b j = x.toNat + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat := by
    rw [show wdrOf b j = (x + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay).toNat from
      w.read_self (fun u => u.withdrawableEpoch.toNat) _, UInt64.toNat_add, Nat.mod_eq_of_lt hno]
  have hexit_a : exitOf a j = farN := by
    unfold exitOf; rw [hv]; simp only [hfar]; rfl
  -- The reservation on `Nat`.
  have hbal : v.effectiveBalance.toNat = ebN a j := by unfold ebN; rw [hv]
  have hbalm : ebN a j ≤ maxEBN := Nat.le_trans (I.shape.ebLe j hjs) (hmax j hjs)
  have hee := I.eeLe
  have hmaxE := Nat.le_max_right st₀.earliestExitEpoch.toNat (E + lagN)
  have hcurlag : epochN a + lagN < 2 ^ 62 := by omega
  have hee62 : a.earliestExitEpoch.toNat < 2 ^ 62 := by
    have : exitedCount a * maddX ≤ (exitedCount a + 1) * maddX :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  have hearl := earliest_toNat a hactE (by omega)
  have hebcle : a.exitBalanceToConsume.toNat ≤ max st₀.exitBalanceToConsume.toNat CX :=
    I.churnX.ebcLe
  have hC62 : C < 2 ^ 62 := by have := Nat.le_max_right st₀.exitBalanceToConsume.toNat CX; omega
  have hcons : (if a.earliestExitEpoch < umax a.earliestExitEpoch act
      then exitChurn a else a.exitBalanceToConsume).toNat =
      if a.earliestExitEpoch.toNat < max a.earliestExitEpoch.toNat (epochN a + lagN) then C
      else a.exitBalanceToConsume.toNat := by
    by_cases hlt : a.earliestExitEpoch.toNat < max a.earliestExitEpoch.toNat (epochN a + lagN)
    · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hearl]; exact hlt), if_pos hlt, hC]
    · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hearl]; exact hlt), if_neg hlt]
  obtain ⟨hx1, hx2⟩ := reserveChurn_toNat v.effectiveBalance _ _ _ (by omega)
    (by rw [hcons]; split <;> omega) (by rw [hC]; omega) (by rw [hC]; exact hC62)
    (by rw [hearl]; omega) hres
  rw [hcons, hearl, hC, hbal] at hx1
  rw [hcons, hC, hbal] at hx2
  have hxN : x.toNat = resEpoch lagN a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat
      (epochN a) C (ebN a j) := by
    rw [hx1]; rfl
  have htot : c.toNat =
      resTotal lagN a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C (ebN a j) := by
    rw [hx2]; rfl
  -- The ghosts after the exit.
  let W' : Nat → Nat := fupd W j (ebN a j)
  let tag' : Nat → Bool := fupd tag j true
  have hW : ∀ k, k ≠ j → W' k = W k := fun k hk => fupd_ne _ _ hk
  have htag : ∀ k, k ≠ j → tag' k = tag k := fun k hk => fupd_ne _ _ hk
  have hWj : W' j = ebN a j := fupd_self _ _ _
  have htagj : tag' j = true := fupd_self _ _ _
  -- The exits that the exit churn paid for grow by at most this exit.
  have hS : churnSum vals st₀ b W' tag' true farN ≤ churnSum vals st₀ a W tag true farN + ebN a j := by
    unfold churnSum
    rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
    refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
    · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
    · rw [hk, hexit_a, hWj]
      split <;> simp
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ledger_step (e₀ := epochN st₀) (ee₀ := st₀.earliestExitEpoch.toNat)
    (ebc₀ := st₀.exitBalanceToConsume.toNat) (Cmax := CX) hcur (by omega) hCu I.churnX.mono
    I.churnX.held hS
  have hebc' : b.exitBalanceToConsume.toNat = resTotal lagN a.earliestExitEpoch.toNat
      a.exitBalanceToConsume.toNat (epochN a) C (ebN a j) - ebN a j := by
    show (c - v.effectiveBalance).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [htot, hbal]; exact hl4)),
      htot, hbal]
  have hee' : b.earliestExitEpoch.toNat = x.toNat := rfl
  have hxge : epochN a + lagN ≤ x.toNat := by rw [hxN]; exact hl3
  have hlag1 : 1 ≤ lagN := by unfold lagN; omega
  have hxlive : E + 1 < x.toNat + EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat := by
    have := hkE; omega
  have hfarN : farN = 2 ^ 64 - 1 := rfl
  have hwdr_a : wdrOf a j = farN := I.shape.exitFar j hjs hexit_a
  -- The potentials stay: the new withdrawable epoch lies after `E + 1`, as `farN` does.
  have hphi : phi vals E b = phi vals E a := by
    have hg : gSl vals b = gSl vals a := by
      unfold gSl
      rw [w.size]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      rw [hsl, hmx]
    have hc : gCons E b = gCons E a := by
      unfold gCons
      congr 2
      show List.filter _ a.pendingConsolidations.val.toList = List.filter _ a.pendingConsolidations.val.toList
      congr 1
      funext q
      by_cases hq : q.sourceIndex.toNat = j
      · rw [hq, hwdr_j, hwdr_a]
        simp only [decide_eq_decide]
        constructor <;> intro _ <;> omega
      · rw [hwdr_ne _ hq]
    unfold phi gPart
    rw [hg, hc]
    rfl
  have hexj_ne : exitOf b j ≠ farN := by rw [hexit_j]; omega
  have hcnt := exitedCount_set a b j hjs w.size hexit_a hexj_ne hexit_ne
  -- The exit epoch lies after the current epoch, so the active gate stays.
  have hkeep : AcKeep a b := w.acKeep rfl rfl (by
    have hvf : v.exitEpoch.toNat = farN := by rw [hfar]; rfl
    have hcN : (EthCLSpecs.Heze.currentEpochOf (pureState a)).toNat = epochN a := rfl
    rw [Bool.eq_iff_iff, isActive_iff, isActive_iff, hcN, hvf]
    show v.activationEpoch.toNat ≤ epochN a ∧ epochN a < x.toNat ↔ _
    constructor <;> intro hh <;> refine ⟨hh.1, ?_⟩ <;> omega)
  refine ⟨hkeep, W', tag', ⟨fun k hk hl => by rw [hcap]; exact I.cap k hk hl,
    by rw [hphi]; exact I.bud, fun k hk hl => by rw [heb]; exact I.track k hk hl,
    fun k h1 h2 => by rw [hact]; exact I.actOnce k h1 h2, ?exitOnce, ?newExit, ?churnX, ?churnC,
    ?shape, ?live, by rw [w.size]; exact I.sizeLe, ?eeLe, ?ceeLe, ?slashInv⟩⟩
  case slashInv =>
    intro k hk hs
    rw [hsl] at hs
    by_cases hkj : k = j
    · subst hkj
      exact absurd hexit_a (I.shape.slashedExit k hjs hs)
    · rw [hwdr_ne _ hkj]; exact I.slashInv k (by rw [← w.size]; exact hk) hs
  case exitOnce =>
    intro k h1 h2
    by_cases hk : k = j
    · subst hk
      exact absurd ((I.exitOnce _ h1 h2).symm.trans hexit_a) h2
    · rw [hexit_ne _ hk]; exact I.exitOnce k h1 h2
  case newExit =>
    intro k hk h1 h2 h3
    by_cases hkj : k.toNat = j
    · rw [hkj] at h1 h2 ⊢
      have hl : liveB st₀ E j = true := by
        have := hshape₀.exitFar j h1 h2
        unfold liveB
        unfold wdrOf at this
        cases hv0 : st₀.validators.val[j]? with
        | none => rfl
        | some v0 =>
          rw [hv0] at this
          dsimp only at this
          simp only [decide_eq_true_eq]
          have := hfarN
          omega
      have hb := (I.track k hk (by rw [hkj]; exact hl)).bound
      rw [hkj] at hb
      rw [hWj]
      have := le_add_absDiff (ebN st₀ j) (ebN a j)
      rw [absDiff_comm] at this
      unfold abound
      omega
    · rw [hW _ hkj]
      exact I.newExit k hk h1 h2 (by rw [← hexit_ne _ hkj]; exact h3)
  case churnX =>
    refine ⟨by rw [hee', hebc', hxN]; exact hl1, fun k hk j1 j2 j3 j4 => ?_, fun X => ?_,
      by rw [hee']; exact Nat.le_trans I.churnX.mono (by rw [hxN]; exact hl2), ?_⟩
    · by_cases hkj : k.toNat = j
      · rw [hkj, hexit_j, hee']; exact Nat.le_refl _
      · rw [hexit_ne _ hkj, hee']
        rw [htag _ hkj] at j4
        exact Nat.le_trans (I.churnX.le_ee k hk j1 j2 (by rw [← hexit_ne _ hkj]; exact j3) j4)
          (by rw [hxN]; exact hl2)
    · by_cases hX : x.toNat ≤ X
      · -- Every exit of the ledger lies at or before `x`, and `x` is at most `X`.
        have hmono : churnSum vals st₀ b W' tag' true X ≤ churnSum vals st₀ b W' tag' true farN := by
          unfold churnSum
          rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
          refine sum_map_le_sum_map _ _ (fun k => ?_) _
          split
          · rename_i hk
            simp only [decide_eq_true_eq] at hk
            have : exitOf b k.toNat < 2 ^ 64 := by
              unfold exitOf; split
              · exact UInt64.toNat_lt _
              · omega
            rw [if_pos (decide_eq_true ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, by omega⟩)]
            exact Nat.le_refl _
          · exact Nat.zero_le _
        have hlx : (x.toNat - ledgerBase (epochN st₀) st₀.earliestExitEpoch.toNat) * CX ≤
            (X - ledgerBase (epochN st₀) st₀.earliestExitEpoch.toNat) * CX :=
          Nat.mul_le_mul_right _ (by omega)
        rw [← hxN] at hl1
        omega
      · -- This exit lies after `X`, so the sum up to `X` keeps its old value.
        have hle : churnSum vals st₀ b W' tag' true X ≤ churnSum vals st₀ a W tag true X + 0 := by
          unfold churnSum
          rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
          refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
          · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
          · rw [hk, hexit_j, hexit_a]
            simp only [decide_eq_true_eq]
            rw [if_neg (by omega), if_neg (by omega)]
            exact Nat.le_refl _
        have := I.churnX.upTo X
        omega
    · rw [hebc']
      have := resTotal_sub_le a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C
        (ebN a j)
      have := I.churnX.ebcLe
      omega
  case churnC =>
    -- The consolidation ledger reads no exit of this step: the exit carries the exit tag.
    have e : ∀ X, churnSum vals st₀ b W' tag' false X = churnSum vals st₀ a W tag false X := by
      intro X
      have h1 : churnSum vals st₀ b W' tag' false X ≤ churnSum vals st₀ a W tag false X + 0 := by
        unfold churnSum
        rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
        refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
        · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
        · rw [hk, htagj]
          simp
      have h2 : churnSum vals st₀ a W tag false X ≤ churnSum vals st₀ b W' tag' false X + 0 := by
        unfold churnSum
        rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite]
        refine sum_le_add_single _ _ j _ _ hnd (fun k _ hk => ?_) (fun k _ hk => ?_)
        · simp only [hexit_ne _ hk, hW _ hk, htag _ hk]
        · rw [hk, hexit_a]
          simp
      omega
    obtain ⟨l1, l2, l3, l4, l5⟩ := I.churnC
    refine ⟨by rw [e]; exact l1, fun k hk j1 j2 j3 j4 => ?_, fun X => by rw [e]; exact l3 X, l4, l5⟩
    have hkj : k.toNat ≠ j := fun hkj => by rw [hkj, htagj] at j4; cases j4
    rw [hexit_ne _ hkj]
    rw [htag _ hkj] at j4
    exact l2 k hk j1 j2 (by rw [← hexit_ne _ hkj]; exact j3) j4
  case shape =>
    obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    refine ⟨by rw [w.bal, s1]; exact w.size.symm, fun k hk => by rw [heb, hmx]; exact s2 k (by
      rw [← w.size]; exact hk), fun k hk => by rw [heb]; exact s3 k (by rw [← w.size]; exact hk),
      fun k hk hx => ?_, fun k hk hs => ?_⟩
    · by_cases hkj : k = j
      · subst hkj; exact absurd hx hexj_ne
      · rw [hwdr_ne _ hkj]; exact s4 k (by rw [← w.size]; exact hk) (by rw [← hexit_ne _ hkj]; exact hx)
    · by_cases hkj : k = j
      · subst hkj; exact hexj_ne
      · rw [hexit_ne _ hkj]; exact s5 k (by rw [← w.size]; exact hk) (by rw [← hsl]; exact hs)
  case live =>
    intro k hk hl hs
    by_cases hkj : k.toNat = j
    · rw [hkj, hwdr_j]; exact hxlive
    · rw [hwdr_ne _ hkj]; exact I.live k hk hl (by rw [← w.size]; exact hs)
  case eeLe =>
    rw [hee', hcnt]
    have h1 := resEpoch_le a.earliestExitEpoch.toNat a.exitBalanceToConsume.toNat (epochN a) C
      (ebN a j)
    rw [← hxN] at h1
    have h2 : ebN a j / C ≤ maxEBN / incN :=
      Nat.le_trans (Nat.div_le_div_right hbalm) (Nat.div_le_div_left hCl hinc)
    have h3 : (exitedCount a + 1) * maddX = exitedCount a * maddX + maddX := Nat.succ_mul _ _
    have h4 : maddX = maxEBN / incN + 1 := rfl
    have h5 := I.eeLe
    omega
  case ceeLe =>
    rw [hcnt]
    have := I.ceeLe
    have : exitedCount a * maddC ≤ (exitedCount a + 1) * maddC :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    show a.earliestConsolidationEpoch.toNat ≤ _
    omega

end

end EthCLSpecs.Proofs.Heze
