import EthCLSpecs.Proofs.Heze.DriftBound

/-!
# `EthCLSpecs.Proofs.Heze.DriftInv`: the invariant of a run for the stake drift

Along a run from `st₀`, the drift bound follows each validator of `vals` with two ghost
values. `V i` bounds the move of its capped balance since `st₀`. `W i` is the effective
balance at which the run made it exit, and `tag i` names the churn that paid for the exit:
`true` for the exit churn, `false` for the consolidation churn.

`RunInv` holds at every state of the run. Its fields:

- `cap`, `track`: the capped balance lies within `V i` of its value at `st₀`, and the
  effective balance follows `EbTrack` (`DriftMath.lean`).
- `bud`: the moves, plus the potentials `phi`, stay within the budget spent so far.
- `actOnce`, `exitOnce`: a set activation epoch or exit epoch of `st₀` stays.
- `newExit`: a validator of `st₀` that the run made exit had an effective balance `W i` close
  to its effective balance at `st₀`.
- `churnX`, `churnC`: the two churn ledgers. The exits that each churn paid for add up to at
  most the churn of the epochs up to the exit epoch.
- `shape`: the shape facts that the writers need (`ShapeOK`).
- `live`: a live index keeps a withdrawable epoch after `E + 1`.
- `sizeLe`, `eeLe`, `ceeLe`: the registry does not shrink, and the two `earliest` epochs stay
  below a bound in the exited count and the reservation count `Γp`.
- `slashInv`: a slashed validator was slashed at `st₀` with the same withdrawable epoch, or
  is withdrawable one slashings vector after the epoch of `st₀`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState ValidatorIndex Validator Gwei)

section
variable [Preset] [HasherTag]

/-- The far-future epoch, in `Nat`. -/
abbrev farN : Nat := 2 ^ 64 - 1

/-- The withdrawable epoch of index `i`, in `Nat`, or the far future past the registry. -/
def wdrOf (u : BeaconState) (i : Nat) : Nat :=
  match u.validators.val[i]? with
  | some v => v.withdrawableEpoch.toNat
  | none => farN

/-- Index `i` is a slashed validator. -/
def slashedOf (u : BeaconState) (i : Nat) : Bool :=
  match u.validators.val[i]? with
  | some v => v.slashed
  | none => false

/-- The size of the registry. -/
def sizeOf (u : BeaconState) : Nat := u.validators.val.size

/-! ## Constants -/

/-- `EFFECTIVE_BALANCE_INCREMENT`. -/
def incN : Nat := EthCLSpecs.Heze.Const.effectiveBalanceIncrementG.toNat

/-- The downward threshold of the hysteresis rule. -/
def downN : Nat :=
  (EthCLSpecs.Heze.Const.effectiveBalanceIncrementG /
    UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisQuotient *
      UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisDownwardMultiplier).toNat

/-- The upward threshold of the hysteresis rule. -/
def upN : Nat :=
  (EthCLSpecs.Heze.Const.effectiveBalanceIncrementG /
    UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisQuotient *
      UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisUpwardMultiplier).toNat

/-- The distance after an update of an effective balance. -/
def aN : Nat := max upN incN

/-- `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
def maxEBN : Nat := EthCLSpecs.Heze.Const.maxEffectiveBalanceElectraG.toNat

/-- The cost of one slashing of a validator with cap `m`: the penalty and the whistleblower
reward. -/
def slashCost (m : Nat) : Nat :=
  m / EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra +
    m / EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra

/-! ## Potentials -/

/-- The slashing potential: the cost of each index of `vals` that is not yet a slashed
validator. An index past the registry costs at the largest cap. -/
def gSl (vals : List ValidatorIndex) (u : BeaconState) : Nat :=
  (vals.map fun i =>
    if i.toNat < sizeOf u then (if slashedOf u i.toNat then 0 else slashCost (maxN u i.toNat))
    else slashCost maxEBN).sum

/-- The consolidation potential: the largest cap for each queued consolidation whose source
can be withdrawn by `E + 1`. -/
def gCons (E : Nat) (u : BeaconState) : Nat :=
  maxEBN * (u.pendingConsolidations.val.toList.filter fun q =>
    decide (wdrOf u q.sourceIndex.toNat ≤ E + 1)).length

/-- The pending-partial potential: the queued partial withdrawals that can be withdrawn by
`E`. -/
def gPart (E : Nat) (u : BeaconState) : Nat :=
  ((u.pendingPartialWithdrawals.val.toList.filter fun w =>
    decide (w.withdrawableEpoch.toNat ≤ E)).map fun w => w.amount.toNat).sum

/-- The sum of the potentials, with the deposit churn carried over. -/
def phi (vals : List ValidatorIndex) (E : Nat) (u : BeaconState) : Nat :=
  u.depositBalanceToConsume.toNat + gCons E u + gSl vals u + gPart E u

/-! ## The churn ledgers -/

/-- The delay of an exit or an activation: `compute_activation_exit_epoch(e) = e + lagN`. -/
def lagN : Nat := 1 + EthCLSpecs.Heze.Const.maxSeedLookahead.toNat

/-- A churn ledger, read at `st₀`: the base epoch `B` and the carried churn `K`. Before any
exit of the run, an `earliest` epoch below `e₀ + lagN` is stale: the first exit restarts the
ledger at the current epoch plus `lagN`. -/
def ledgerBase (e₀ ee₀ : Nat) : Nat := max ee₀ (e₀ + lagN - 1)

def ledgerCarry (e₀ ee₀ ebc₀ : Nat) : Nat := if e₀ + lagN ≤ ee₀ then ebc₀ else 0

/-- The churn that a ledger state still holds: the carried churn, when the ledger is not
stale. -/
def ledgerHeld (e₀ ee ebc : Nat) : Nat := if e₀ + lagN ≤ ee then ebc else 0

/-- The exits of the run that a churn paid for, up to the epoch `X`: the validators of
`st₀`, without an exit at `st₀`, with the tag of the churn and an exit epoch at most `X`. -/
def churnSum (vals : List ValidatorIndex) (st₀ u : BeaconState) (W : Nat → Nat)
    (tag : Nat → Bool) (t : Bool) (X : Nat) : Nat :=
  ((vals.filter fun i => decide (i.toNat < sizeOf st₀ ∧ exitOf st₀ i.toNat = farN ∧
      exitOf u i.toNat ≠ farN ∧ tag i.toNat = t ∧ exitOf u i.toNat ≤ X)).map
    fun i => W i.toNat).sum

/-- One churn ledger along the run. `ee` and `ebc` read the ledger fields of `u`, and `C` bounds
the churn of one epoch. -/
structure Ledger (vals : List ValidatorIndex) (st₀ u : BeaconState) (W : Nat → Nat)
    (tag : Nat → Bool) (t : Bool) (ee₀ ebc₀ ee ebc C : Nat) : Prop where
  held : churnSum vals st₀ u W tag t farN + ledgerHeld (epochN st₀) ee ebc ≤
    ledgerCarry (epochN st₀) ee₀ ebc₀ + (ee - ledgerBase (epochN st₀) ee₀) * C
  le_ee : ∀ i ∈ vals, i.toNat < sizeOf st₀ → exitOf st₀ i.toNat = farN →
    exitOf u i.toNat ≠ farN → tag i.toNat = t → exitOf u i.toNat ≤ ee
  upTo : ∀ X, churnSum vals st₀ u W tag t X ≤
    ledgerCarry (epochN st₀) ee₀ ebc₀ + (X - ledgerBase (epochN st₀) ee₀) * C
  mono : ee₀ ≤ ee
  ebcLe : ebc ≤ max ebc₀ C

/-- A ledger reads the exits of its state alone. -/
theorem Ledger.of_exit_eq {vals : List ValidatorIndex} {st₀ a b : BeaconState} {W : Nat → Nat}
    {tag : Nat → Bool} {t : Bool} {ee₀ ebc₀ ee ebc C : Nat}
    (L : Ledger vals st₀ a W tag t ee₀ ebc₀ ee ebc C) (h : ∀ i, exitOf b i = exitOf a i) :
    Ledger vals st₀ b W tag t ee₀ ebc₀ ee ebc C := by
  have e : ∀ X, churnSum vals st₀ b W tag t X = churnSum vals st₀ a W tag t X := fun X => by
    simp [churnSum, h]
  exact ⟨by rw [e]; exact L.held, fun i hi j1 j2 j3 j4 => by
    rw [h]; exact L.le_ee i hi j1 j2 (by rw [← h]; exact j3) j4,
    fun X => by rw [e]; exact L.upTo X, L.mono, L.ebcLe⟩

/-- The number of validators of `u` with an exit epoch. -/
def exitedCount (u : BeaconState) : Nat :=
  ((List.range (sizeOf u)).filter fun i => decide (exitOf u i ≠ farN)).length

/-- The largest move of `earliest_exit_epoch` by one exit. -/
def maddX : Nat := maxEBN / incN + 1

/-- The largest move of `earliest_exit_epoch` by one partial withdrawal. -/
def maddP : Nat := 2 ^ 62 / incN + 1

/-- The largest move of `earliest_consolidation_epoch` by one consolidation. -/
def maddC : Nat := maxEBN / EthCLSpecs.Heze.Const.minActivationBalance.toNat + 1

/-! ## The invariant -/

/-- The shape facts of a state that the writers need. -/
structure ShapeOK (u : BeaconState) : Prop where
  sizes : u.balances.val.size = u.validators.val.size
  ebLe : ∀ i, i < sizeOf u → ebN u i ≤ maxN u i
  ebMul : ∀ i, i < sizeOf u → ebN u i % incN = 0
  exitFar : ∀ i, i < sizeOf u → exitOf u i = farN → wdrOf u i = farN
  slashedExit : ∀ i, i < sizeOf u → slashedOf u i = true → exitOf u i ≠ farN

/-- The invariant of the run at `t`, with the ghosts `V`, `W`, `tag`, the count `Γp` of partial
withdrawals that reserved exit churn, and the budget spent `B`. `CX` and `CC` bound the exit
churn and the consolidation churn of one epoch. -/
structure RunInv (vals : List ValidatorIndex) (st₀ : BeaconState) (E CX CC : Nat)
    (t : BeaconState) (V W : Nat → Nat) (tag : Nat → Bool) (Γp B : Nat) : Prop where
  cap : ∀ i ∈ vals, liveB st₀ E i.toNat = true →
    absDiff (capN t i.toNat) (capN st₀ i.toNat) ≤ V i.toNat
  bud : ((vals.filter fun i => liveB st₀ E i.toNat).map fun i => V i.toNat).sum +
    phi vals E t ≤ B
  track : ∀ i ∈ vals, liveB st₀ E i.toNat = true →
    EbTrack downN aN (ebN t i.toNat) (ebN st₀ i.toNat) (eps0 st₀ i.toNat) (V i.toNat)
  actOnce : ∀ i, i < sizeOf st₀ → actOf st₀ i ≠ farN → actOf t i = actOf st₀ i
  exitOnce : ∀ i, i < sizeOf st₀ → exitOf st₀ i ≠ farN → exitOf t i = exitOf st₀ i
  newExit : ∀ i ∈ vals, i.toNat < sizeOf st₀ → exitOf st₀ i.toNat = farN →
    exitOf t i.toNat ≠ farN →
    ebN st₀ i.toNat ≤ W i.toNat + abound aN downN (eps0 st₀ i.toNat + V i.toNat)
  churnX : Ledger vals st₀ t W tag true st₀.earliestExitEpoch.toNat
    st₀.exitBalanceToConsume.toNat t.earliestExitEpoch.toNat t.exitBalanceToConsume.toNat CX
  churnC : Ledger vals st₀ t W tag false st₀.earliestConsolidationEpoch.toNat
    st₀.consolidationBalanceToConsume.toNat t.earliestConsolidationEpoch.toNat
    t.consolidationBalanceToConsume.toNat CC
  shape : ShapeOK t
  live : ∀ i ∈ vals, liveB st₀ E i.toNat = true → i.toNat < sizeOf t → E + 1 < wdrOf t i.toNat
  sizeLe : sizeOf st₀ ≤ sizeOf t
  eeLe : t.earliestExitEpoch.toNat ≤ max st₀.earliestExitEpoch.toNat (E + lagN) +
    exitedCount t * maddX + Γp * maddP
  ceeLe : t.earliestConsolidationEpoch.toNat ≤ max st₀.earliestConsolidationEpoch.toNat (E + lagN) +
    exitedCount t * maddC
  slashInv : ∀ i, i < sizeOf t → slashedOf t i = true →
    (i < sizeOf st₀ ∧ slashedOf st₀ i = true ∧ wdrOf t i = wdrOf st₀ i) ∨
      epochN st₀ + EthCLSpecs.Heze.Const.epochsPerSlashingsVector ≤ wdrOf t i

/-! ## The gates at the end of the run -/

omit [Preset] [HasherTag] in
/-- The gates of one validator, as `Nat` facts. A set activation epoch and a set exit epoch
stay, and the epoch does not decrease. Then the gates differ only for a pending activation, a
scheduled exit up to `E`, or a new exit up to `E`. -/
theorem gates_change {a₀ x₀ aᵤ xᵤ e₀ E : Nat} (hE : e₀ ≤ E) (hEf : E < farN)
    (ha : a₀ ≠ farN → aᵤ = a₀) (hx : x₀ ≠ farN → xᵤ = x₀)
    (hch : ((aᵤ ≤ E ∧ E < xᵤ) ∨ (aᵤ ≤ E - 1 ∧ E - 1 < xᵤ)) ≠
        ((a₀ ≤ e₀ ∧ e₀ < x₀) ∨ (a₀ ≤ e₀ - 1 ∧ e₀ - 1 < x₀)) ∨
      (aᵤ ≤ E ∧ E < xᵤ) ≠ (a₀ ≤ e₀ ∧ e₀ < x₀)) :
    e₀ < a₀ ∨ (x₀ ≠ farN ∧ e₀ ≤ x₀ ∧ x₀ ≤ E) ∨ (x₀ = farN ∧ xᵤ ≤ E) := by
  by_cases h1 : e₀ < a₀
  · exact .inl h1
  have haf : a₀ ≠ farN := by omega
  have hau := ha haf
  subst hau
  -- Away from the three cases, both gates agree, against `hch`.
  by_cases hxf : x₀ = farN
  · by_cases h3 : xᵤ ≤ E
    · exact .inr (.inr ⟨hxf, h3⟩)
    · exfalso
      apply hch.elim <;> intro hne <;> apply hne <;> apply propext <;>
        constructor <;> intro _ <;> omega
  · have hxu := hx hxf
    subst hxu
    by_cases h2 : e₀ ≤ xᵤ ∧ xᵤ ≤ E
    · exact .inr (.inl ⟨hxf, h2.1, h2.2⟩)
    · exfalso
      apply hch.elim <;> intro hne <;> apply hne <;> apply propext <;>
        constructor <;> intro _ <;> omega

/-- The previous epoch of `u`, in `Nat`. -/
theorem prevN (u : BeaconState) :
    (EthCLSpecs.Heze.previousEpochOf (pureState u)).toNat = epochN u - 1 := by
  rw [previousEpochOf_toNat_sub]
  unfold epochN
  rw [currentEpochOf_toNat]
  rfl

omit [HasherTag] in
/-- `isActiveValidator`, in `Nat`. -/
theorem isActive_iff (v : Validator) (e : EthCLSpecs.Heze.Epoch) :
    EthCLSpecs.Heze.isActiveValidator v e = true ↔
      v.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < v.exitEpoch.toNat := by
  unfold EthCLSpecs.Heze.isActiveValidator
  simp [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]

/-- The link gate, in `Nat`. -/
theorem laB_iff (u : BeaconState) (i : Nat) (v : Validator) (hv : u.validators.val[i]? = some v) :
    laB u i = true ↔ (v.activationEpoch.toNat ≤ epochN u ∧ epochN u < v.exitEpoch.toNat) ∨
      (v.activationEpoch.toNat ≤ epochN u - 1 ∧ epochN u - 1 < v.exitEpoch.toNat) := by
  unfold laB
  rw [hv]
  simp only [Bool.or_eq_true, isActive_iff, prevN]
  rfl

/-- The active gate, in `Nat`. -/
theorem acB_iff (u : BeaconState) (i : Nat) (v : Validator) (hv : u.validators.val[i]? = some v) :
    acB u i = true ↔ v.activationEpoch.toNat ≤ epochN u ∧ epochN u < v.exitEpoch.toNat := by
  unfold acB
  rw [hv]
  simp only [isActive_iff]
  rfl

/-- The new-exit bound of the end facts: the two churn ledgers up to `E`. -/
def neBound (st₀ : BeaconState) (E CX CC : Nat) : Nat :=
  (ledgerCarry (epochN st₀) st₀.earliestExitEpoch.toNat st₀.exitBalanceToConsume.toNat +
    (E - ledgerBase (epochN st₀) st₀.earliestExitEpoch.toNat) * CX) +
  (ledgerCarry (epochN st₀) st₀.earliestConsolidationEpoch.toNat
      st₀.consolidationBalanceToConsume.toNat +
    (E - ledgerBase (epochN st₀) st₀.earliestConsolidationEpoch.toNat) * CC)

/-- **The invariant at the end of the run gives the end facts.** -/
theorem RunInv.endFacts {vals : List ValidatorIndex} {st₀ u : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC u V W tag Γp B) (hnd : vals.Nodup)
    (hcov : ∀ i, i < st₀.validators.val.size → UInt64.ofNat i ∈ vals)
    (h64₀ : st₀.validators.val.size < 2 ^ 64) (h64u : u.validators.val.size < 2 ^ 64)
    (sum₀ : (st₀.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64)
    (sumu : (u.validators.val.toList.map (·.effectiveBalance.toNat)).sum < 2 ^ 64)
    (hE : epochN u = E) (hE0 : epochN st₀ ≤ E) (hEf : E + 1 < farN) (delay : Nat)
    (hdelay : 2 ≤ delay) (hshape₀ : ShapeOK st₀)
    (hwd₀ : ∀ i, i < sizeOf st₀ → exitOf st₀ i ≠ farN → exitOf st₀ i + delay ≤ wdrOf st₀ i) :
    EndFacts vals st₀ u E aN downN V W B (neBound st₀ E CX CC) := by
  -- A validator of `st₀` at index `i`, and its validator in `u`.
  have hsome : ∀ i, i < sizeOf st₀ → ∃ v₀ vᵤ, st₀.validators.val[i]? = some v₀ ∧
      u.validators.val[i]? = some vᵤ ∧ actOf st₀ i = v₀.activationEpoch.toNat ∧
      exitOf st₀ i = v₀.exitEpoch.toNat ∧ actOf u i = vᵤ.activationEpoch.toNat ∧
      exitOf u i = vᵤ.exitEpoch.toNat := fun i hi => by
    have hi' : i < st₀.validators.val.size := hi
    have hiu : i < u.validators.val.size := Nat.lt_of_lt_of_le hi I.sizeLe
    refine ⟨_, _, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hiu, ?_, ?_, ?_, ?_⟩ <;>
      simp [actOf, exitOf, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hiu]
  refine ⟨hnd, hcov, h64₀, h64u, sum₀, sumu, ?laLive, I.track, ?gate, ?neEB, ?neSum, ?vSum⟩
  case laLive =>
    intro i _ hla
    unfold liveB
    cases hv : st₀.validators.val[i.toNat]? with
    | none => rfl
    | some v₀ =>
      simp only [decide_eq_true_eq]
      refine Classical.byContradiction fun hw => ?_
      have hi : i.toNat < sizeOf st₀ := (Array.getElem?_eq_some_iff.mp hv).1
      obtain ⟨v₀', vᵤ, h0, hu, -, hx0, -, hxu⟩ := hsome _ hi
      rw [hv] at h0
      cases h0
      have hwdr : wdrOf st₀ i.toNat = v₀.withdrawableEpoch.toNat := by simp [wdrOf, hv]
      by_cases hf : exitOf st₀ i.toNat = farN
      · have := hshape₀.exitFar _ hi hf
        omega
      · have h1 := hwd₀ _ hi hf
        have h2 := I.exitOnce _ hi hf
        rw [(laB_iff u _ _ hu), hE] at hla
        omega
  case gate =>
    intro i _ hch hne0
    have hi : i.toNat < sizeOf st₀ := Classical.byContradiction fun hge =>
      hne0 (ebN_eq_zero_of_ge (by unfold sizeOf at hge; omega))
    obtain ⟨v₀, vᵤ, h0, hu, ha0, hx0, hau, hxu⟩ := hsome _ hi
    have hg := gates_change hE0 (by omega)
      (fun h => (I.actOnce _ hi h).trans rfl |>.trans rfl) (fun h => I.exitOnce _ hi h) (by
        rw [ha0, hx0, hau, hxu]
        rcases hch with h | h
        · refine .inl fun heq => h ?_
          rw [Bool.eq_iff_iff, laB_iff u _ _ hu, laB_iff st₀ _ _ h0, hE]
          exact Iff.of_eq heq
        · refine .inr fun heq => h ?_
          rw [Bool.eq_iff_iff, acB_iff u _ _ hu, acB_iff st₀ _ _ h0, hE]
          exact Iff.of_eq heq)
    unfold pendingB schedB newExitB
    rcases hg with h | h | h
    · exact .inl (decide_eq_true h)
    · exact .inr (.inl (decide_eq_true h))
    · exact .inr (.inr (decide_eq_true ⟨hi, h⟩))
  case neEB =>
    intro i hiv hn
    unfold newExitB at hn
    obtain ⟨hi, hx0, hxu⟩ := of_decide_eq_true hn
    refine ⟨I.newExit i hiv hi hx0 (by omega), ?_⟩
    have hw := hshape₀.exitFar _ hi hx0
    unfold liveB
    cases hv : st₀.validators.val[i.toNat]? with
    | none => rfl
    | some v₀ =>
      have : wdrOf st₀ i.toNat = v₀.withdrawableEpoch.toNat := by simp [wdrOf, hv]
      simp only [decide_eq_true_eq]
      omega
  case neSum =>
    -- Each new exit up to `E` belongs to one of the two ledgers.
    have hsplit : ((vals.filter fun i => newExitB st₀ u E i.toNat).map fun i => W i.toNat).sum ≤
        churnSum vals st₀ u W tag true E + churnSum vals st₀ u W tag false E := by
      unfold churnSum
      rw [sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, sum_filter_eq_sum_ite, ← sum_map_add]
      refine sum_map_le_sum_map _ _ (fun i => ?_) _
      unfold newExitB
      by_cases hn : i.toNat < sizeOf st₀ ∧ exitOf st₀ i.toNat = farN ∧ exitOf u i.toNat ≤ E
      · have hnf : exitOf u i.toNat ≠ farN := by omega
        unfold sizeOf at hn
        cases tag i.toNat <;> simp [hn, hnf, sizeOf]
      · unfold sizeOf at hn
        simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact Nat.zero_le _
    have h1 := I.churnX.upTo E
    have h2 := I.churnC.upTo E
    unfold neBound
    omega
  case vSum =>
    have := I.bud
    omega

/-! ## The start of the run -/

omit [HasherTag] in
/-- No validator of `st₀` exits in an empty run. -/
theorem churnSum_self (vals : List ValidatorIndex) (st₀ : BeaconState) (W : Nat → Nat)
    (tag : Nat → Bool) (t : Bool) (X : Nat) : churnSum vals st₀ st₀ W tag t X = 0 := by
  unfold churnSum
  rw [show (vals.filter fun i => decide (i.toNat < sizeOf st₀ ∧ exitOf st₀ i.toNat = farN ∧
      exitOf st₀ i.toNat ≠ farN ∧ tag i.toNat = t ∧ exitOf st₀ i.toNat ≤ X)) = [] from
    List.filter_eq_nil_iff.mpr fun i _ => by simp only [decide_eq_true_eq]; omega]
  rfl

theorem Ledger.init (vals : List ValidatorIndex) (st₀ : BeaconState) (W : Nat → Nat)
    (tag : Nat → Bool) (t : Bool) (ee₀ ebc₀ C : Nat) :
    Ledger vals st₀ st₀ W tag t ee₀ ebc₀ ee₀ ebc₀ C := by
  refine ⟨?_, fun i _ _ h1 h2 => absurd h1 h2, fun X => ?_, Nat.le_refl _, Nat.le_max_left _ _⟩
  · rw [churnSum_self]
    unfold ledgerHeld ledgerCarry ledgerBase
    split <;> omega
  · rw [churnSum_self]
    exact Nat.zero_le _

/-- **The invariant holds at the start of the run.** -/
theorem RunInv.init (vals : List ValidatorIndex) (st₀ : BeaconState) (E CX CC : Nat)
    (hshape : ShapeOK st₀) :
    RunInv vals st₀ E CX CC st₀ (fun _ => 0) (fun _ => 0) (fun _ => true) 0 (phi vals E st₀) where
  cap i _ _ := by simp [absDiff_self]
  bud := by
    have : ((vals.filter fun i => liveB st₀ E i.toNat).map fun _ => (0 : Nat)).sum = 0 := by
      induction (vals.filter fun i => liveB st₀ E i.toNat) with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    omega
  track i _ _ := EbTrack.init _ _ _ _ _
  actOnce _ _ _ := rfl
  exitOnce _ _ _ := rfl
  newExit _ _ _ h1 h2 := absurd h1 h2
  churnX := Ledger.init vals st₀ _ _ _ _ _ _
  churnC := Ledger.init vals st₀ _ _ _ _ _ _
  shape := hshape
  live i _ hl hi := by
    unfold liveB at hl
    unfold wdrOf
    unfold sizeOf at hi
    rw [Array.getElem?_eq_getElem hi] at hl ⊢
    exact of_decide_eq_true hl
  sizeLe := Nat.le_refl _
  eeLe := by have := Nat.le_max_left st₀.earliestExitEpoch.toNat (E + lagN); omega
  ceeLe := by have := Nat.le_max_left st₀.earliestConsolidationEpoch.toNat (E + lagN); omega
  slashInv i hi hs := .inl ⟨hi, hs, rfl⟩

/-! ## Frames -/

/-- The fields of a state that the invariant reads. -/
def econView (u : BeaconState) :=
  (u.validators, u.balances, u.pendingConsolidations, u.pendingPartialWithdrawals,
    u.depositBalanceToConsume, u.exitBalanceToConsume, u.earliestExitEpoch,
    u.consolidationBalanceToConsume, u.earliestConsolidationEpoch)

omit [HasherTag] in
/-- Two registries of one size with the same exit epochs have the same exited count. -/
theorem exitedCount_eq {a b : BeaconState} (hs : sizeOf b = sizeOf a)
    (he : ∀ i, exitOf b i = exitOf a i) : exitedCount b = exitedCount a := by
  unfold exitedCount
  rw [hs]
  simp only [he]

/-- A state with the same `econView` keeps the invariant. -/
theorem RunInv.of_econ {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (h : econView b = econView a) : RunInv vals st₀ E CX CC b V W tag Γp B := by
  simp only [econView, Prod.mk.injEq] at h
  obtain ⟨hv, hb, hc, hp, hd, hx1, hx2, hc1, hc2⟩ := h
  have e1 : ∀ i, capN b i = capN a i := fun i => by simp [capN, balN, maxN, hv, hb]
  have e2 : ∀ i, ebN b i = ebN a i := fun i => by simp [ebN, hv]
  have e3 : phi vals E b = phi vals E a := by
    unfold phi gCons gSl gPart sizeOf slashedOf maxN wdrOf
    rw [hv, hc, hp, hd]
  have e4 : ∀ i, actOf b i = actOf a i := fun i => by simp [actOf, hv]
  have e5 : ∀ i, exitOf b i = exitOf a i := fun i => by simp [exitOf, hv]
  have e6 : ∀ i, wdrOf b i = wdrOf a i := fun i => by simp [wdrOf, hv]
  have e7 : sizeOf b = sizeOf a := by simp [sizeOf, hv]
  have e10 := exitedCount_eq e7 e5
  have e11 : ∀ i, slashedOf b i = slashedOf a i := fun i => by simp [slashedOf, hv]
  refine ⟨fun i hi hl => by rw [e1]; exact I.cap i hi hl, by rw [e3]; exact I.bud,
    fun i hi hl => by rw [e2]; exact I.track i hi hl, fun i h1 h2 => by rw [e4]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [e5]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => I.newExit i hi h1 h2 (by rw [← e5]; exact h3),
    by rw [hx1, hx2]; exact I.churnX.of_exit_eq e5, by rw [hc1, hc2]; exact I.churnC.of_exit_eq e5, ?_,
    fun i hi hl hs => by rw [e6]; exact I.live i hi hl (by rw [← e7]; exact hs),
    by rw [e7]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [e6]; exact I.slashInv i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)⟩
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    have e9 : ∀ i, maxN b i = maxN a i := fun i => by simp [maxN, hv]
    constructor
    · rw [hv, hb]; exact s1
    · intro i hi; rw [e2, e9]; exact s2 i (by rw [← e7]; exact hi)
    · intro i hi; rw [e2]; exact s3 i (by rw [← e7]; exact hi)
    · intro i hi hx; rw [e6]; exact s4 i (by rw [← e7]; exact hi) (by rw [← e5]; exact hx)
    · intro i hi hs; rw [e5]; exact s5 i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)

/-! ## The constants -/

/-- The facts on the preset and config constants that the bound needs. The hysteresis
thresholds lie below one increment, in the right order, and every cap of an effective
balance is a multiple of the increment. The constants that the body casts to `uint64` with
`UInt64.ofNat` fit in `uint64`, so the cast keeps their value. -/
structure DriftConsts : Prop where
  incPos : 0 < incN
  downLe : downN ≤ upN
  downLt : downN < incN
  upSmall : upN < 2 ^ 62
  maxMul : ∀ v : Validator, (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat % incN = 0
  maxLe : ∀ v : Validator, (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat ≤ maxEBN
  maxEB62 : maxEBN < 2 ^ 62
  slashQ : EthCLSpecs.Heze.Const.minSlashingPenaltyQuotientElectra < 2 ^ 64 ∧
    EthCLSpecs.Heze.Const.whistleblowerRewardQuotientElectra < 2 ^ 64
  syncLt : EthCLSpecs.Heze.Const.syncCommitteeSize < 2 ^ 64

/-! ## Balance writers -/

omit [Preset] [HasherTag] in
theorem abound_mono {A d x y : Nat} (h : x ≤ y) : abound A d x ≤ abound A d y := by
  unfold abound
  exact Nat.add_le_add h (Nat.div_le_div_right (Nat.mul_le_mul_left _ h))

/-- The ghost move after a step from `a` to `b`. -/
def stepV (V : Nat → Nat) (a b : BeaconState) (i : Nat) : Nat := V i + absDiff (capN b i) (capN a i)

omit [HasherTag] in
theorem sum_stepV (vals : List ValidatorIndex) (st₀ : BeaconState) (E : Nat) (V : Nat → Nat)
    (a b : BeaconState) :
    ((vals.filter fun i => liveB st₀ E i.toNat).map fun i => stepV V a b i.toNat).sum =
      ((vals.filter fun i => liveB st₀ E i.toNat).map fun i => V i.toNat).sum +
        moveN vals st₀ E a b := by
  unfold stepV moveN
  rw [sum_map_add]

/-- **A writer that changes balances alone keeps the invariant**, with the ghost move of the
step, at the cost of its move. -/
theorem RunInv.balanceStep {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B β : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (h : econView b = econView { a with balances := b.balances })
    (hsz : b.balances.val.size = a.balances.val.size) (hm : moveN vals st₀ E a b ≤ β) :
    RunInv vals st₀ E CX CC b (stepV V a b) W tag Γp (B + β) := by
  simp only [econView, Prod.mk.injEq] at h
  obtain ⟨hv, -, hc, hp, hd, hx1, hx2, hc1, hc2⟩ := h
  have e2 : ∀ i, ebN b i = ebN a i := fun i => by simp [ebN, hv]
  have e3 : phi vals E b = phi vals E a := by
    unfold phi gCons gSl gPart sizeOf slashedOf maxN wdrOf
    rw [hv, hc, hp, hd]
  have e4 : ∀ i, actOf b i = actOf a i := fun i => by simp [actOf, hv]
  have e5 : ∀ i, exitOf b i = exitOf a i := fun i => by simp [exitOf, hv]
  have e6 : ∀ i, wdrOf b i = wdrOf a i := fun i => by simp [wdrOf, hv]
  have e7 : sizeOf b = sizeOf a := by simp [sizeOf, hv]
  have e9 : ∀ i, maxN b i = maxN a i := fun i => by simp [maxN, hv]
  have e10 := exitedCount_eq e7 e5
  have e11 : ∀ i, slashedOf b i = slashedOf a i := fun i => by simp [slashedOf, hv]
  have hV : ∀ i, V i ≤ stepV V a b i := fun i => Nat.le_add_right _ _
  refine ⟨fun i hi hl => ?_, ?_, fun i hi hl => ?_, fun i h1 h2 => by rw [e4]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [e5]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => ?_, by rw [hx1, hx2]; exact I.churnX.of_exit_eq e5,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq e5, ?_,
    fun i hi hl hs => by rw [e6]; exact I.live i hi hl (by rw [← e7]; exact hs),
    by rw [e7]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [e6]; exact I.slashInv i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)⟩
  · have := absDiff_triangle (capN b i.toNat) (capN a i.toNat) (capN st₀ i.toNat)
    have := I.cap i hi hl
    unfold stepV
    omega
  · rw [sum_stepV, e3]
    have := I.bud
    omega
  · rw [e2]; exact (I.track i hi hl).mono (hV _)
  · exact Nat.le_trans (I.newExit i hi h1 h2 (by rw [← e5]; exact h3))
      (Nat.add_le_add_left (abound_mono (Nat.add_le_add_left (hV _) _)) _)
  · obtain ⟨s1, s2, s3, s4, s5⟩ := I.shape
    constructor
    · rw [hv, hsz]; exact s1
    · intro i hi; rw [e2, e9]; exact s2 i (by rw [← e7]; exact hi)
    · intro i hi; rw [e2]; exact s3 i (by rw [← e7]; exact hi)
    · intro i hi hx; rw [e6]; exact s4 i (by rw [← e7]; exact hi) (by rw [← e5]; exact hx)
    · intro i hi hs; rw [e5]; exact s5 i (by rw [← e7]; exact hi) (by rw [← e11]; exact hs)

/-! ## The effective-balance update -/

omit [HasherTag] in
/-- `ebuVal` keeps every field but the effective balance. -/
theorem ebuVal_eq (v : Validator) (bal : Gwei) :
    ebuVal v bal = { v with effectiveBalance := (ebuVal v bal).effectiveBalance } := by
  unfold ebuVal; dsimp only; split <;> rfl

omit [HasherTag] in
/-- `ebuVal` on `Nat`, when the two threshold sums do not wrap. -/
theorem ebuVal_toNat (v : Validator) (bal : Gwei) (hb : bal.toNat + downN < 2 ^ 64)
    (he : v.effectiveBalance.toNat + upN < 2 ^ 64) :
    (ebuVal v bal).effectiveBalance.toNat = ebUpdate incN downN upN v.effectiveBalance.toNat
      bal.toNat (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat := by
  unfold ebuVal ebUpdate
  dsimp only
  unfold downN at hb
  unfold upN at he
  have c1 : (bal + EthCLSpecs.Heze.Const.effectiveBalanceIncrementG /
      UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisQuotient *
        UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisDownwardMultiplier < v.effectiveBalance) ↔
      bal.toNat + downN < v.effectiveBalance.toNat := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt hb]; rfl
  have c2 : (v.effectiveBalance + EthCLSpecs.Heze.Const.effectiveBalanceIncrementG /
      UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisQuotient *
        UInt64.ofNat EthCLSpecs.Heze.Const.hysteresisUpwardMultiplier < bal) ↔
      v.effectiveBalance.toNat + upN < bal.toNat := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt he]; rfl
  by_cases hc : bal.toNat + downN < v.effectiveBalance.toNat ∨ v.effectiveBalance.toNat + upN < bal.toNat
  · rw [if_pos (by simpa [c1, c2] using hc), if_pos hc]
    simp only
    rw [umin_toNat, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)), UInt64.toNat_mod]
    rfl
  · rw [if_neg (by simpa [c1, c2] using hc), if_neg hc]

/-- **A step that keeps every read but the effective balances keeps the invariant**, with
the same ghosts, when the effective balances still track and keep their shape. -/
theorem RunInv.transfer {vals : List ValidatorIndex} {st₀ a b : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B)
    (hcap : ∀ i, capN b i = capN a i) (hphi : phi vals E b = phi vals E a)
    (hact : ∀ i, actOf b i = actOf a i) (hexit : ∀ i, exitOf b i = exitOf a i)
    (hwdr : ∀ i, wdrOf b i = wdrOf a i)
    (hslash : ∀ i, slashedOf b i = slashedOf a i)
    (hsize : sizeOf b = sizeOf a) (hbsz : b.balances.val.size = a.balances.val.size)
    (hx1 : b.exitBalanceToConsume = a.exitBalanceToConsume)
    (hx2 : b.earliestExitEpoch = a.earliestExitEpoch)
    (hc1 : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume)
    (hc2 : b.earliestConsolidationEpoch = a.earliestConsolidationEpoch)
    (htrack : ∀ i ∈ vals, liveB st₀ E i.toNat = true →
      EbTrack downN aN (ebN b i.toNat) (ebN st₀ i.toNat) (eps0 st₀ i.toNat) (V i.toNat))
    (hle : ∀ i, i < sizeOf b → ebN b i ≤ maxN b i) (hmul : ∀ i, i < sizeOf b → ebN b i % incN = 0) :
    RunInv vals st₀ E CX CC b V W tag Γp B := by
  have e10 := exitedCount_eq hsize hexit
  refine ⟨fun i hi hl => by rw [hcap]; exact I.cap i hi hl, by rw [hphi]; exact I.bud, htrack,
    fun i h1 h2 => by rw [hact]; exact I.actOnce i h1 h2,
    fun i h1 h2 => by rw [hexit]; exact I.exitOnce i h1 h2,
    fun i hi h1 h2 h3 => I.newExit i hi h1 h2 (by rw [← hexit]; exact h3),
    by rw [hx1, hx2]; exact I.churnX.of_exit_eq hexit,
    by rw [hc1, hc2]; exact I.churnC.of_exit_eq hexit, ?_,
    fun i hi hl hs => by rw [hwdr]; exact I.live i hi hl (by rw [← hsize]; exact hs),
    by rw [hsize]; exact I.sizeLe, by rw [hx2, e10]; exact I.eeLe, by rw [hc2, e10]; exact I.ceeLe,
    fun i hi hs => by
      rw [hwdr]; exact I.slashInv i (by rw [← hsize]; exact hi) (by rw [← hslash]; exact hs)⟩
  · obtain ⟨s1, -, -, s4, s5⟩ := I.shape
    refine ⟨?_, hle, hmul, fun i hi hx => ?_, fun i hi hs => ?_⟩
    · rw [hbsz, s1]; exact hsize.symm
    · rw [hwdr]; exact s4 i (by rw [← hsize]; exact hi) (by rw [← hexit]; exact hx)
    · rw [hexit]; exact s5 i (by rw [← hsize]; exact hi) (by rw [← hslash]; exact hs)

omit [Preset] [HasherTag] in
/-- A multiple of `inc` capped at a multiple of `inc` is a multiple of `inc`. -/
theorem ebUpdate_mul {inc down up eb b m : Nat} (heb : eb % inc = 0) (hm : m % inc = 0) :
    ebUpdate inc down up eb b m % inc = 0 := by
  unfold ebUpdate
  split
  · rcases Nat.le_total (b - b % inc) m with h | h
    · rw [Nat.min_eq_left h]
      exact Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm
    · rw [Nat.min_eq_right h]; exact hm
  · exact heb

/-- **The effective-balance update keeps the invariant**, with the same ghosts. -/
theorem RunInv.ebuStep {vals : List ValidatorIndex} {st₀ a : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B : Nat} (C : DriftConsts)
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (h64 : sizeOf a < 2 ^ 64)
    (hbal : ∀ i, i < sizeOf a → balN a i + downN < 2 ^ 64)
    (heb : ∀ i, i < sizeOf a → ebN a i + upN < 2 ^ 64) :
    RunInv vals st₀ E CX CC ((List.range' 0 a.validators.size).foldl ebuBody a) V W tag Γp B := by
  have hsz : a.validators.size = sizeOf a := rfl
  obtain ⟨e, hs, hlo, -⟩ := ebuFold_spec a (by rw [hsz]; omega) a.validators.size (Nat.le_refl _)
  generalize hr : (List.range' 0 a.validators.size).foldl ebuBody a = r at e hs hlo
  have hsize : sizeOf r = sizeOf a := hs
  have hsr : r.validators.val.size = a.validators.val.size := hs
  have hbals : r.balances = a.balances := by rw [e]
  have hsz₀ : a.balances.val.size = a.validators.val.size := I.shape.sizes
  -- The validator of `r` at an index of the registry.
  have hget : ∀ i (hi : i < sizeOf a), r.validators.val[i]? =
      some (ebuVal (a.validators.val[i]'hi) (a.balances.val[i]'(Nat.lt_of_lt_of_eq hi hsz₀.symm))) := by
    intro i hi
    have hi' : i < a.validators.val.size := hi
    have h1 := hlo i hi
    rw [sszList_getElem!_eq, sszList_getElem!_eq, sszList_getElem!_eq,
      getElem!_pos a.validators.val i hi',
      getElem!_pos a.balances.val i (Nat.lt_of_lt_of_eq hi' hsz₀.symm)] at h1
    have hri : i < r.validators.val.size := Nat.lt_of_lt_of_eq hi' hsr.symm
    rw [getElem!_pos r.validators.val i hri] at h1
    rw [getElem?_pos r.validators.val i hri]
    exact congrArg some h1
  have hnone : ∀ i, sizeOf a ≤ i → r.validators.val[i]? = none := fun i hi =>
    Array.getElem?_eq_none (by rw [hsr]; exact hi)
  have hnone' : ∀ i, sizeOf a ≤ i → a.validators.val[i]? = none := fun i hi =>
    Array.getElem?_eq_none hi
  -- Every read but the effective balance stays.
  have hfield : ∀ (f : Validator → Nat) (dflt : Nat), (∀ v bal, f (ebuVal v bal) = f v) → ∀ i : Nat,
      (match r.validators.val[i]? with | some v => f v | none => dflt) =
        (match a.validators.val[i]? with | some v => f v | none => dflt) := by
    intro f dflt hf i
    by_cases hi : i < sizeOf a
    · rw [hget i hi, getElem?_pos a.validators.val i hi]
      exact hf _ _
    · rw [hnone i (by omega), hnone' i (by omega)]
  have hkeep : ∀ (f : Validator → Nat), (∀ v (x : Gwei), f { v with effectiveBalance := x } = f v) →
      ∀ v bal, f (ebuVal v bal) = f v := fun f hf v bal => by rw [ebuVal_eq]; exact hf _ _
  have hmax : ∀ i, maxN r i = maxN a i := fun i =>
    hfield (fun v => (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat) 0
      (hkeep (fun v => (EthCLSpecs.Heze.getMaxEffectiveBalance v).toNat) fun _ _ => rfl) i
  have hact : ∀ i, actOf r i = actOf a i := hfield (fun v => v.activationEpoch.toNat) 0
    (hkeep (fun v => v.activationEpoch.toNat) fun _ _ => rfl)
  have hexit : ∀ i, exitOf r i = exitOf a i := hfield (fun v => v.exitEpoch.toNat) _
    (hkeep (fun v => v.exitEpoch.toNat) fun _ _ => rfl)
  have hwdr : ∀ i, wdrOf r i = wdrOf a i := hfield (fun v => v.withdrawableEpoch.toNat) _
    (hkeep (fun v => v.withdrawableEpoch.toNat) fun _ _ => rfl)
  have hslash : ∀ i, slashedOf r i = slashedOf a i := fun i => by
    unfold slashedOf
    by_cases hi : i < sizeOf a
    · rw [hget i hi, getElem?_pos a.validators.val i hi, ebuVal_eq]
    · rw [hnone i (by omega), hnone' i (by omega)]
  have hcap : ∀ i, capN r i = capN a i := fun i => by
    unfold capN balN
    rw [hbals, hmax]
  have hphi : phi vals E r = phi vals E a := by
    have hg : gSl vals r = gSl vals a := by
      unfold gSl
      rw [hsize]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      rw [hslash, hmax]
    have hc : gCons E r = gCons E a := by
      unfold gCons
      rw [e]
      dsimp only
      congr 3
      funext q
      rw [show wdrOf { a with validators := r.validators } q.sourceIndex.toNat = wdrOf r q.sourceIndex.toNat
        from rfl, hwdr]
    unfold phi gPart
    rw [hg, hc, e]
  -- The new effective balance, on `Nat`.
  have heb' : ∀ i (hi : i < sizeOf a), ebN r i = ebUpdate incN downN upN (ebN a i) (balN a i)
      (maxN a i) := by
    intro i hi
    have hb : balN a i = (a.balances.val[i]'(by rw [hsz₀]; exact hi)).toNat := by
      unfold balN; rw [getElem?_pos a.balances.val i (by rw [hsz₀]; exact hi)]; rfl
    have he : ebN a i = (a.validators.val[i]'hi).effectiveBalance.toNat := by
      unfold ebN; rw [getElem?_pos a.validators.val i hi]
    have hm : maxN a i = (EthCLSpecs.Heze.getMaxEffectiveBalance (a.validators.val[i]'hi)).toNat := by
      unfold maxN; rw [getElem?_pos a.validators.val i hi]
    rw [hb, he, hm]
    show (match r.validators.val[i]? with
      | some v => v.effectiveBalance.toNat | none => 0) = _
    rw [hget i hi]
    exact ebuVal_toNat _ _ (by rw [← hb]; exact hbal i hi) (by rw [← he]; exact heb i hi)
  refine I.transfer hcap hphi hact hexit hwdr hslash hsize (by rw [hbals]) (by rw [e]) (by rw [e])
    (by rw [e]) (by rw [e]) ?_ ?_ ?_
  · intro i hi hl
    by_cases hia : i.toNat < sizeOf a
    · refine EbTrack.step (I.track i hi hl) ?_ ?_ (I.cap i hi hl)
      · rw [heb' _ hia]
        exact ebUpdate_near C.incPos C.downLe (I.shape.ebLe _ hia)
      · intro hne
        rw [heb' _ hia] at hne
        exact ebUpdate_far C.downLe C.downLt (I.shape.ebLe _ hia) (I.shape.ebMul _ hia)
          (by unfold maxN; rw [getElem?_pos a.validators.val _ hia]; exact C.maxMul _) hne
    · have : ebN r i.toNat = ebN a i.toNat := by
        unfold ebN; rw [hnone _ (by omega), hnone' _ (by omega)]
      rw [this]; exact I.track i hi hl
  · intro i hi
    rw [hsize] at hi
    rw [heb' _ hi, hmax]
    exact ebUpdate_le_cap _ _ _ (I.shape.ebLe _ hi)
  · intro i hi
    rw [hsize] at hi
    rw [heb' _ hi]
    exact ebUpdate_mul (I.shape.ebMul _ hi)
      (by unfold maxN; rw [getElem?_pos a.validators.val _ hi]; exact C.maxMul _)

end

end EthCLSpecs.Proofs.Heze
