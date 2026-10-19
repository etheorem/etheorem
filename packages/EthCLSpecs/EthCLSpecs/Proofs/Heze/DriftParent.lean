import EthCLSpecs.Proofs.Heze.DriftCons

/-!
# `EthCLSpecs.Proofs.Heze.DriftParent`: the requests of the parent payload

`process_parent_execution_payload` applies the execution requests of the parent payload. A
withdrawal request exits a validator, reserves churn for a partial withdrawal, or does nothing.
A consolidation request switches a validator to compounding, consolidates two validators, or
does nothing. The other requests write no read of the invariant.

`ConsCtx` collects the facts that the consolidation requests need at the start of the block,
beside `OpsCtx`. The run of the requests keeps `OpsInv`, with `Γp` grown by at most one per withdrawal
request and the budget grown by at most `slashCost maxEBN` per consolidation request.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (KeepsUncached pureState run_bind_eq_ok run_bind_eq_ok_pure
  run_get_bind_eq_ok run_assert_bind_eq_ok run_pure_state_eq run_ite_eq_ok keepsUncached_bind
  keepsUncached_pure keepsUncached_forIn_sszList)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config State BeaconState ValidatorIndex Validator Gwei modifyState)

section
variable [Preset] [HasherTag]

/-- A larger count of reservations keeps the invariant. -/
theorem RunInv.mono_Γ {vals : List ValidatorIndex} {st₀ a : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp Γp' B : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (h : Γp ≤ Γp') :
    RunInv vals st₀ E CX CC a V W tag Γp' B :=
  { I with eeLe := Nat.le_trans I.eeLe (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _) }

/-- A larger budget keeps the invariant. -/
theorem RunInv.mono_B {vals : List ValidatorIndex} {st₀ a : BeaconState} {E CX CC : Nat}
    {V W : Nat → Nat} {tag : Nat → Bool} {Γp B B' : Nat}
    (I : RunInv vals st₀ E CX CC a V W tag Γp B) (h : B ≤ B') :
    RunInv vals st₀ E CX CC a V W tag Γp B' :=
  { I with bud := Nat.le_trans I.bud h }

theorem OpsInv.mono {vals : List ValidatorIndex} {st₀ a₀ s : BeaconState} {E CX CC Γp Γp' B B' : Nat}
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (h1 : Γp ≤ Γp') (h2 : B ≤ B') :
    OpsInv vals st₀ a₀ E CX CC Γp' B' s := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  exact ⟨⟨V, W, tag, (I.mono_Γ h1).mono_B h2⟩, hk⟩

/-- The consolidation churn of one epoch reads `AcKeep` alone. -/
theorem consChurn_congr [Config] {a b : BeaconState} (h : AcKeep a b)
    (h64 : a.validators.val.size < 2 ^ 64) : consChurn b = consChurn a := by
  unfold consChurn EthCLSpecs.Heze.getConsolidationChurnLimit
  rw [totalActive_congr h h64]

end

/-- A loop whose every step keeps `Q` at a cost `c`, while the cost stays within `Bmax`. -/
theorem forIn_list_ops_budget_le [Preset] [HasherTag] {δ : Type} (Q : Nat → BeaconState → Prop)
    (op : δ → HezeRun PUnit) (hk : ∀ d, KeepsUncached (op d)) (c Bmax : Nat) :
    ∀ (l : List δ), (∀ d ∈ l, ∀ (B : Nat) (s s' : BeaconState), B + c ≤ Bmax → Q B s →
        (op d).run (pureState s) = .ok ((), pureState s') → Q (B + c) s') →
      ∀ (B : Nat) (s s' : BeaconState), B + l.length * c ≤ Bmax → Q B s →
        (forIn l PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
          : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s') →
        Q (B + l.length * c) s' := by
  intro l
  induction l with
  | nil =>
    intro _ B s s' _ hs h
    rw [List.forIn_nil] at h
    rw [pureState_inj (run_pure_state_eq _ _ _ _ h)]
    simpa using hs
  | cons d rest ih =>
    intro hop B s s' hB hs h
    rw [List.forIn_cons] at h
    obtain ⟨step, s1, hb, hr⟩ :=
      run_bind_eq_ok_pure (keepsUncached_bind (hk d) (fun _ => keepsUncached_pure _)) h
    obtain ⟨⟨⟩, s0, hop1, hp⟩ := run_bind_eq_ok_pure (hk d) hb
    injection hp with hp
    injection hp with hstep hs1
    subst hstep
    rw [← pureState_inj hs1] at hr
    rw [List.length_cons, Nat.succ_mul] at hB ⊢
    have := ih (fun d' hd' => hop d' (List.mem_cons_of_mem _ hd')) (B + c) s0 s' (by omega)
      (hop d List.mem_cons_self B s s0 (by omega) hs hop1) hr
    rwa [Nat.add_assoc, Nat.add_comm c] at this

/-- `forIn_list_ops_budget_le` for an array. -/
theorem forIn_array_ops_budget_le [Preset] [HasherTag] {δ : Type} (Q : Nat → BeaconState → Prop)
    (op : δ → HezeRun PUnit) (hk : ∀ d, KeepsUncached (op d)) (c Bmax : Nat) (xs : Array δ)
    (hop : ∀ d ∈ xs, ∀ (B : Nat) (s s' : BeaconState), B + c ≤ Bmax → Q B s →
      (op d).run (pureState s) = .ok ((), pureState s') → Q (B + c) s')
    (B : Nat) (s s' : BeaconState) (hB : B + xs.size * c ≤ Bmax) (hs : Q B s)
    (h : (forIn xs PUnit.unit (fun d _ => op d >>= fun _ => pure (ForInStep.yield PUnit.unit))
      : HezeRun PUnit).run (pureState s) = .ok (PUnit.unit, pureState s')) :
    Q (B + xs.size * c) s' := by
  rw [← Array.forIn_toList] at h
  rw [← Array.length_toList] at hB ⊢
  exact forIn_list_ops_budget_le Q op hk c Bmax xs.toList
    (fun d hd => hop d (Array.mem_toList_iff.mp hd)) B s s' hB hs h

section
variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
/-- A run of `pure ()` keeps `OpsInv`, with the larger bounds. -/
theorem OpsInv.of_pure {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γp Γp' B B' : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (h1 : Γp ≤ Γp')
    (h2 : B ≤ B')
    (h : (pure () : HezeRun Unit).run (pureState s) = .ok ((), pureState s')) :
    OpsInv vals st₀ a₀ E CX CC Γp' B' s' := by
  rw [pureState_inj (run_pure_state_eq _ _ _ _ h)]
  exact hs.mono h1 h2

/-- **A withdrawal request keeps `OpsInv`, with one more reservation.** The amount of the
request stays below `2 ^ 62`. -/
theorem OpsInv.withdrawalRequest {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (hΓ : Γp + 1 ≤ Γc)
    (hd62 : EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 62)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (wr : EthCLSpecs.Heze.WithdrawalRequest)
    (hamt : wr.amount.toNat < 2 ^ 62)
    (h : (EthCLSpecs.Heze.processWithdrawalRequest (StateTransition := HezeRun) wr).run
      (pureState s) = .ok ((), pureState s')) :
    OpsInv vals st₀ a₀ E CX CC (Γp + 1) B s' := by
  have hle : Γp ≤ Γp + 1 := Nat.le_succ _
  unfold EthCLSpecs.Heze.processWithdrawalRequest at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure hle (Nat.le_refl _) h
  split at h
  · exact hs.of_pure hle (Nat.le_refl _) h
  rename_i idxN _
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure hle (Nat.le_refl _) h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure hle (Nat.le_refl _) h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure hle (Nat.le_refl _) h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure hle (Nat.le_refl _) h
  -- The pending-withdrawal read keeps the state.
  obtain ⟨pend, h⟩ := run_liftErr_bind_eq_ok h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · -- A full exit.
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact (hs.exit X (by omega) _ h).mono hle (Nat.le_refl _)
    · exact hs.of_pure hle (Nat.le_refl _) h
  -- A partial withdrawal: the balance read and the checked threshold keep the state.
  obtain ⟨bal, s1, hbal, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨-, rfl⟩ := sszGetIdx_run_ok hbal
  obtain ⟨thr, s1', hthr, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, -, -⟩ := checkedAdd_run_ok hthr
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  case inr => exact hs.of_pure hle (Nat.le_refl _) h
  obtain ⟨x, a1, hx, h⟩ :=
    EthCLLib.Proofs.run_bind_eq_ok_pure (keepsUncached_computeExitEpochAndUpdateChurn _) h
  -- The checked withdrawable epoch keeps the state and is the sum.
  obtain ⟨we, a2, hwe, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, hwe', -⟩ := checkedAdd_run_ok hwe
  subst hwe'
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨NX, ΓX, P, hn, hg⟩ := X.pre
  have P' := P.keep hk
  have hcnt : exitedCount s * maddX ≤ NX * maddX := by
    have := exitedCount_le s
    have := hk.size
    exact Nat.mul_le_mul_right _ (by omega)
  have hgam : (Γp + 1) * maddP ≤ ΓX * maddP := Nat.mul_le_mul_right _ (by omega)
  have hsm := P'.small
  -- The amount: at most the amount of the request.
  have hb62 : (umin (bal - EthCLSpecs.Heze.Const.minActivationBalance - pend)
      wr.amount).toNat < 2 ^ 62 := by
    rw [umin_toNat]; omega
  obtain ⟨hk', I'⟩ := I.partialReserve _ x hx _ rfl h P'.cl P'.cu X.consts.incPos P'.cur P'.curE
    P'.kE (by omega) P'.c62 hb62 hd62
  exact ⟨⟨V, W, tag, I'⟩, hk.trans hk'⟩

/-- The facts at the start of a block that a consolidation needs, beside `OpsCtx`. -/
structure ConsCtx (st₀ a₀ : BeaconState) (E CC : Nat) : Prop where
  cu : (consChurn a₀).toNat ≤ CC
  c62 : max st₀.consolidationBalanceToConsume.toNat CC < 2 ^ 62
  min0 : 0 < EthCLSpecs.Heze.Const.minActivationBalance.toNat
  minMax : EthCLSpecs.Heze.Const.minActivationBalance.toNat ≤ maxEBN
  d62 : EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 62
  small : ∃ NC, sizeOf a₀ + 1 ≤ NC ∧
    max st₀.earliestConsolidationEpoch.toNat (E + lagN) + NC * maddC < 2 ^ 62

omit [Config] [CryptoBackend] in
/-- An index that `validatorIndexByPubkey?` returns lies in the registry. -/
theorem validatorIndexByPubkey?_lt {s : BeaconState} {pk : EthCLSpecs.Heze.BLSPubkey} {n : Nat}
    (h : EthCLSpecs.Heze.validatorIndexByPubkey? (pureState s) pk = some n) :
    n < s.validators.val.size :=
  (Array.findIdx?_eq_some_iff_getElem.mp h).1

omit [Config] [CryptoBackend] in
/-- A valid switch to compounding names a validator with execution credentials. -/
theorem isValidSwitch_eth1 {s : BeaconState} {req : EthCLSpecs.Heze.ConsolidationRequest}
    (h : EthCLSpecs.Heze.isValidSwitchToCompoundingRequest (pureState s) req = true) {si : Nat}
    (hsi : EthCLSpecs.Heze.validatorIndexByPubkey? (pureState s) req.sourcePubkey = some si) :
    EthCLSpecs.Heze.hasEth1WithdrawalCredential (s.validators[si]!) = true := by
  unfold EthCLSpecs.Heze.isValidSwitchToCompoundingRequest at h
  split at h
  · cases h
  rw [hsi] at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i hc
    simpa using hc

omit [HasherTag] [Config] [CryptoBackend] in
/-- An execution credential is not a compounding credential. -/
theorem not_compounding_of_eth1 {v : Validator}
    (h : EthCLSpecs.Heze.hasEth1WithdrawalCredential v = true) :
    EthCLSpecs.Heze.hasCompoundingWithdrawalCredential v = false := by
  unfold EthCLSpecs.Heze.hasEth1WithdrawalCredential at h
  unfold EthCLSpecs.Heze.hasCompoundingWithdrawalCredential
  rw [beq_iff_eq.mp h]
  decide

omit [Config] [CryptoBackend] in
/-- A write of one validator that keeps its epochs and its effective balance keeps the reads of
the total active balance, whatever it writes to the balances. -/
theorem AcKeep.of_set {a b : BeaconState} {j : Nat} {v v' : Validator}
    (hv : a.validators.val[j]? = some v) (hbv : b.validators = a.validators.set! j v')
    (hslot : b.slot = a.slot) (heb : v'.effectiveBalance = v.effectiveBalance)
    (hact : v'.activationEpoch = v.activationEpoch) (hex : v'.exitEpoch = v.exitEpoch) :
    AcKeep a b := by
  have hj : j < a.validators.val.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hget : ∀ k, b.validators.val[k]? = if j = k then some v' else a.validators.val[k]? :=
    fun k => by rw [hbv]; exact getElem?_validators_set a j k _ hj
  have hc : EthCLSpecs.Heze.currentEpochOf (pureState b) =
      EthCLSpecs.Heze.currentEpochOf (pureState a) := by
    show EthCLSpecs.Heze.computeEpochAtSlot b.slot = EthCLSpecs.Heze.computeEpochAtSlot a.slot
    rw [hslot]
  refine ⟨hslot, ?_, fun k => ?_, fun k _ => ?_⟩
  · show b.validators.val.size = a.validators.val.size
    rw [hbv]; exact SizzLean.Proofs.sszListSet!_size _ _ _
  · unfold acB
    rw [hc, hget k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, hv]
      unfold EthCLSpecs.Heze.isActiveValidator
      dsimp only
      rw [hact, hex]
    · rw [if_neg hk]
  · unfold ebN
    rw [hget k]
    by_cases hk : j = k
    · subst hk; rw [if_pos rfl, hv]; dsimp only; rw [heb]
    · rw [if_neg hk]

omit [CryptoBackend] in
/-- **A switch to compounding keeps `OpsInv`, at the cost `slashCost maxEBN`.** -/
theorem OpsInv.switch {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (Y : ConsCtx st₀ a₀ E CC)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (i : ValidatorIndex)
    (hnc : ∀ v, s.validators.val[i.toNat]? = some v →
      EthCLSpecs.Heze.hasCompoundingWithdrawalCredential v = false)
    (h : (EthCLSpecs.Heze.switchToCompoundingValidator (StateTransition := HezeRun) i).run
      (pureState s) = .ok ((), pureState s')) :
    OpsInv vals st₀ a₀ E CX CC Γp (B + slashCost maxEBN) s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨v, hv, hbv, hsl, hq1, hq2, hd, hx1, hx2, hc1, hc2, hbal⟩ := switchToCompounding_run i s s' h
  exact ⟨⟨V, W, tag, I.switch X.nodup _ v hv (hnc v hv) Y.minMax hbv hq1 hq2 hd hx1 hx2 hc1 hc2 hbal⟩,
    hk.trans (AcKeep.of_set hv hbv hsl rfl rfl rfl)⟩

/-- **A consolidation keeps `OpsInv`.** The run reserves consolidation churn for the source
`j`, writes its exit, and queues the consolidation. -/
theorem OpsInv.consolidation {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (Y : ConsCtx st₀ a₀ E CC)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (j : Nat) (v : Validator)
    (hv : s.validators.val[j]? = some v)
    (hfar : v.exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch)
    (hlim : EthCLSpecs.Heze.Const.minActivationBalance <
      consChurn s)
    (q : EthCLSpecs.Heze.PendingConsolidation) (hq : q.sourceIndex.toNat = j)
    (h : (EthCLSpecs.Heze.computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun)
        v.effectiveBalance >>= fun x =>
      checkedAdd x EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay
        "process_consolidation_request: exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY" >>= fun we =>
      (modifyState fun state => EthCLSpecs.Heze.modValidator state (UInt64.ofNat j) fun u =>
        { u with exitEpoch := x, withdrawableEpoch := we }) >>=
        fun _ => (appendState pendingConsolidations q : HezeRun Unit)).run (pureState s)
      = .ok ((), pureState s')) :
    OpsInv vals st₀ a₀ E CX CC Γp B s' := by
  obtain ⟨⟨V, W, tag, I⟩, hk⟩ := hs
  obtain ⟨NX, ΓX, P, hn, hg⟩ := X.pre
  have P' := P.keep hk
  obtain ⟨NC, hNC, hcs⟩ := Y.small
  have hj : j < s.validators.val.size := (Array.getElem?_eq_some_iff.mp hv).1
  have hj64 : (UInt64.ofNat j).toNat = j :=
    EthCLLib.Proofs.toNat_ofNat_lt64 (Nat.lt_trans hj P'.h64)
  obtain ⟨x, s2, hx, h⟩ :=
    run_bind_eq_ok_pure (keepsUncached_computeConsolidationEpochAndUpdateChurn _) h
  obtain ⟨act, c, hactE, -, hres, hs2⟩ := computeConsolidationEpochAndUpdateChurn_run _ s hx
  subst hs2
  -- The checked withdrawable epoch keeps the state and is the sum.
  obtain ⟨we, s4, hwe, h⟩ := run_bind_eq_ok _ _ _ _ h
  obtain ⟨rfl, hwe', -⟩ := checkedAdd_run_ok hwe
  subst hwe'
  obtain ⟨⟨⟩, s3, h3, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e3 := EthCLLib.Proofs.run_modifyThe_eq_ok h3
  rw [modValidator_pureState] at e3
  subst e3
  obtain ⟨hlt, hb⟩ := appendConsolidation_run _ s' _ h
  have hget : (afterConsChurn s v.effectiveBalance x c).validators[(UInt64.ofNat j).toNat]! = v := by
    show s.validators[(UInt64.ofNat j).toNat]! = v
    rw [hj64, sszList_getElem!_eq, getElem!_pos s.validators.val j hj]
    exact (Array.getElem?_eq_some_iff.mp hv).2
  have hbv : s'.validators = s.validators.set! j
      (exitVal v x EthCLSpecs.Heze.Const.minValidatorWithdrawabilityDelay) := by
    subst hb
    show (afterConsChurn s v.effectiveBalance x c).validators.set! (UInt64.ofNat j).toNat _ = _
    rw [hget, hj64]
    rfl
  have hcl : (consChurn s).toNat ≤ CC := by
    rw [consChurn_congr hk P.h64]; exact Y.cu
  have hcnt : (exitedCount s + 1) * maddC ≤ NC * maddC := by
    have := exitedCount_le s
    have := hk.size
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨hk', W', tag', I'⟩ := I.consolidate X.nodup X.shape₀ j v hv hfar act x c hactE hres q hq
    (fun k => by rw [hbv]; exact getElem?_validators_set s j k _ hj)
    (by rw [hbv]; exact SizzLean.Proofs.sszListSet!_size _ _ _) (by subst hb; rfl) (by subst hb; rfl)
    (by subst hb; rw [SizzLean.Proofs.sszListPush_val, Array.toList_push]; rfl)
    (by subst hb; rfl) (by subst hb; rfl) (by subst hb; rfl)
    (by subst hb; rfl) (by subst hb; rfl) (by subst hb; rfl)
    (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlim)) hcl Y.min0 P'.cur P'.curE P'.kE
    (by omega) Y.c62
    (fun k _ => by unfold maxN; split; exact X.consts.maxLe _; exact Nat.zero_le _)
    X.consts.maxEB62 Y.d62
  exact ⟨⟨V, W', tag', I'⟩, hk.trans hk'⟩

/-- **A consolidation request keeps `OpsInv`, at the cost `slashCost maxEBN`.** -/
theorem OpsInv.consolidationRequest {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (Y : ConsCtx st₀ a₀ E CC)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B s) (req : EthCLSpecs.Heze.ConsolidationRequest)
    (h : (EthCLSpecs.Heze.processConsolidationRequest (StateTransition := HezeRun) req).run
      (pureState s) = .ok ((), pureState s')) :
    OpsInv vals st₀ a₀ E CX CC Γp (B + slashCost maxEBN) s' := by
  have hle : B ≤ B + slashCost maxEBN := Nat.le_add_right _ _
  have h64 : s.validators.val.size < 2 ^ 64 := by
    obtain ⟨NX, ΓX, P, -, -⟩ := X.pre
    have := hs.2.size
    have := P.h64
    unfold sizeOf at *
    omega
  unfold EthCLSpecs.Heze.processConsolidationRequest at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨hsw, h⟩ | ⟨-, h⟩
  · -- A switch to compounding.
    split at h
    · rename_i si hsi
      have hsiN := validatorIndexByPubkey?_lt hsi
      have hsi64 : (UInt64.ofNat si).toNat = si := EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)
      refine hs.switch X Y _ (fun v hv => ?_) h
      rw [hsi64] at hv
      have heth := isValidSwitch_eth1 hsw hsi
      rw [sszList_getElem!_eq, getElem!_pos s.validators.val si hsiN] at heth
      rw [(Array.getElem?_eq_some_iff.mp hv).2] at heth
      exact not_compounding_of_eth1 heth
    · exact hs.of_pure (Nat.le_refl _) hle h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure (Nat.le_refl _) hle h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · exact hs.of_pure (Nat.le_refl _) hle h
  -- The churn-limit read succeeds, so it returns `consChurn s`.
  cases hcl : EthCLSpecs.Heze.getConsolidationChurnLimit (pureState s) with
  | error e =>
    rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_error _ _ (by rw [hcl]; rfl),
      EthCLLib.Proofs.except_bind_error] at h
    cases h
  | ok lim =>
  rw [EthCLLib.Proofs.run_bind, EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [hcl]; rfl),
    EthCLLib.Proofs.except_bind_ok] at h
  have elim : consChurn s = lim := by
    unfold consChurn
    rw [hcl]
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hlim, h⟩
  · exact hs.of_pure (Nat.le_refl _) hle h
  obtain ⟨_, s0, h0, h⟩ := run_bind_eq_ok _ _ _ _ h
  have e0 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h0
  subst e0
  split at h
  · rename_i srcN tgtN hsrc htgt
    have hsN := validatorIndexByPubkey?_lt hsrc
    have hv : s.validators.val[srcN]? = some (s.validators.val[srcN]'hsN) :=
      getElem?_pos s.validators.val srcN hsN
    simp only [SizzLean.Proofs.view_uncachedBox, SizzLean.Repr.SSZList.toArray, hv,
      Option.getD_some] at h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hne, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    -- The pending-withdrawal read keeps the state.
    obtain ⟨_, h⟩ := run_liftErr_bind_eq_ok h
    rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
    · exact hs.of_pure (Nat.le_refl _) hle h
    obtain ⟨_, s1, h1, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e1 := EthCLLib.Proofs.run_pure_state_eq _ _ _ _ h1
    subst e1
    have hfar : (s.validators.val[srcN]'hsN).exitEpoch = EthCLSpecs.Heze.Const.farFutureEpoch := by
      unfold EthCLSpecs.Heze.hasNotInitiatedExit at hne
      simpa using hne
    refine (hs.consolidation X Y srcN _ hv hfar ?_ _
      (EthCLLib.Proofs.toNat_ofNat_lt64 (by omega)) h).mono (Nat.le_refl _) hle
    rw [elim]
    exact UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_not_le fun hc => hlim (UInt64.le_iff_toNat_le.mpr hc))
  · exact hs.of_pure (Nat.le_refl _) hle h

omit [Config] [CryptoBackend] in
/-- A step that keeps `econView`, after which the slot is the slot of the start of the block,
keeps `OpsInv`. -/
theorem OpsInv.of_econ_slot {vals : List ValidatorIndex} {st₀ a₀ s s' : BeaconState}
    {E CX CC Γp B : Nat} (hs : OpsInv vals st₀ a₀ E CX CC Γp B s)
    (he : econView s' = econView s) (hsl : s'.slot = a₀.slot) :
    OpsInv vals st₀ a₀ E CX CC Γp B s' :=
  hs.of_econ he (hsl.trans hs.2.slot.symm)

/-- **The parent payload keeps `OpsInv`**, with one reservation per withdrawal request and one
cost `slashCost maxEBN` per consolidation request. Each withdrawal request has an amount below
`2 ^ 62`. -/
theorem processParentExecutionPayload_ops {vals : List ValidatorIndex} {st₀ a₀ a b : BeaconState}
    {E CX CC Γc Γp B : Nat} (X : OpsCtx vals st₀ a₀ E CX Γc) (Y : ConsCtx st₀ a₀ E CC)
    (hs : OpsInv vals st₀ a₀ E CX CC Γp B a) (blk : EthCLSpecs.Heze.BeaconBlock)
    (hamt : ∀ wr ∈ blk.body.parentExecutionRequests.withdrawals.val, wr.amount.toNat < 2 ^ 62)
    (hΓ : Γp + blk.body.parentExecutionRequests.withdrawals.val.size ≤ Γc)
    (h : (EthCLSpecs.Heze.processParentExecutionPayload (StateTransition := HezeRun) blk).run
      (pureState a) = .ok ((), pureState b)) :
    OpsInv vals st₀ a₀ E CX CC (Γp + blk.body.parentExecutionRequests.withdrawals.val.size)
      (B + blk.body.parentExecutionRequests.consolidations.val.size * slashCost maxEBN) b := by
  have hsp := processParentExecutionPayload_frame_spine h
  have hslb : b.slot = a₀.slot := (congrArg (fun w => w.1) hsp).trans hs.2.slot
  unfold EthCLSpecs.Heze.processParentExecutionPayload at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  · have e : (pureState b).view = (pureState a).view := by frame_invert h
    change b = a at e
    subst e
    exact hs.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  obtain ⟨-, h⟩ := run_assert_bind_eq_ok _ _ _ _ h
  unfold EthCLSpecs.Heze.applyParentExecutionPayload at h
  have h := run_get_bind_eq_ok _ _ _ h
  dsimp only at h
  have hd62 := Y.d62
  -- The deposit requests.
  obtain ⟨_, s1, h1, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun d _ =>
    keepsUncached_bind (keepsUncached_processDepositRequest d)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t1 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC Γp B) _
    keepsUncached_processDepositRequest _
    (fun d _ s s' hq hr => hq.of_econ (processDepositRequest_frame_econ hr)
      (congrArg (fun w => w.1.1) (processDepositRequest_frame hr))) a s1 hs h1
  -- The withdrawal requests: one reservation each.
  obtain ⟨_, s2, h2, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun w _ =>
    keepsUncached_bind (keepsUncached_processWithdrawalRequest w)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t2 := forIn_array_ops_budget_le (fun g s => OpsInv vals st₀ a₀ E CX CC g B s) _
    keepsUncached_processWithdrawalRequest 1 Γc _
    (fun wr hm g s s' hg hq hr => hq.withdrawalRequest X hg hd62 wr (hamt wr hm) hr)
    Γp s1 s2 (by rw [Nat.mul_one]; exact hΓ) t1 h2
  rw [Nat.mul_one] at t2
  -- The consolidation requests: one cost each.
  obtain ⟨_, s3, h3, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun c _ =>
    keepsUncached_bind (keepsUncached_processConsolidationRequest c)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t3 := forIn_array_ops_budget
    (fun B' s => OpsInv vals st₀ a₀ E CX CC
      (Γp + blk.body.parentExecutionRequests.withdrawals.val.size) B' s) _
    keepsUncached_processConsolidationRequest (slashCost maxEBN) _
    (fun c _ B' s s' hq hr => hq.consolidationRequest X Y c hr) B s2 s3 t2 h3
  -- The builder requests.
  obtain ⟨_, s4, h4, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun bd _ =>
    keepsUncached_bind (keepsUncached_processBuilderDepositRequest bd)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t4 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC _ _) _
    keepsUncached_processBuilderDepositRequest _
    (fun d _ s s' hq hr => hq.of_econ (processBuilderDepositRequest_frame_econ hr)
      (congrArg (fun w => w.1.1) (processBuilderDepositRequest_frame hr)))
    s3 s4 t3 h4
  obtain ⟨_, s5, h5, h⟩ := run_bind_eq_ok_pure (keepsUncached_forIn_sszList _ (fun be _ =>
    keepsUncached_bind (keepsUncached_processBuilderExitRequest be)
      (fun _ => keepsUncached_pure _)) _ _) h
  have t5 := forIn_array_ops_inv (OpsInv vals st₀ a₀ E CX CC _ _) _
    keepsUncached_processBuilderExitRequest _
    (fun d _ s s' hq hr => hq.of_econ (processBuilderExitRequest_frame_econ hr)
      (congrArg (fun w => w.1.1) (processBuilderExitRequest_frame hr)))
    s4 s5 t4 h5
  -- The settlement and the two writes at the end keep `econView`.
  -- Each branch of the settlement ends in the two writes.
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  rotate_left
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  rotate_left
  rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
  -- Each branch: an append to the builder withdrawal queue, nothing, or a settlement. The
  -- two writes at the end keep `econView`.
  · -- The append: the `some` branch writes the queue only.
    obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok _ _ _ _ h
    have h6 := run_get_bind_eq_ok _ _ _ h6
    split at h6
    · rename_i s' heq
      have e6 := EthCLLib.Proofs.run_modifyThe_eq_ok h6
      obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp heq
      subst e6
      obtain ⟨⟨⟩, s7, h7, h⟩ := run_bind_eq_ok _ _ _ _ h
      have e7 := EthCLLib.Proofs.run_modifyThe_eq_ok h7
      subst e7
      have he : econBox (pureState b) = econBox (pureState s5) := by
        rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
        rfl
      exact t5.of_econ_slot he hslb
    · cases h6
  · -- No settlement.
    obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e6 := run_pure_state_eq _ _ _ _ h6
    subst e6
    obtain ⟨⟨⟩, s7, h7, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e7 := EthCLLib.Proofs.run_modifyThe_eq_ok h7
    subst e7
    have he : econBox (pureState b) = econBox (pureState s5) := by
      rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      rfl
    exact t5.of_econ_slot he hslb
  all_goals
    -- A settlement keeps `econView` (`settleBuilderPayment_frame_econ`).
    obtain ⟨⟨⟩, s6, h6, h⟩ := run_bind_eq_ok_pure (keepsUncached_settleBuilderPayment _) h
    have e6 := settleBuilderPayment_frame_econ h6
    obtain ⟨⟨⟩, s7, h7, h⟩ := run_bind_eq_ok _ _ _ _ h
    have e7 := EthCLLib.Proofs.run_modifyThe_eq_ok h7
    subst e7
    have he : econBox (pureState b) = econBox (pureState s6) := by
      rw [EthCLLib.Proofs.run_modifyThe_eq_ok h]
      rfl
    exact t5.of_econ_slot (he.trans e6) hslb

end

end EthCLSpecs.Proofs.Heze
