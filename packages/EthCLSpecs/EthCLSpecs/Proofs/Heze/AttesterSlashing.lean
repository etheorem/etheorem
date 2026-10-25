import EthCLSpecs.Proofs.Heze.LatestMessages
import EthCLSpecs.Proofs.Heze.SlotsIncrease
import EthCLSpecs.Proofs.Heze.Churn
import EthCLSpecs.Proofs.Heze.Time

/-!
# `EthCLSpecs.Proofs.Heze.AttesterSlashing`: the slashing conditions and their acceptance

## The slashing test

`is_slashable_attestation_data` (`electra/beacon-chain.md`, inherited by Heze) accepts two
attestation data in two cases:

- a double vote: two data with different roots and one target epoch;
- a surround vote: the first vote surrounds the second. Its source is earlier, and its target
  is later.

`isSlashableAttestationData_iff` states the test as these two cases. The double vote compares
roots. So two different data with one target epoch are a double vote, or the two
data are an SSZ root collision (`isSlashableAttestationData_of_ne`).

## The acceptance

`process_attester_slashing` has four asserts: the data are slashable, the two indexed
attestations are valid, and the loop slashed at least one validator. The loop runs over the
sorted intersection of the two index lists. It slashes each index that is in range and
slashable in the state it reads.

`processAttesterSlashing_run_not_assert` takes the four conditions: the data are slashable,
both validity reads return `true`, and a validator of both lists is slashable. Then the run
does not reject with an assert. The run can still fail in `slashValidator`. Its exit epoch
(`initiateValidatorExit`) reads the exit churn limit, a checked sum of the active balances.
It then runs the checked `computeActivationExitEpoch` and
`reserveChurn`, and its balance increases are checked `uint64` additions. Its balance
writes read the balances through `sszGetIdx`. So the theorem excludes the `.assert` class
only. The sort of the intersection is a hypothesis (`QsortMem`, `LatestMessages.lean`).

The loop argument needs no frame lemma for `slashValidator`. Each slash sets the flag
`slashedAny`. So until a slash sets the flag, the state does not change.
At the common slashable index, the test reads the start state and passes
(`forIn_bool_found`).

The three converse lemmas state that each of the first three asserts rejects when its
test returns `false`. A validity read that faults ends the run with its own error.

## The no-assert rules

`NoAssert x` says that no run of `x` rejects with `.assert`. The rules in the first section
build it through a `do` block: `pure`, `get`, `set`, `modifyThe`, a bind, an `if`, an index
read through `liftErr`, a checked computation through `liftErr` that never rejects with an
assert (`noAssert_liftErr_of`), `checkedAdd`, and `throwArithmetic`. `noAssert_slashValidator` applies them to
`slashValidator`, which has no assert. The rules are generic in the state type.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (pureState runPure runPure_eq run_bind run_pure except_bind_ok
  except_bind_error run_bind_eq_ok run_get_bind_eq_ok run_ite_eq_ok)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config BeaconState AttestationData AttesterSlashing ValidatorIndex
  isSlashableAttestationData isValidIndexedAttestation processAttesterSlashing slashValidator
  isSlashableValidator currentEpochOf)

/-! ## The no-assert rules -/

section NoAssert
variable {σ α β : Type}

/-- No run of `x` rejects with an assert. Other rejects, such as `.outOfBounds` and
`.arithmetic`, can still occur. -/
def NoAssert (x : StateT σ (Except StateTransitionError) α) : Prop :=
  ∀ s d, x.run s ≠ .error (.assert d)

/-- An action that succeeds from every state does not reject with an assert. -/
theorem noAssert_of_ok {x : StateT σ (Except StateTransitionError) α}
    (h : ∀ s, ∃ r, x.run s = .ok r) : NoAssert x := by
  intro s d he
  obtain ⟨r, hr⟩ := h s
  rw [hr] at he
  cases he

theorem noAssert_pure (a : α) : NoAssert (pure a : StateT σ (Except StateTransitionError) α) :=
  noAssert_of_ok fun s => ⟨(a, s), rfl⟩

theorem noAssert_get : NoAssert (get : StateT σ (Except StateTransitionError) σ) :=
  noAssert_of_ok fun s => ⟨(s, s), rfl⟩

theorem noAssert_set (t : σ) : NoAssert (set t : StateT σ (Except StateTransitionError) PUnit) :=
  noAssert_of_ok fun _ => ⟨(PUnit.unit, t), rfl⟩

/-- A fork's `modifyState` unfolds to `modifyThe`. -/
theorem noAssert_modifyThe (g : σ → σ) :
    NoAssert (modifyThe σ g : StateT σ (Except StateTransitionError) PUnit) :=
  noAssert_of_ok fun s => ⟨(PUnit.unit, g s), rfl⟩

/-- A bind rejects with an assert only when one of its two parts does. -/
theorem noAssert_bind {x : StateT σ (Except StateTransitionError) α}
    {f : α → StateT σ (Except StateTransitionError) β}
    (hx : NoAssert x) (hf : ∀ a, NoAssert (f a)) : NoAssert (x >>= f) := by
  intro s d he
  rw [run_bind] at he
  cases hr : x.run s with
  | error e =>
    rw [hr, except_bind_error] at he
    injection he with he
    exact hx s d (he ▸ hr)
  | ok p =>
    rw [hr, except_bind_ok] at he
    exact hf p.1 p.2 d he

theorem noAssert_ite {c : Prop} [Decidable c] {x y : StateT σ (Except StateTransitionError) α}
    (hx : NoAssert x) (hy : NoAssert y) : NoAssert (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact hx
  · rw [if_neg hc]; exact hy

/-- An index read through `liftErr` rejects with `.outOfBounds` only. -/
theorem noAssert_liftErr_index (e : Except SizzLean.Cache.IndexError α) :
    NoAssert (liftErr (m := StateT σ (Except StateTransitionError)) e) := by
  intro s d he
  cases e with
  | ok a => cases he
  | error ie => cases ie; cases he

/-- A checked computation lifted through `liftErr` does not reject with an assert when its own
value is never an assert reject. -/
theorem noAssert_liftErr_of {e : Except StateTransitionError α}
    (he : ∀ d, e ≠ .error (.assert d)) :
    NoAssert (liftErr (m := StateT σ (Except StateTransitionError)) e) := by
  intro s d h
  cases e with
  | ok a => cases h
  | error x =>
    injection h with h
    exact he d (congrArg Except.error h)

theorem noAssert_throwArithmetic (descr : String) :
    NoAssert (throwArithmetic (m := StateT σ (Except StateTransitionError)) (α := α) descr) := by
  intro s d he
  cases he

/-- A checked addition rejects with `.arithmetic` only. -/
theorem noAssert_checkedAdd (a b : UInt64) (descr : String) :
    NoAssert (checkedAdd (m := StateT σ (Except StateTransitionError)) a b descr) :=
  noAssert_ite (noAssert_throwArithmetic descr) (noAssert_pure _)

/-- A loop over a list whose body does not reject with an assert does not reject with an
assert. -/
theorem noAssert_forIn_list (body : α → β → StateT σ (Except StateTransitionError) (ForInStep β))
    (hb : ∀ a b, NoAssert (body a b)) :
    ∀ (l : List α) (b : β), NoAssert (forIn l b body) := by
  intro l
  induction l with
  | nil => intro b; exact noAssert_pure b
  | cons a rest ih =>
    intro b
    rw [List.forIn_cons]
    refine noAssert_bind (hb a b) (fun st => ?_)
    cases st with
    | done x => exact noAssert_pure x
    | yield x => exact ih x

end NoAssert

/-! ## Run facts for the loop -/

section Loop
variable {σ α : Type}

/-- A bind of `Except` values that fails: the first value failed, or it succeeded and the
continuation failed. -/
theorem except_bind_eq_error {ε β γ : Type} {x : Except ε β} {k : β → Except ε γ} {e : ε}
    (h : x >>= k = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ k a = .error e := by
  cases x with
  | error e' =>
    rw [except_bind_error] at h
    injection h with h
    exact .inl (h ▸ rfl)
  | ok a => exact .inr ⟨a, rfl, h⟩

/-- A successful run of `pure a` returns `a` and the start state. The proof stays at a
generic state type, so it never unfolds a fork's boxed state. -/
theorem run_pure_ok_eq {ε β : Type} {a : β} {s : σ} {r : β × σ}
    (h : (pure a : StateT σ (Except ε) β).run s = .ok r) : r = (a, s) := by
  rw [run_pure] at h
  exact (Except.ok.inj h).symm

/-- `Except.map` passes an error through unchanged. -/
theorem except_map_eq_error {ε β γ : Type} {f : β → γ} {x : Except ε β} {e : ε}
    (h : x.map f = .error e) : x = .error e := by
  cases x with
  | error e' =>
    injection h with h
    exact h ▸ rfl
  | ok a => cases h

/-- A list `mapM` in `Except` whose step never fails with `e` never fails with `e`. -/
theorem list_mapM_ne_error {ε β γ : Type} {f : β → Except ε γ} {e : ε}
    (hf : ∀ a, f a ≠ .error e) (l : List β) : l.mapM f ≠ .error e := by
  induction l with
  | nil => exact fun h => by cases h
  | cons a l ih =>
    rw [List.mapM_cons]
    intro h
    rcases except_bind_eq_error h with ha | ⟨b, -, h⟩
    · exact hf a ha
    · rcases except_bind_eq_error h with hl | ⟨bs, -, h⟩
      · exact ih hl
      · cases h

/-- A list `foldlM` in `Except` whose step never fails with `e` never fails with `e`. -/
theorem list_foldlM_ne_error {ε β γ : Type} {f : γ → β → Except ε γ} {e : ε}
    (hf : ∀ b a, f b a ≠ .error e) (l : List β) (init : γ) : l.foldlM f init ≠ .error e := by
  induction l generalizing init with
  | nil => exact fun h => by cases h
  | cons a l ih =>
    rw [List.foldlM_cons]
    intro h
    rcases except_bind_eq_error h with ha | ⟨b, -, h⟩
    · exact hf init a ha
    · exact ih b h

/-- A loop with a `Bool` flag that finds `i`. Three conditions on the body:

- From the flag `true`, it keeps the flag `true`.
- From the flag `false` and a state that satisfies `P`, it sets the flag, or it keeps the flag
  `false` and a state that satisfies `P`.
- At `i`, from the flag `false` and a state that satisfies `P`, it sets the flag.

Then a successful run over a list that holds `i`, from the flag `false` and a state that
satisfies `P`, returns the flag `true`. -/
theorem forIn_bool_found [DecidableEq α] (i : α) (P : σ → Prop)
    (body : α → Bool → StateT σ (Except StateTransitionError) (ForInStep Bool))
    (hT : ∀ a s r, (body a true).run s = .ok r → r.1 = .yield true)
    (hF : ∀ a s r, P s → (body a false).run s = .ok r →
      r.1 = .yield true ∨ (r.1 = .yield false ∧ P r.2))
    (hI : ∀ s r, P s → (body i false).run s = .ok r → r.1 = .yield true) :
    ∀ (l : List α) (b : Bool) (s : σ) (r : Bool × σ), (i ∈ l ∨ b = true) →
      (b = true ∨ P s) → (forIn l b body).run s = .ok r → r.1 = true := by
  intro l
  induction l with
  | nil =>
    intro b s r hm hp h
    rcases hm with hm | hb
    · cases hm
    · rw [List.forIn_nil, run_pure] at h
      injection h with h
      rw [← h]; exact hb
  | cons a rest ih =>
    intro b s r hm hp h
    rw [List.forIn_cons] at h
    obtain ⟨st, s1, hbody, hrest⟩ := run_bind_eq_ok _ _ _ _ h
    -- The step sets the flag, or it keeps the flag `false`, `i` is still ahead, and `P` holds.
    have key : st = .yield true ∨ (st = .yield false ∧ i ∈ rest ∧ P s1) := by
      cases b with
      | true => exact .inl (hT a s (st, s1) hbody)
      | false =>
        have hps : P s := hp.resolve_left (by simp)
        by_cases hai : a = i
        · subst hai; exact .inl (hI s (st, s1) hps hbody)
        · rcases hF a s (st, s1) hps hbody with h1 | ⟨h1, h2⟩
          · exact .inl h1
          · have hmr : i ∈ rest := by
              rcases hm with hm | hm
              · rcases List.mem_cons.mp hm with he | he
                · exact absurd he.symm hai
                · exact he
              · cases hm
            exact .inr ⟨h1, hmr, h2⟩
    rcases key with rfl | ⟨rfl, hmr, hp1⟩
    · exact ih true s1 r (.inr rfl) (.inl rfl) hrest
    · exact ih false s1 r (.inl hmr) (.inr hp1) hrest

end Loop

/-! ## The slashing test -/

section Test
variable [Preset] [HasherTag]

/-- The slashing test of two attestation data: a double vote (different roots, one target
epoch) or a surround vote. -/
@[characterizes EthCLSpecs.Heze.isSlashableAttestationData]
theorem isSlashableAttestationData_iff (d₁ d₂ : AttestationData) :
    isSlashableAttestationData d₁ d₂ = true ↔
      (htr d₁ ≠ htr d₂ ∧ d₁.target.epoch = d₂.target.epoch) ∨
      (d₁.source.epoch < d₂.source.epoch ∧ d₂.target.epoch < d₁.target.epoch) := by
  simp [isSlashableAttestationData]

/-- Two different data with one target epoch are a double vote, or their roots collide. -/
theorem isSlashableAttestationData_of_ne (d₁ d₂ : AttestationData) (h : d₁ ≠ d₂)
    (he : d₁.target.epoch = d₂.target.epoch) :
    HtrCollision AttestationData ∨ isSlashableAttestationData d₁ d₂ = true := by
  by_cases hr : htr d₁ = htr d₂
  · exact Or.inl ⟨d₁, d₂, h, hr⟩
  · exact Or.inr ((isSlashableAttestationData_iff d₁ d₂).mpr (Or.inl ⟨hr, he⟩))

/-- The read of the start state, as a run. -/
private theorem run_get_pure (st : BeaconState) :
    (get : HezeRun EthCLSpecs.Heze.State).run (pureState st) = .ok (pureState st, pureState st) :=
  rfl

/-- A validity read that returns `b` keeps the start state. -/
private theorem run_valid_read [CryptoBackend] (st : BeaconState)
    (a : EthCLSpecs.Heze.IndexedAttestation) {b : Bool}
    (h : isValidIndexedAttestation (pureState st) a = .ok b) :
    (liftErr (isValidIndexedAttestation (pureState st) a) : HezeRun Bool).run (pureState st)
      = .ok (b, pureState st) :=
  EthCLLib.Proofs.run_liftErr_of_ok _ _ (by rw [h]; rfl)

end Test

/-! ## The acceptance -/

section Acceptance
variable [Preset] [HasherTag] [Config]

omit [HasherTag] [Config] in
/-- `compute_activation_exit_epoch` rejects with `.arithmetic` only
(`computeActivationExitEpoch_eq`). -/
theorem computeActivationExitEpoch_not_assert (e : EthCLSpecs.Heze.Epoch) (d : String) :
    (EthCLSpecs.Heze.computeActivationExitEpoch e : Except StateTransitionError _)
      ≠ .error (.assert d) := by
  rw [computeActivationExitEpoch_eq]
  split
  · exact fun h => by cases h
  · split <;> exact fun h => by cases h

omit [Preset] [HasherTag] [Config] in
/-- `reserveChurn` rejects with `.arithmetic` only. Each case is one of the four results of
`Churn.lean`: the balance fits, the limit is zero, every sum stays below `2 ^ 64`, or one
reaches it. -/
theorem reserveChurn_not_assert (balance consume perEpoch earliest : UInt64) (d : String) :
    (EthCLSpecs.Heze.reserveChurn balance consume perEpoch earliest :
      Except StateTransitionError _) ≠ .error (.assert d) := by
  intro h
  by_cases hfit : balance ≤ consume
  · rw [reserveChurn_fits _ _ _ _ hfit] at h
    cases h
  have hlt : consume < balance := UInt64.lt_iff_toNat_lt.mpr
    (Nat.lt_of_not_le fun h' => hfit (UInt64.le_iff_toNat_le.mpr h'))
  by_cases hp : perEpoch = 0
  · subst hp
    rw [reserveChurn_zero _ _ _ hlt] at h
    cases h
  have hp' : 0 < perEpoch.toNat :=
    Nat.pos_of_ne_zero fun hz => hp (UInt64.toNat_inj.mp hz)
  -- The overflow case: some checked result reaches `2 ^ 64`.
  have hover : (2 ^ 64 ≤ earliest.toNat +
        EthCLSpecs.Proofs.Fulu.churnEpochs balance consume perEpoch ∨
      2 ^ 64 ≤ EthCLSpecs.Proofs.Fulu.churnEpochs balance consume perEpoch * perEpoch.toNat ∨
      2 ^ 64 ≤ consume.toNat +
        EthCLSpecs.Proofs.Fulu.churnEpochs balance consume perEpoch * perEpoch.toNat) →
      False := fun hb => by
    obtain ⟨_, he⟩ := reserveChurn_overflow _ _ _ earliest hlt hp' hb
    rw [he] at h
    cases h
  by_cases h1 : earliest.toNat + EthCLSpecs.Proofs.Fulu.churnEpochs balance consume perEpoch
      < 2 ^ 64
  · by_cases h2 : EthCLSpecs.Proofs.Fulu.churnEpochs balance consume perEpoch * perEpoch.toNat
        < 2 ^ 64
    · by_cases h3 : consume.toNat +
          EthCLSpecs.Proofs.Fulu.churnEpochs balance consume perEpoch * perEpoch.toNat < 2 ^ 64
      · obtain ⟨_, _, hok, -⟩ := reserveChurn_ok _ _ _ _ hlt hp' h1 h2 h3
        rw [hok] at h
        cases h
      · exact hover (.inr (.inr (Nat.le_of_not_lt h3)))
    · exact hover (.inr (.inl (Nat.le_of_not_lt h2)))
  · exact hover (.inl (Nat.le_of_not_lt h1))

/-- `slashValidator` has no assert. It can reject on an index read, a checked addition, or a
checked churn computation only. -/
theorem noAssert_slashValidator (i : ValidatorIndex) :
    NoAssert (slashValidator (StateTransition := HezeRun) i) := by
  -- `get_exit_churn_limit` reads `get_total_active_balance`, and through it
  -- `get_total_balance`: index reads of the effective balances, then a checked sum. Neither
  -- rejects with an assert, at the box state that the run reads.
  have hchurn : ∀ (st : EthCLSpecs.Heze.State) (d : String),
      EthCLSpecs.Heze.getExitChurnLimit st ≠ .error (.assert d) := by
    intro st d h
    unfold EthCLSpecs.Heze.getExitChurnLimit EthCLSpecs.Heze.getTotalActiveBalance
      EthCLSpecs.Heze.getTotalBalance at h
    rcases except_bind_eq_error h with he | ⟨t, -, h⟩
    · rcases except_bind_eq_error he with he | ⟨bals, -, he⟩
      · -- The reads of the effective balances.
        rw [Array.mapM_eq_mapM_toList] at he
        refine list_mapM_ne_error (fun i hi => ?_) _ (except_map_eq_error he)
        simp only [sszGetIdx] at hi
        split at hi <;> cases hi
      · rcases except_bind_eq_error he with he | ⟨t, -, he⟩
        · -- The checked sum.
          rw [← Array.foldlM_toList] at he
          refine list_foldlM_ne_error (fun b a hb => ?_) _ _ he
          unfold checkedAdd at hb
          split at hb <;> cases hb
        · cases he
    · cases h
  unfold slashValidator EthCLSpecs.Heze.initiateValidatorExit
    EthCLSpecs.Heze.computeExitEpochAndUpdateChurn EthCLSpecs.Heze.decreaseBalance
    EthCLSpecs.Heze.increaseBalance EthCLSpecs.Heze.modifyState sszGetIdx
  repeat' first
    | exact noAssert_pure _
    | exact noAssert_get
    | exact noAssert_set _
    | exact noAssert_modifyThe _
    | exact noAssert_liftErr_index _
    | exact noAssert_liftErr_of (computeActivationExitEpoch_not_assert _)
    | exact noAssert_liftErr_of (reserveChurn_not_assert _ _ _ _)
    | with_reducible exact noAssert_liftErr_of (hchurn _)
    | exact noAssert_checkedAdd _ _ _
    | exact noAssert_throwArithmetic _
    | refine noAssert_bind ?_ (fun _ => ?_)
    | refine noAssert_ite ?_ ?_

variable [CryptoBackend]

/-- The four asserts of `processAttesterSlashing` pass: the data are slashable, both indexed
attestations are valid, and a validator of both index lists is slashable. Then the run does not
reject with an assert. The slashes can still fail on an arithmetic fault or an index. -/
@[characterizes EthCLSpecs.Heze.processAttesterSlashing]
theorem processAttesterSlashing_run_not_assert (hq : QsortMem) (st : BeaconState)
    (asl : AttesterSlashing)
    (hs : isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true)
    (h₁ : isValidIndexedAttestation (pureState st) asl.attestation1 = .ok true)
    (h₂ : isValidIndexedAttestation (pureState st) asl.attestation2 = .ok true)
    (hi : ∃ i ∈ asl.attestation1.attestingIndices.toArray,
      i ∈ asl.attestation2.attestingIndices.toArray ∧
      ∃ hlt : i.toNat < st.validators.toArray.size,
        isSlashableValidator st.validators.toArray[i.toNat] (currentEpochOf (pureState st))
          = true)
    (d : String) :
    runPure (processAttesterSlashing (StateTransition := HezeRun) asl) st ≠ .error (.assert d) := by
  obtain ⟨i, hi1, hi2, hlt, hsl⟩ := hi
  intro h
  rw [runPure_eq] at h
  have h' := except_map_eq_error h
  clear h
  unfold processAttesterSlashing at h'
  -- The three asserts read the start state and pass. The two validity reads return `true`.
  have hl₁ := run_valid_read st asl.attestation1 h₁
  have hl₂ := run_valid_read st asl.attestation2 h₂
  simp only [run_bind, run_get_pure, except_bind_ok, hs, hl₁, hl₂, if_true, run_pure] at h'
  rw [← Array.forIn_toList] at h'
  rcases except_bind_eq_error h' with he | ⟨p, hp, hk⟩
  · -- The loop rejected. Its body reads, tests, and slashes, and none of these asserts.
    refine noAssert_forIn_list _ (fun a b => ?_) _ _ _ _ he
    repeat' first
      | exact noAssert_pure _
      | exact noAssert_get
      | exact noAssert_slashValidator _
      | refine noAssert_bind ?_ (fun _ => ?_)
      | refine noAssert_ite ?_ ?_
  · -- The loop succeeded. It met `i`, so it set the flag, and the last assert passes.
    have hmem : i ∈ ((arrayInter asl.attestation1.attestingIndices.toArray
        asl.attestation2.attestingIndices.toArray).qsort (· < ·)).toList := by
      rw [Array.mem_toList_iff, hq, arrayInter, Array.mem_filter]
      exact ⟨hi1, Array.contains_iff_mem.mpr hi2⟩
    have htrue := forIn_bool_found i (fun s => s = pureState st) _ ?hT ?hF ?hI _ false _ p
      (.inl hmem) (.inr rfl) hp
    · rw [htrue, if_pos rfl] at hk
      cases hk
    · -- From the flag `true`, both branches yield `true`.
      intro a s r h
      have h := run_get_bind_eq_ok _ _ _ h
      rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
      · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        rw [run_pure_ok_eq h]
      · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        rw [run_pure_ok_eq h]
    · -- From the flag `false`, a slash sets the flag, and a skip keeps the state.
      intro a s r hs h
      subst hs
      have h := run_get_bind_eq_ok _ _ _ h
      rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨-, h⟩
      · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        exact .inl (by rw [run_pure_ok_eq h])
      · obtain ⟨_, _, hu, h⟩ := run_bind_eq_ok _ _ _ _ h
        have hu := congrArg Prod.snd (run_pure_ok_eq hu)
        rw [run_pure_ok_eq h]
        exact .inr ⟨rfl, hu⟩
    · -- At `i` in the start state, the test passes, so the body slashes.
      intro s r hs h
      subst hs
      have h := run_get_bind_eq_ok _ _ _ h
      rcases run_ite_eq_ok h with ⟨-, h⟩ | ⟨hc, -⟩
      · obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        obtain ⟨_, _, -, h⟩ := run_bind_eq_ok _ _ _ _ h
        rw [run_pure_ok_eq h]
      · exfalso
        apply hc
        have hb : st.validators[i.toNat]! = st.validators.toArray[i.toNat] := by
          simp [hlt]
          rfl
        -- `(pureState st).view` is `st` by definition.
        show (decide (i.toNat < st.validators.size) &&
          isSlashableValidator st.validators[i.toNat]! (currentEpochOf (pureState st))) = true
        rw [hb, hsl]
        simpa using hlt

/-- The first assert rejects data that are not slashable. -/
theorem processAttesterSlashing_run_assert_of_not_slashable (st : BeaconState)
    (asl : AttesterSlashing)
    (hs : isSlashableAttestationData asl.attestation1.data asl.attestation2.data = false) :
    ∃ d, runPure (processAttesterSlashing (StateTransition := HezeRun) asl) st
      = .error (.assert d) := by
  apply Exists.intro
  rw [runPure_eq]
  unfold processAttesterSlashing
  simp only [run_bind, run_get_pure, except_bind_ok, hs, Bool.false_eq_true, if_false]
  rfl

/-- The second assert rejects an invalid first attestation. -/
theorem processAttesterSlashing_run_assert_of_invalid_first (st : BeaconState)
    (asl : AttesterSlashing)
    (hs : isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true)
    (h₁ : isValidIndexedAttestation (pureState st) asl.attestation1 = .ok false) :
    ∃ d, runPure (processAttesterSlashing (StateTransition := HezeRun) asl) st
      = .error (.assert d) := by
  apply Exists.intro
  rw [runPure_eq]
  unfold processAttesterSlashing
  simp only [run_bind, run_get_pure, except_bind_ok, hs, run_valid_read st _ h₁,
    Bool.false_eq_true, if_true, if_false, run_pure]
  rfl

/-- The third assert rejects an invalid second attestation. -/
theorem processAttesterSlashing_run_assert_of_invalid_second (st : BeaconState)
    (asl : AttesterSlashing)
    (hs : isSlashableAttestationData asl.attestation1.data asl.attestation2.data = true)
    (h₁ : isValidIndexedAttestation (pureState st) asl.attestation1 = .ok true)
    (h₂ : isValidIndexedAttestation (pureState st) asl.attestation2 = .ok false) :
    ∃ d, runPure (processAttesterSlashing (StateTransition := HezeRun) asl) st
      = .error (.assert d) := by
  apply Exists.intro
  rw [runPure_eq]
  unfold processAttesterSlashing
  simp only [run_bind, run_get_pure, except_bind_ok, hs, run_valid_read st _ h₁,
    run_valid_read st _ h₂, Bool.false_eq_true, if_true, if_false, run_pure]
  rfl

end Acceptance

end EthCLSpecs.Proofs.Heze
