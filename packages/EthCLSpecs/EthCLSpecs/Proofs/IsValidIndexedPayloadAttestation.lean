import EthCLSpecs.Gloas.Operations
import SizzLean.Proofs.SSZListGetElem

/-!
# `EthCLSpecs.Proofs.IsValidIndexedPayloadAttestation`: a two-layer characterization

An exact backend-generic characterization of
`EthCLSpecs.Gloas.isValidIndexedPayloadAttestation` (`Gloas/Operations.lean:424-435`).

**Layer 1** (`isValidIndexedPayloadAttestation_eq_true_iff_checks`) restates the
function's `if` / `||` / `!` control flow as a plain conjunction, one conjunct per
gate, with the two `Array.all`-based gates (adjacent nondecreasing check, in-range)
left exactly as the implementation's own literal booleans.

**Layer 2** (`isValidIndexedPayloadAttestation_eq_true_iff`) bridges those literal
gates into named propositions: non-empty, adjacent nondecreasing, every index in
range, and the configured `[CryptoBackend]` returning `true` on the exact pubkey
array, signing root, domain, and epoch the implementation computes.

**Why Layer 2's in-range gate binds a proof.** The implementation reads each pubkey
with `validators[i.toNat]!`, which silently yields `default` past the end of the
registry. Layer 2 states the in-range gate as `∃ hRange : ∀ i ∈ idx, …`, so the
bound is in scope for the signature conjunct, whose pubkey array is then built by
`Array.attach` with genuine in-bounds proofs. No `!` survives into the semantic
statement, and the reading is unconditional. The `∃` is invisible in use: callers
still build the whole right-hand side with `⟨h1, h2, h3, h4⟩` and still project the
bound out with `.2.2.1`, since a `Prop`-valued binder is proof-irrelevant.

Layer 1 keeps `validators[i.toNat]!` on purpose. Mirroring the implementation's
literal gates is that layer's entire job, and the implementation panics-by-default
there.

**Shared scope.** Sortedness is deliberately adjacent and non-strict (the PTC can
repeat a validator). This module does not assert uniqueness, full `List.Pairwise`
sortedness, or `Array.qsort` correctness. The signature conjunct names a backend
call returning `true`, not a cryptographic soundness claim. No mathlib.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (CryptoBackend HasherTag blsFastAggregateVerify computeSigningRoot)
open scoped EthCLLib.Spec
open EthCLSpecs.Gloas (Preset ValidatorIndex)
open EthCLSpecs.Gloas.Const (domainPtcAttester)
open EthCLSpecs.Gloas
  (State IndexedPayloadAttestation isValidIndexedPayloadAttestation getDomain computeEpochAtSlot)
open SizzLean.Proofs (sszListMap_getElem!_eq_attachMap)

/-! ## Layer 1: the literal characterization -/

/-- Exact backend-generic characterization using the function's literal
`Array.all` validation gates. -/
theorem isValidIndexedPayloadAttestation_eq_true_iff_checks [Preset] [HasherTag] [CryptoBackend]
    (state : State) (a : IndexedPayloadAttestation) :
    isValidIndexedPayloadAttestation state a = true ↔
      let idx := a.attestingIndices.toArray
      let validators := sszGet state validators
      idx.size ≠ 0 ∧
      (Array.range (idx.size - 1)).all
          (fun i => idx[i]?.getD default ≤ idx[i + 1]?.getD default) = true ∧
      idx.all (fun i => i.toNat < validators.size) = true ∧
      blsFastAggregateVerify (idx.map (fun i => (validators[i.toNat]!).pubkey))
        (computeSigningRoot a.data
          (getDomain state domainPtcAttester (computeEpochAtSlot a.data.slot)))
        a.signature = true := by
  simp [isValidIndexedPayloadAttestation, and_assoc]

/-! ## Layer 2: private core-only bridge lemmas, then the public semantic theorem -/

/-- Bridges the adjacent nondecreasing check
`isValidIndexedPayloadAttestation` performs (`Array.range` + `all` + `Option.getD`) into
an indexed inequality between consecutive elements. -/
private theorem indexedPayloadAttestation_adjacentNondecreasing_iff (idx : Array ValidatorIndex) :
    (Array.range (idx.size - 1)).all
        (fun i => idx[i]?.getD default ≤ idx[i + 1]?.getD default) = true ↔
      ∀ i (h : i + 1 < idx.size), idx[i]'(by omega) ≤ idx[i + 1]'h := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have hi' : i < (Array.range (idx.size - 1)).size := by rw [Array.size_range]; omega
    have h' := h i hi'
    rw [Array.getElem_range hi'] at h'
    rwa [Array.getElem?_eq_getElem (show i < idx.size by omega),
      Array.getElem?_eq_getElem (show i + 1 < idx.size by omega), Option.getD_some,
      Option.getD_some, decide_eq_true_eq] at h'
  · intro h i hi
    have hi' : i < idx.size - 1 := by simpa [Array.size_range] using hi
    rw [Array.getElem_range hi]
    rw [Array.getElem?_eq_getElem (show i < idx.size by omega),
      Array.getElem?_eq_getElem (show i + 1 < idx.size by omega), Option.getD_some,
      Option.getD_some, decide_eq_true_eq]
    exact h i (by omega)

/-- Bridges the in-range check `isValidIndexedPayloadAttestation` performs
(`Array.all` over the raw elements) into a membership-indexed bound. The bound is an
arbitrary `n`, the validator-registry size the caller instantiates it at plays no
part in the argument. Membership rather than position, because the bound's consumer
is the pubkey map below, which reads `validators` at an element of `idx`. -/
private theorem indexedPayloadAttestation_indicesInRange_iff
    (n : Nat) (idx : Array ValidatorIndex) :
    idx.all (fun i => i.toNat < n) = true ↔ ∀ i ∈ idx, i.toNat < n := by
  simp only [Array.all_eq_true', decide_eq_true_eq]

/-- Public semantic characterization: non-empty, adjacent-nondecreasing, in-range
indices, and the configured `[CryptoBackend]` returning `true` on the
implementation's exact aggregate-verification call. The in-range conjunct binds its
proof so the pubkey array can be read in bounds; see the module docstring. -/
theorem isValidIndexedPayloadAttestation_eq_true_iff [Preset] [HasherTag] [CryptoBackend]
    (state : State) (a : IndexedPayloadAttestation) :
    isValidIndexedPayloadAttestation state a = true ↔
      let idx := a.attestingIndices.toArray
      let validators := sszGet state validators
      idx.size ≠ 0 ∧
      (∀ i (h : i + 1 < idx.size), idx[i]'(by omega) ≤ idx[i + 1]'h) ∧
      ∃ hRange : ∀ i ∈ idx, i.toNat < validators.size,
        blsFastAggregateVerify
          (idx.attach.map (fun i => (validators[i.1.toNat]'(hRange i.1 i.2)).pubkey))
          (computeSigningRoot a.data
            (getDomain state domainPtcAttester (computeEpochAtSlot a.data.slot)))
          a.signature = true := by
  rw [isValidIndexedPayloadAttestation_eq_true_iff_checks]
  simp only [indexedPayloadAttestation_adjacentNondecreasing_iff,
    indexedPayloadAttestation_indicesInRange_iff]
  -- Only the last two conjuncts change shape; the first two pass through untouched.
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · rintro ⟨hRange, hVerify⟩
    exact ⟨hRange, by rwa [sszListMap_getElem!_eq_attachMap _ _ _ _ hRange] at hVerify⟩
  · rintro ⟨hRange, hVerify⟩
    exact ⟨hRange, by rwa [sszListMap_getElem!_eq_attachMap _ _ _ _ hRange]⟩

end EthCLSpecs.Proofs
