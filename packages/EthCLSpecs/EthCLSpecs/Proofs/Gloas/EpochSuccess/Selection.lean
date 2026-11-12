import EthCLSpecs.Gloas.EpochProcessing
import EthCLLib.Proofs.ZeroChunks

/-!
# `EthCLSpecs.Proofs.Gloas.EpochSuccess.Selection`: the balance-weighted selection fills

The Gloas counterpart of the Fulu module of the same name, over Gloas's progressive lists.

`compute_balance_weighted_selection` draws candidates until it has `size` of them, with a
`uint64` pass counter that faults at `2^64 - 1`. `cbwsAux_ok` shows the draw loop fills under the
hash premise `ZeroChunksOften`: each zero chunk accepts its candidate, and the loop's cached
random bytes always hold the chunk block of the current pass. The selection's own
`assert (total > 0)` needs a nonempty candidate list. The proposer and sync-committee selections
call it with the active validators of a future epoch.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs (pureState selectionChunk zeroChunkCount ZeroChunksOften zeroChunkCount_succ
  zeroChunkCount_of_le)
open EthCLLib.Spec (HasherTag sha le2 uint64ToBytes StateTransitionError)
open EthCLSpecs.Gloas

theorem cbwsAux_ok [Preset] [HasherTag] (indices effBals : Array Nat) (perm : Array ValidatorIndex)
    (seed : ByteArray) (total size : Nat) (shuffle : Bool) :
    ∀ (k i : Nat) (randomBytes : ByteArray) (selected : Array ValidatorIndex),
      UInt64.size - i = k →
      (i % 16 ≠ 0 → randomBytes = sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16)))) →
      size - selected.size ≤ zeroChunkCount seed i →
      ∃ r, cbwsAux indices effBals perm seed total size shuffle i randomBytes selected = .ok r := by
  intro k
  induction k with
  | zero =>
    intro i randomBytes selected hk hcache hcount
    rw [zeroChunkCount_of_le seed i (by omega)] at hcount
    rw [cbwsAux]
    rw [ite_eq_left (by omega)]
    exact ⟨_, rfl⟩
  | succ k ih =>
    intro i randomBytes selected hk hcache hcount
    rw [cbwsAux]
    split
    · exact ⟨_, rfl⟩
    · rename_i hlt
      have hcpos : 1 ≤ zeroChunkCount seed i := by omega
      have hi : i + 1 < UInt64.size := by
        rcases Nat.lt_or_ge (i + 1) UInt64.size with h | h
        · exact h
        · rw [zeroChunkCount_of_le seed i (by omega)] at hcpos
          omega
      have hrb : (if (i % 16 * 2 == 0) = true then sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16)))
          else randomBytes) = sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16))) := by
        by_cases h0 : i % 16 = 0
        · simp [h0]
        · rw [hcache h0]
          split <;> rfl
      have hrec := zeroChunkCount_succ seed i (by omega)
      have hsucc : (EthCLLib.Spec.checkedSucc i "compute_balance_weighted_selection: i += 1 past 2**64 - 1" :
          Except StateTransitionError { j : Nat // j = i + 1 ∧ j < UInt64.size }) =
          pure ⟨i + 1, rfl, hi⟩ := dite_eq_left hi
      dsimp only
      rw [hrb, hsucc]
      refine ih (i + 1) _ _ (by omega) (fun h => by rw [show (i + 1) / 16 = i / 16 by omega]) ?_
      unfold selectionChunk at hrec
      by_cases hz : le2 (sha (seed ++ uint64ToBytes (UInt64.ofNat (i / 16)))) (i % 16 * 2) = 0
      · -- A zero chunk sets the threshold to zero, so the pass accepts its candidate.
        rw [hz, Nat.mul_zero, ite_eq_left (Nat.zero_le _), Array.size_push]
        rw [ite_eq_left hz] at hrec
        omega
      · rw [ite_eq_right hz] at hrec
        -- Either way the pass keeps or grows the selection; the count does not drop.
        repeat' split
        all_goals (try simp only [Array.size_push])
        all_goals omega

theorem computeBalanceWeightedSelection_ok [Preset] [HasherTag] (st : BeaconState)
    (indices : Array ValidatorIndex) (seed : ByteArray) (size : Nat) (shuffle : Bool)
    (hz : ZeroChunksOften size) (hne : 0 < indices.size) :
    ∃ r, computeBalanceWeightedSelection (pureState st) indices seed size shuffle = .ok r := by
  unfold computeBalanceWeightedSelection
  dsimp only
  rw [ite_eq_left hne]
  exact cbwsAux_ok _ _ _ seed _ size shuffle _ 0 _ _ rfl (fun h => absurd rfl h)
    (by have := hz seed; simp only [Array.size_empty, Nat.sub_zero]; exact this)

theorem computeProposerIndices_ok [Preset] [HasherTag] (st : BeaconState) (epoch : Epoch)
    (seed : Bytes32) (indices : Array ValidatorIndex) (hz : ZeroChunksOften 1)
    (hne : 0 < indices.size) :
    ∃ r, computeProposerIndices (pureState st) epoch seed indices = .ok r := by
  unfold computeProposerIndices
  -- Every slot's draw succeeds, so the `mapM` over the epoch's slots does.
  refine Exists.imp (fun _ h => h.1)
    (EthCLLib.Proofs.except_array_mapM_ok (P := fun _ => True) _ (fun i _ => ?_))
  obtain ⟨s, hs⟩ := computeBalanceWeightedSelection_ok st indices
    (sha (seed ++ uint64ToBytes (computeStartSlotAtEpoch epoch + UInt64.ofNat i))) 1 true hz hne
  refine ⟨s[0]!, ?_, trivial⟩
  dsimp only
  rw [hs]
  rfl

/-- The Gloas proposer lookahead samples the unslashed active validators; it succeeds when there
is one. -/
theorem getBeaconProposerIndices_ok [Preset] [HasherTag] (st : BeaconState) (epoch : Epoch)
    (hz : ZeroChunksOften 1)
    (hne : 0 < ((getActiveValidatorIndices (pureState st) epoch).filter
      (fun vi => !((pureState st).view.validators[vi.toNat]!).slashed)).size) :
    ∃ r, getBeaconProposerIndices (pureState st) epoch = .ok r :=
  computeProposerIndices_ok st epoch _ _ hz hne

theorem getNextSyncCommittee_ok [Preset] [HasherTag] [EthCLLib.Spec.CryptoBackend] (st : BeaconState)
    (hz : ZeroChunksOften Const.syncCommitteeSize)
    (hne : 0 < (getActiveValidatorIndices (pureState st) (currentEpochOf (pureState st) + 1)).size) :
    ∃ r, getNextSyncCommittee (pureState st) = .ok r := by
  unfold getNextSyncCommittee
  dsimp only
  obtain ⟨s, hs⟩ := computeBalanceWeightedSelection_ok st _
    (getSeed (pureState st) (currentEpochOf (pureState st) + 1) Const.domainSyncCommittee) _ true hz hne
  rw [hs]
  exact ⟨_, rfl⟩
