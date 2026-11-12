import EthCLLib.Spec.Arith
import EthCLLib.Spec.SigningRoot

/-!
# `EthCLLib.Proofs.ZeroChunks`: the hash premise behind balance-weighted selection

`compute_balance_weighted_selection` (Gloas `beacon-chain.md`, inherited by every fork this
repo models) draws candidates in passes `i = 0, 1, 2, …`. Pass `i` reads a two-byte random
value, chunk `i % 16` of `sha(seed ++ uint64_to_bytes(i // 16))`, and accepts the candidate
when `effective_balance * MAX_RANDOM_VALUE >= MAX_EFFECTIVE_BALANCE_ELECTRA * random_value`. The
pass counter is a `uint64`, so the loop faults when it reaches `2^64 - 1` before it has
selected `size` candidates.

Whether it fills in time depends on the hash. A zero chunk accepts every candidate, including
one with effective balance zero, so `k` zero chunks among the passes give `k` acceptances.
`ZeroChunksOften k` states that every seed has at least `k` zero chunks among the passes below
`2^64 - 1`.

For SHA-256 this is believed true: a chunk is zero with probability `2^-16`, so a seed
expects about `2^48` zero chunks, and `k` is at most a few hundred. It is out of reach of
proof. For a degenerate hasher it is false: a hasher that outputs constant `0xFF` bytes has no
zero chunk at all, and a registry with no validator at the maximum effective balance then
never fills. So the success theorems take `ZeroChunksOften` as a premise. It is never an
axiom, so `#axioms` never shows it.

The premise reads the hash alone. It names no fork and no state.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs

open EthCLLib.Spec (HasherTag sha le2 uint64ToBytes)

/-- The two-byte random value the selection reads at pass `j`: chunk `j % 16` of the hash of
`seed` and the block number `j / 16`. -/
def selectionChunk [HasherTag] (seed : ByteArray) (j : Nat) : Nat :=
  le2 (sha (seed ++ uint64ToBytes (UInt64.ofNat (j / 16)))) ((j % 16) * 2)

/-- The passes `j` with `i ≤ j < 2^64 - 1` whose chunk is zero. The list is never built; the
count is a specification. -/
def zeroChunkCount [HasherTag] (seed : ByteArray) (i : Nat) : Nat :=
  ((List.range' i (UInt64.size - 1 - i)).filter (fun j => selectionChunk seed j == 0)).length

/-- Every seed has at least `k` zero chunks among the passes below `2^64 - 1`. -/
def ZeroChunksOften [HasherTag] (k : Nat) : Prop :=
  ∀ seed : ByteArray, k ≤ zeroChunkCount seed 0

/-- One pass of the count: pass `i` counts when its chunk is zero, and the rest of the count
starts at `i + 1`. -/
theorem zeroChunkCount_succ [HasherTag] (seed : ByteArray) (i : Nat) (hi : i < UInt64.size - 1) :
    zeroChunkCount seed i =
      (if selectionChunk seed i = 0 then 1 else 0) + zeroChunkCount seed (i + 1) := by
  unfold zeroChunkCount
  have hlen : UInt64.size - 1 - i = (UInt64.size - 1 - (i + 1)) + 1 := by omega
  rw [hlen, List.range'_succ, List.filter_cons]
  by_cases h : selectionChunk seed i = 0
  · simp [h, Nat.add_comm]
  · simp [h]

/-- Past the last pass the count is zero. -/
theorem zeroChunkCount_of_le [HasherTag] (seed : ByteArray) (i : Nat) (hi : UInt64.size - 1 ≤ i) :
    zeroChunkCount seed i = 0 := by
  unfold zeroChunkCount
  rw [show UInt64.size - 1 - i = 0 by omega]
  rfl

/-- A premise for `k` zero chunks gives one for fewer. -/
theorem ZeroChunksOften.mono [HasherTag] {k k' : Nat} (h : ZeroChunksOften k) (hk : k' ≤ k) :
    ZeroChunksOften k' :=
  fun seed => Nat.le_trans hk (h seed)

end EthCLLib.Proofs
