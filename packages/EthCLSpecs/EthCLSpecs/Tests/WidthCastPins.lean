import EthCLSpecs.Fulu
import EthCLSpecs.Heze

/-!
# `EthCLSpecs.Tests.WidthCastPins`: the shuffle's width-8 round byte

Behavior pins for the Stage 8.2 width sweep. The in-scope pyspec text casts to a width
other than 64 bits in one body: `compute_shuffled_permutation` feeds
`uint_to_bytes(Uint8(current_round))` and `uint_to_bytes(Uint32(position_bucket))` into
its hash (`fulu/minimal.py:1252-1273`). Every other `Uint8` / `Uint32` / `Uint256` site
in scope is byte data or a codec value (`mb/spec-arithmetic-implementation/stage-8.2.md`).

The `Uint8` cast raises once a preset sets more than `2^8` rounds. At the pin,
`SHUFFLE_ROUND_COUNT = Uint64(257)` raises
`SSZValueError: 256 is out of range for Uint8 [0, 255]` in round 256. The pre-change body
computed `UInt8.ofNat round`, which wraps 256 to the byte `0` and returned a permutation.
The preset premise `shuffleRoundCountLe : shuffleRoundCount ≤ 2 ^ 8` now rules that
preset out, so the round byte is the proof-carrying `CLUint8.ofNatLT`.

1. The premise: both standard presets satisfy it, the 256-round boundary child satisfies
   it, and a 257-round preset cannot satisfy it.
2. Permutation values from the pinned pyspec, seed `bytes(range(32))`, `index_count = 7`:
   the minimal preset (10 rounds), and children at 255 and 256 rounds. Round 255 hashes
   the round byte `0xff`, the last value the cast admits.
3. The inherited body replays at Heze with the same values.

`computeShuffledPermutation` hashes through the FFI `Sha256` seam, so the value pins use
`native_decide` (CLAUDE.md, "Proofs involving SSZ hashes", case 2).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Tests.WidthCastPins

/-! ## 1. The preset premise -/

example : @EthCLSpecs.Fulu.Const.shuffleRoundCount EthCLSpecs.Fulu.minimal = 10 := rfl
example : @EthCLSpecs.Fulu.Const.shuffleRoundCount EthCLSpecs.Fulu.mainnet = 90 := rfl

/-- The first round count the pinned `Uint8(current_round)` cast rejects: no preset can
carry it. -/
example : ¬ (257 ≤ 2 ^ 8) := by decide

/-- The checked narrowing the premise replaces: `Uint8(256)` raises the typed range fault,
where the pre-change `UInt8.ofNat 256` wrapped to `0`. -/
example : CLUint8.ofNat? 256 = .error (.range "Uint8()" 8 256 0) := by decide
example : UInt8.ofNat 256 = 0 := by decide

/-- The last admitted round byte, `0xff`, through the proof-carrying route. -/
example : (CLUint8.ofNatLT 255 (by decide)).val = 255 := by decide

/-! ## 2. Permutation values (pinned pyspec) -/

/-- The seed `bytes(range(32))`. -/
private def seed : ByteArray := ⟨(Array.range 32).map UInt8.ofNat⟩

/-- The minimal preset with `rounds` shuffle rounds, the boundary premise re-proved. -/
@[reducible] private def minimalRounds (rounds : Nat) (h : rounds ≤ 2 ^ 8) : EthCLSpecs.Fulu.Preset :=
  { EthCLSpecs.Fulu.minimal with shuffleRoundCount := rounds, shuffleRoundCountLe := h }

private def fuluPerm (p : EthCLSpecs.Fulu.Preset) : Array Nat :=
  letI := p
  letI := fastHasherTag
  EthCLSpecs.Fulu.computeShuffledPermutation 7 seed

/-- Minimal, 10 rounds: `[0, 2, 4, 5, 6, 3, 1]`. -/
example : fuluPerm EthCLSpecs.Fulu.minimal = #[0, 2, 4, 5, 6, 3, 1] := by native_decide

/-- 255 rounds, the last round byte `0xfe`: `[0, 2, 4, 6, 3, 1, 5]`. -/
example : fuluPerm (minimalRounds 255 (by decide)) = #[0, 2, 4, 6, 3, 1, 5] := by
  native_decide

/-- 256 rounds, the boundary: round 255 hashes the byte `0xff`. `[5, 3, 4, 6, 2, 1, 0]`. -/
example : fuluPerm (minimalRounds 256 (by decide)) = #[5, 3, 4, 6, 2, 1, 0] := by
  native_decide

/-! ## 3. The Heze replay -/

/-- The inherited body reads Heze's own `Const.shuffleRoundCountLe`. -/
example :
    (letI := EthCLSpecs.Heze.minimal
     letI := fastHasherTag
     EthCLSpecs.Heze.computeShuffledPermutation 7 seed) = #[0, 2, 4, 5, 6, 3, 1] := by
  native_decide

end EthCLSpecs.Tests.WidthCastPins
