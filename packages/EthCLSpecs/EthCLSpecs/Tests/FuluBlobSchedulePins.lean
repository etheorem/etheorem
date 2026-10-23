import EthCLSpecs.Fulu.Time

/-!
# `EthCLSpecs.Tests.FuluBlobSchedulePins`: `get_blob_parameters` at both shipped configs

Each pin states the `(epoch, max_blobs_per_block)` pair the pinned pyspec
(`v1.7.0-alpha.11`) returns at the same epoch. The probe script that produced the pyspec side
is `.tmp/batchfaith/probe_b2.py` (local, not committed). The mainnet schedule has entries at
epochs 412672 (15 blobs) and 419072 (21 blobs). The minimal schedule is empty, so every epoch
gets the Electra fallback, `(2 ^ 64 - 1, 9)`.

`getBlobParameters` reads no state and hashes nothing, so the pins close by kernel `decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.FuluBlobSchedulePins

open EthCLSpecs.Fulu

/-- The epochs each pin probes: zero, both sides of each schedule entry, and `2 ^ 64 - 1`. -/
private def epochs : List Epoch := [0, 412671, 412672, 419071, 419072, 18446744073709551615]

/-- `getBlobParameters` at every probe epoch, as `(epoch, max_blobs_per_block)` pairs. -/
private def params [Preset] [Config] : List (Nat × Nat) :=
  epochs.map fun e =>
    let p := getBlobParameters e
    (p.epoch.toNat, p.maxBlobsPerBlock.toNat)

-- Mainnet: the Electra fallback below 412672, then 15, then 21.
example : (letI : Preset := mainnet; letI : Config := mainnetConfig; params) =
    [(364032, 9), (364032, 9), (412672, 15), (412672, 15), (419072, 21), (419072, 21)] := by
  decide

-- Minimal: the empty schedule gives the Electra fallback at every epoch.
example : (letI : Preset := minimal; letI : Config := minimalConfig; params) =
    List.replicate 6 (18446744073709551615, 9) := by
  decide

end EthCLSpecs.Tests.FuluBlobSchedulePins
