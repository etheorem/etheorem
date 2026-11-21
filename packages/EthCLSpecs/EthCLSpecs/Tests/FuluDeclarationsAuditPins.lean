import EthCLSpecs.Fulu
import EthCLSpecs.Heze

/-!
# `EthCLSpecs.Tests.FuluDeclarationsAuditPins`: the preset-view range pins

Behavior pins for seven checked preset views in `Fulu/Constants.lean`. A view built as
`CLUint64.trustedOfUInt64 (UInt64.ofNat n)` is an unjustified raw construction.
`UInt64.ofNat` wraps a value past `2 ^ 64 - 1` before the wrapper sees it
(`SPEC_ARITHMETIC.md` §4.5). The pinned module types each of the seven `Epoch` or `Uint64`
(`EPOCHS_PER_SLASHINGS_VECTOR`, `EPOCHS_PER_ETH1_VOTING_PERIOD`,
`EPOCHS_PER_SYNC_COMMITTEE_PERIOD`, `MAX_COMMITTEES_PER_SLOT`, `TARGET_COMMITTEE_SIZE`,
`MAX_WITHDRAWALS_PER_PAYLOAD`, `MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP`), so a value of
`2 ^ 64` raises when the module loads. The raw view reads such a preset as `0`, and
`TARGET_COMMITTEE_SIZE = 2 ^ 64` then divides by zero inside `get_committee_count_per_slot`.

Each view is `CLUint64.ofNatLT` over a preset premise `…Lt : … < 2 ^ 64`, so that preset
cannot be built.

1. The premise boundary: `2 ^ 64 - 1` is admitted, `2 ^ 64` is not, and the pre-change
   route wrapped `2 ^ 64` to `0`.
2. A child preset at `2 ^ 64 - 1` builds, and its view reads the value with no wrap.
3. Every view equals its structural `Nat` field at both presets, in Fulu and through the
   Gloas and Heze replays, so the shipped presets keep their values.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Tests.FuluDeclarationsAuditPins

/-! ## 1. The premise boundary -/

/-- The last value a `Uint64` preset entry can hold satisfies the premise. -/
example : 18446744073709551615 < 2 ^ 64 := by decide

/-- The first value the pinned module rejects at load: no preset can carry it. -/
example : ¬ (18446744073709551616 < 2 ^ 64) := by decide

/-- The pre-change route: `UInt64.ofNat` wraps `2 ^ 64` to `0` before `trustedOfUInt64`
sees it, so the old view of `TARGET_COMMITTEE_SIZE = 2 ^ 64` was a zero divisor. -/
example : (CLUint64.trustedOfUInt64 (UInt64.ofNat 18446744073709551616)).toPlainNat = 0 := by
  decide

/-- The checked conversion of the same value raises the typed range fault, the answer the
pinned `Uint64(2**64)` gives. -/
example : (CLUint64.ofNat? 18446744073709551616).toOption = none := by decide

/-! ## 2. The boundary child preset -/

/-- The Fulu minimal preset with `TARGET_COMMITTEE_SIZE` and `MAX_WITHDRAWALS_PER_PAYLOAD` at
`2 ^ 64 - 1`, each premise re-proved. -/
@[reducible] private def boundary : EthCLSpecs.Fulu.Preset :=
  { EthCLSpecs.Fulu.minimal with
    targetCommitteeSize := 18446744073709551615, targetCommitteeSizeLt := by decide,
    maxWithdrawalsPerPayload := 18446744073709551615, maxWithdrawalsPerPayloadLt := by decide }

example : (@EthCLSpecs.Fulu.Const.targetCommitteeSizeC boundary).toPlainNat
    = 18446744073709551615 := by decide
example : (@EthCLSpecs.Fulu.Const.maxWithdrawalsPerPayloadC boundary).toPlainNat
    = 18446744073709551615 := by decide

/-! ## 3. The shipped presets keep their values -/

section Fulu
open EthCLSpecs.Fulu

/-- Each checked view against its structural field at preset `P`. -/
private def fuluViewsMatch (P : Preset) : Bool :=
  (@Const.epochsPerSlashingsVectorC P).toPlainNat == @Const.epochsPerSlashingsVector P &&
  (@Const.epochsPerEth1VotingPeriodC P).toPlainNat == @Const.epochsPerEth1VotingPeriod P &&
  (@Const.epochsPerSyncCommitteePeriodC P).toPlainNat == @Const.epochsPerSyncCommitteePeriod P &&
  (@Const.maxCommitteesPerSlotC P).toPlainNat == @Const.maxCommitteesPerSlot P &&
  (@Const.targetCommitteeSizeC P).toPlainNat == @Const.targetCommitteeSize P &&
  (@Const.maxWithdrawalsPerPayloadC P).toPlainNat == @Const.maxWithdrawalsPerPayload P &&
  (@Const.maxPendingPartialsPerWithdrawalsSweepC P).toPlainNat
    == @Const.maxPendingPartialsPerWithdrawalsSweep P

example : fuluViewsMatch minimal = true := by decide
example : fuluViewsMatch mainnet = true := by decide

/-- The minimal values, read through the views: `64`, `4`, `8`, `4`, `4`, `4`, `2`. -/
example : [(@Const.epochsPerSlashingsVectorC minimal).toPlainNat,
    (@Const.epochsPerEth1VotingPeriodC minimal).toPlainNat,
    (@Const.epochsPerSyncCommitteePeriodC minimal).toPlainNat,
    (@Const.maxCommitteesPerSlotC minimal).toPlainNat,
    (@Const.targetCommitteeSizeC minimal).toPlainNat,
    (@Const.maxWithdrawalsPerPayloadC minimal).toPlainNat,
    (@Const.maxPendingPartialsPerWithdrawalsSweepC minimal).toPlainNat]
    = [64, 4, 8, 4, 4, 4, 2] := by decide

end Fulu

section Gloas
open EthCLSpecs.Gloas

/-- The Gloas replay reads Gloas's own preset, which merges the Fulu premises. -/
private def gloasViewsMatch (P : Preset) : Bool :=
  (@Const.epochsPerSlashingsVectorC P).toPlainNat == @Const.epochsPerSlashingsVector P &&
  (@Const.maxCommitteesPerSlotC P).toPlainNat == @Const.maxCommitteesPerSlot P &&
  (@Const.targetCommitteeSizeC P).toPlainNat == @Const.targetCommitteeSize P &&
  (@Const.maxWithdrawalsPerPayloadC P).toPlainNat == @Const.maxWithdrawalsPerPayload P

example : gloasViewsMatch minimal = true := by decide
example : gloasViewsMatch mainnet = true := by decide

end Gloas

section Heze
open EthCLSpecs.Heze

/-- The Heze replay, one fork further down the lineage. -/
private def hezeViewsMatch (P : Preset) : Bool :=
  (@Const.epochsPerSyncCommitteePeriodC P).toPlainNat == @Const.epochsPerSyncCommitteePeriod P &&
  (@Const.maxCommitteesPerSlotC P).toPlainNat == @Const.maxCommitteesPerSlot P &&
  (@Const.maxPendingPartialsPerWithdrawalsSweepC P).toPlainNat
    == @Const.maxPendingPartialsPerWithdrawalsSweep P

example : hezeViewsMatch minimal = true := by decide
example : hezeViewsMatch mainnet = true := by decide

end Heze

end EthCLSpecs.Tests.FuluDeclarationsAuditPins
