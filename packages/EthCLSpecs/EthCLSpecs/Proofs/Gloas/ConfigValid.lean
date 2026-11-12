import EthCLSpecs.Gloas.Constants
import EthCLSpecs.Proofs.Fulu.ConfigValid

/-!
# `EthCLSpecs.Proofs.Gloas.ConfigValid`: the Gloas presets and configs the proofs accept

The Gloas counterpart of `Proofs/Fulu/ConfigValid.lean`. A Gloas preset carries every Fulu
field, so each Gloas class extends the Fulu one at the downgraded preset: `toFulu` holds the
Fulu rules, read through the `Gloas.Preset → Fulu.Preset` bridge that
`open scoped EthCLSpecs.Gloas.Downgrade` supplies (`SPECS_ARCHITECTURE.md` §6.2). The Gloas
`upgrade` case then reuses the Fulu lemmas, and a Gloas `Const.x` agrees with its Fulu twin
under the bridge by `rfl`.

The Gloas fields:

* phase0 `test_time`, post-Gloas branch: `ATTESTATION_DUE_BPS_GLOAS <= BASIS_POINTS`.
* Addition: the two Gloas churn quotients are positive. EIP-8061 divides the active balance
  by `CHURN_LIMIT_QUOTIENT_GLOAS` for the exit churn, and EIP-7732 by
  `CONSOLIDATION_CHURN_LIMIT_QUOTIENT` for the consolidation churn. A zero divisor makes pyspec
  raise and the model return a zero churn.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLSpecs.Gloas (Preset Config minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Gloas.Const
open scoped EthCLSpecs.Gloas.Downgrade

/-- The Gloas presets the proofs accept: the Fulu rules at the downgraded preset. -/
class PresetValid [Preset] : Prop extends toFulu : EthCLSpecs.Proofs.Fulu.PresetValid

/-- The Gloas configs the proofs accept, at a preset: the Fulu rules and the Gloas fields. -/
class ConfigValid [Preset] [Config] : Prop extends toFulu : EthCLSpecs.Proofs.Fulu.ConfigValid where
  /-- phase0 `test_time`, post-Gloas branch: `ATTESTATION_DUE_BPS_GLOAS <= BASIS_POINTS`. -/
  attestationDueBpsGloasLe : attestationDueBpsGloas ≤ basisPoints
  /-- Addition: the EIP-8061 exit-churn quotient is a divisor. -/
  churnLimitQuotientGloasPos : 1 ≤ churnLimitQuotientGloas.toNat
  /-- Addition: the EIP-7732 consolidation-churn quotient is a divisor. -/
  consolidationChurnLimitQuotientPos : 1 ≤ consolidationChurnLimitQuotient.toNat

-- `apply` fills `toFulu` by instance search: the Fulu instance at the downgraded preset
-- applies once the bridge reduces to the Fulu preset with the same values.
instance presetValidMinimal : @PresetValid minimal := by
  apply @PresetValid.mk minimal

instance presetValidMainnet : @PresetValid mainnet := by
  apply @PresetValid.mk mainnet

instance configValidMinimal : @ConfigValid minimal minimalConfig := by
  apply @ConfigValid.mk minimal minimalConfig <;> decide

instance configValidMainnet : @ConfigValid mainnet mainnetConfig := by
  apply @ConfigValid.mk mainnet mainnetConfig <;> decide

end EthCLSpecs.Proofs.Gloas
