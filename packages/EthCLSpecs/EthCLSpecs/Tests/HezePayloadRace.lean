import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Heze.PayloadRaceBounds

/-!
# `EthCLSpecs.Tests.HezePayloadRace`: the tie rule and the 70 % bound on small races

One committee of balance 100 votes in slot `lo = 1`. The honest part votes `empty`, the
adversarial part votes `full`, and the adversary adds a boost of 40. At 71 honest, EMPTY
wins. At 70 honest, the two sides tie, and the tie goes to FULL. The two `#guard` lines pin
both cases on `EmptyAhead`. The `example` lines take the same numbers through
`seventy_percent` and `count_of_fraction`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.HezePayloadRace

open EthCLSpecs.Proofs.Heze.PayloadRace

/-- A validator that votes in slot 1 only. -/
def oneVote (index balance : Nat) (honest : Bool) : Validator :=
  ⟨index, balance, honest, fun t => t == 1⟩

/-- One committee: `honestBalance` honest, the rest of 100 adversarial. -/
def committee (honestBalance : Nat) : List Validator :=
  [oneVote 0 honestBalance true, oneVote 1 (100 - honestBalance) false]

/-- The honest validator on `empty`, the adversarial one on `full`. -/
def splitView : Validator → Side := fun v => if v.honest then .empty else .full

#guard decide (EmptyAhead (committee 71) splitView 40)

#guard !decide (EmptyAhead (committee 70) splitView 40)

/-- At 71 of 100 the uniform condition holds, through `seventy_percent` with `u = 1`. -/
example : 100 * 1 + 40 * 1 < 2 * 71 := (seventy_percent 1 71).mpr (by decide)

/-- At 70 of 100 the uniform condition fails, as the tie rule requires. -/
example : ¬ (100 * 1 + 40 * 1 < 2 * 70) := fun h =>
  absurd ((seventy_percent 1 70).mp h) (by decide)

/-- The boost of 40 in these pins and in `seventy_percent` is the Heze constant
`PROPOSER_SCORE_BOOST`, at both configs. -/
private def pinBoost (preset : EthCLSpecs.Heze.Preset) (config : EthCLSpecs.Heze.Config) :
    Nat :=
  letI := preset
  letI := config
  EthCLSpecs.Heze.Const.proposerScoreBoost

#guard pinBoost EthCLSpecs.Heze.minimal EthCLSpecs.Heze.minimalConfig = 40
#guard pinBoost EthCLSpecs.Heze.mainnet EthCLSpecs.Heze.mainnetConfig = 40

/-- `count_of_fraction` at 71 of 100: one committee gives the counting inequality. -/
example : 1 * (100 - 71) + 40 < 1 * 71 :=
  count_of_fraction 1 71 100 40 (by decide) (by decide) (by decide)

end EthCLSpecs.Tests.HezePayloadRace
