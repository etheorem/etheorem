import EthCLSpecs.Fulu

/-!
# `EthCLSpecs.TheoremVectors.Manual.Fulu`: the Fulu manual terms

Author-written input terms (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, §4.2), `[Preset]`-generic
so one definition serves every preset a named line lists: the command
elaborates each `with` term inside the theorem's telescope, where the
theorem's own instances fill the term's instance binders. A term that
fails the check is a build error, because the author claimed it works.

Two manual states serve the balance-mutator theorems of
`Proofs/Fulu/Balances.lean`. Both are `default` with a one-element
balances list, so the state's remaining containers stay at their zero
forms and the runs evaluate cheap:

- `oneBalanceState` holds the balance `5`, which
  `decreaseBalance_run_no_underflow` reads in range and subtracts from.
- `maxBalanceState` holds the balance `2 ^ 64 - 1`, which paired with
  `delta := 1` pushes the sum to `2 ^ 64`, so `checkedAdd`'s carry test
  fires in `increaseBalance_run_overflow`.

The two out-of-range theorems take no manual state: `default`'s empty
balances list already makes their `¬ i < size` hypothesis true, and the
generator names `default` directly in the `with` clause.
-/

set_option autoImplicit false

open EthCLSpecs.Fulu (Preset)

namespace EthCLSpecs.TheoremVectors.Manual.Fulu

/-- A state whose balances list holds the single balance `5`: one in-range
entry for `decreaseBalance_run_no_underflow` to read and subtract from. -/
def oneBalanceState [Preset] : EthCLSpecs.Fulu.BeaconState :=
  let bs : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Gwei
      EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    ((default : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Gwei
        EthCLSpecs.Fulu.Const.validatorRegistryLimit).push 5)
  { (default : EthCLSpecs.Fulu.BeaconState) with balances := bs }

/-- A state whose single balance sits one below the `uint64` wrap: paired
with `delta := 1`, the sum reaches `2 ^ 64` and `checkedAdd`'s carry test
rejects, which is the run `increaseBalance_run_overflow` states. -/
def maxBalanceState [Preset] : EthCLSpecs.Fulu.BeaconState :=
  let bs : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Gwei
      EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    ((default : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Gwei
        EthCLSpecs.Fulu.Const.validatorRegistryLimit).push 18446744073709551615)
  { (default : EthCLSpecs.Fulu.BeaconState) with balances := bs }

end EthCLSpecs.TheoremVectors.Manual.Fulu
