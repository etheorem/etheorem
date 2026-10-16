import EthCLSpecs.Proofs.Fulu.Balances
import EthCLSpecs.Proofs.Fulu.DepositIndex
import EthCLSpecs.Proofs.Fulu.Run

/-!
# `EthCLSpecs.Proofs.Fulu`: the Fulu fork's theorems (index)

Every theorem about an `EthCLSpecs.Fulu` declaration, one module per subject. The directory
mirrors `EthCLSpecs/Fulu/`. A fork elaborates its own constant for every declaration, inherited
ones included. A theorem here is about the Fulu constant. `increaseBalance` is the case that
shows it. Gloas and Heze inherit it, and each inheritance is a separate constant these theorems
leave untouched.

Every declaration here sits in the `EthCLSpecs.Proofs.Fulu` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Fulu.Run`: `FuluRun`, the state-transition monad every Fulu proof in this
  directory pins its theorems to.
* `EthCLSpecs.Proofs.Fulu.Balances`: `increaseBalance` and `decreaseBalance`, each with an exact
  run equation and an out-of-range reject, plus `increaseBalance`'s overflow reject and its
  exact stored sum, and `decreaseBalance`'s truncating difference.
* `EthCLSpecs.Proofs.Fulu.DepositIndex`: `processDeposit` up to `applyDeposit`. The index
  increment faults only at `2 ^ 64 - 1`, and never under the `processOperations` guard.
-/
