import EthCLLib.Proofs.ArrayUnion
import EthCLLib.Proofs.Checked
import EthCLLib.Proofs.EngineLaws
import EthCLLib.Proofs.Frame
import EthCLLib.Proofs.KeepsUncached
import EthCLLib.Proofs.KeepsUncachedMemLoop
import EthCLLib.Proofs.LawfulFcMap
import EthCLLib.Proofs.MerkleBranch
import EthCLLib.Proofs.OfFnM
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StateFree
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.SwapOrNot

/-!
# `EthCLLib.Proofs`: framework proof modules

The theorems about the spec functions `EthCLLib.Spec` declares, plus the
generic proof toolkit the fork proofs build on: the runners' `StateT`-over-
`Except` run facts, the pure box helpers `pureState` and `runPure`, and the
flavour preservation behind the conditional `runPure` bind law. A fork body's
theorems live in `EthCLSpecs/Proofs/<Fork>/` instead, one directory per fork,
because each fork re-elaborates its own declarations.

Nothing here carries `@[characterizes]`. That attribute claims a `forkdef`'s
contract, and the framework declares no `forkdef`, so `scripts/ProofCoverage.lean`
counts none of these modules; it audits their axioms through this same root.

Re-exports:

* `EthCLLib.Proofs.ArrayUnion`: an element is in `arrayUnion xs ys` exactly when it is
  in `xs` or in `ys` (`mem_arrayUnion`).
* `EthCLLib.Proofs.Checked`: when `checkedMul` raises. `mulGuard_iff` reads its guard on
  `Nat`, and `checkedMul_of_lt` / `checkedMul_of_ge` give the two outcomes from a `Nat` bound.
* `EthCLLib.Proofs.EngineLaws`: the EIP-7805 inclusion rule as an assumption on an
  `ExecutionEngine` (`LawfulInclusionList`).
* `EthCLLib.Proofs.Frame`: the frame rules (`KeepsAt`, `Resets`, `Returns`) that
  prove a store run leaves one field alone, one bind at a time.
* `EthCLLib.Proofs.LawfulFcMap`: the laws of an `FcMap`
  (`LawfulFcMap`, `FcMap.lookup_insert_self`,
  `FcMap.contains_insert_self`, `FcMap.mem_values`), with `instLawfulFcMapTreeMap`.
  The order laws of `instOrdVectorUInt8` that the
  `treeMap` instance needs at `Root` sit in `EthCLLib.Spec.FiniteMap`.
* `EthCLLib.Proofs.MerkleBranch`: what `isValidMerkleBranch` accepts.
* `EthCLLib.Proofs.OfFnM`: `ofFnM_eq_ok_ofFn`, which collapses an
  all-succeeding `Vector.ofFnM` in `Except` to the pure `Vector.ofFn`.
* `EthCLLib.Proofs.Run`: the `StateT`-over-`Except` run facts every pure runner
  shares (`run_bind`, `run_pure`, `run_throw`, `except_bind_ok`,
  `except_bind_error`, the `ofExcept` and `liftErr` run equations), plus the pure
  box helpers `pureState` and `runPure` and their lemmas.
* `EthCLLib.Proofs.StateFree`: the rules for a run that reads no runner state, and the
  tactic `free_solve` that applies them to a fork-choice query.
* `EthCLLib.Proofs.StoreRun`: `ForkChoiceStoreRun`, the pure store-machine runner
  every fork's fork-choice proofs pin at that fork's `Store`, the
  store-specific `throwArithmetic_run` equation, and `toNat_add_of_not_lt` for a
  `checkedAdd` that does not raise.
* `EthCLLib.Proofs.KeepsUncached`: the box-flavour predicates (`KeepsUncached`,
  `KeepsUncachedFrom`, `ReturnsUncached`, `RunPassesP`), their closure and loop
  lemmas, the indexed-read run equations, and the conditional bind law
  `runPure_bind_of_keepsUncached`.
* `EthCLLib.Proofs.KeepsUncachedMemLoop`: the `forIn'` loop lemmas for a
  `for h : i in xs` loop, whose body reads the membership proof `h`.
* `EthCLLib.Proofs.SwapOrNot`: the swap-or-not shuffle is a permutation. The fork
  bridges in `EthCLSpecs/Proofs/<Fork>/Shuffle.lean` use its theorems.
-/
