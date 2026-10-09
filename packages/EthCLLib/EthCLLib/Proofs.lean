import EthCLLib.Proofs.KeepsUncached
import EthCLLib.Proofs.LawfulFcMap
import EthCLLib.Proofs.MerkleBranch
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.StoreRun

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

* `EthCLLib.Proofs.LawfulFcMap`: same-key insertion for `FcMap`
  (`LawfulFcMap`, `FcMap.lookup_insert_self`,
  `FcMap.contains_insert_self`), with `instLawfulFcMapTreeMap` and
  `instLawfulFcMapHashMap`.
* `EthCLLib.Proofs.MerkleBranch`: what `isValidMerkleBranch` accepts.
* `EthCLLib.Proofs.Run`: the `StateT`-over-`Except` run facts every pure runner
  shares (`run_bind`, `run_pure`, `run_throw`, `except_bind_ok`,
  `except_bind_error`, the `ofExcept` and `liftErr` run equations), plus the pure
  box helpers `pureState` and `runPure` and their lemmas.
* `EthCLLib.Proofs.StoreRun`: `ForkChoiceStoreRun`, the pure store-machine runner
  every fork's fork-choice proofs pin at that fork's `Store`, and the
  store-specific `throwArithmetic_run` equation.
* `EthCLLib.Proofs.KeepsUncached`: the box-flavour predicates (`KeepsUncached`,
  `KeepsUncachedFrom`, `ReturnsUncached`, `RunPassesP`), their closure and loop
  lemmas, the indexed-read run equations, and the conditional bind law
  `runPure_bind_of_keepsUncached`.
-/
