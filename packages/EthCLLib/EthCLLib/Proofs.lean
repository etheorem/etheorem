import EthCLLib.Proofs.Arith
import EthCLLib.Proofs.BoxSimp
import EthCLLib.Proofs.IndicesWhere
import EthCLLib.Proofs.KeepsUncached
import EthCLLib.Proofs.LawfulFcMap
import EthCLLib.Proofs.MerkleBranch
import EthCLLib.Proofs.Preserves
import EthCLLib.Proofs.Run
import EthCLLib.Proofs.RunEnsures
import EthCLLib.Proofs.RunSucceeds
import EthCLLib.Proofs.StoreRun
import EthCLLib.Proofs.ZeroChunks

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

* `EthCLLib.Proofs.Arith`: what `saturatingSub` computes (`saturatingSub_toNat`,
  `saturatingSub_le`).
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
* `EthCLLib.Proofs.IndicesWhere`: what the registry filter `indicesWhere` returns: indices in
  range that satisfy the predicate (`mem_indicesWhere`), and at least one when some element does
  (`indicesWhere_size_pos`).
* `EthCLLib.Proofs.BoxSimp`: the `box_reduce` simp set, for reading a field of a state a
  record update on the uncached box left.
* `EthCLLib.Proofs.Preserves`: `Preserves`, the invariant every successful run keeps, and
  `ReadsOnly`; leaves for the spec helpers (`getThe`, the checked operators,
  `throwListFull`, `sszOfArrayM`); loop rules for `fuelLoop`, `forIn'`, pure `Id` loops, and
  loops that carry a box; and the `append_split` tactic for `appendState`'s `match`.
* `EthCLLib.Proofs.RunEnsures`: `RunEnsures`, the per-start triple that says what a
  successful run guarantees, with weakest-precondition closure lemmas, loop rules
  that take an invariant (`runEnsures_forIn_range` also sees the index), the
  relational reading `KeepsUncachedWith`, and the `run_ensures` tactic.
* `EthCLLib.Proofs.RunSucceeds`: `RunSucceeds`, the total-correctness triple: the run
  succeeds and its result satisfies the postcondition. The same rule set as `RunEnsures`,
  with each check's premise made explicit; `RunSucceeds.and_ensures` to join a
  partial-correctness fact; and the `run_succeeds` tactic.
* `EthCLLib.Proofs.ZeroChunks`: `ZeroChunksOften`, the hash premise under which
  balance-weighted selection fills before its `uint64` pass counter overflows.
-/
