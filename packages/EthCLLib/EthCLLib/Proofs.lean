import EthCLLib.Proofs.LawfulFcMap
import EthCLLib.Proofs.MerkleBranch

/-!
# `EthCLLib.Proofs`: framework proof modules

The theorems about the spec functions `EthCLLib.Spec` declares. A fork body's
theorems live in `EthCLSpecs/Proofs/<Fork>/` instead, one directory per fork,
because each fork re-elaborates its own declarations.

Nothing here carries `@[characterizes]`. That attribute claims a `forkdef`'s
contract, and the framework declares no `forkdef`, so `scripts/ProofCoverage.lean`
counts none of these modules.

Re-exports:

* `EthCLLib.Proofs.LawfulFcMap`: the laws of an `FcMap`
  (`LawfulFcMap`, `FcMap.lookup_insert_self`,
  `FcMap.contains_insert_self`, `FcMap.mem_values`), with `instLawfulFcMapTreeMap`
  and `instLawfulFcMapHashMap`. The order laws of `instOrdVectorUInt8` that the
  `treeMap` instance needs at `Root` sit in `EthCLLib.Spec.FiniteMap`.
* `EthCLLib.Proofs.MerkleBranch`: what `isValidMerkleBranch` accepts.
-/
