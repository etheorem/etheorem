import SizzLeanTests.ReprExamples
import SizzLeanTests.SetAtRandom
import SizzLeanTests.Sha256Equivalence
import SizzLeanTests.ExampleContainers
import SizzLeanTests.TreeBackedCoherence
import SizzLeanTests.TreeBackedSetField
import SizzLeanTests.MultiSetterIndex
import SizzLeanTests.PendingOverlayCoherence
import SizzLeanTests.PendingPrefixConflict
import SizzLeanTests.PendingListShrink
import SizzLeanTests.WidthsAndLists
import SizzLeanTests.PresetSymbolicCap
import SizzLeanTests.CollectionInstances
import SizzLeanTests.ElementSurface
import SizzLeanTests.IndexErrorPayload
import SizzLeanTests.InfallibleIndex
import SizzLeanTests.Modify
import SizzLeanTests.Sha256BatchEquivalence
-- `HashConsCoherence` gates the standalone hash-cons primitive; it
-- is kept on disk but not in the default test build because the
-- smart constructor is not wired into `Node.ofShape` / `setAt` /
-- `merkleRootWithCache`, so the user-facing `SSZ.FastBox` /
-- `TreeBacked` path doesn't exercise it.
import SizzLeanTests.SerializeCacheCoherence

/-!
# `SizzLeanTests`: SSZ-only empirical / property-test gates

Property-test gates that exercise the SSZ library *in isolation*,
no Eth consensus-spec types. Build with:

```
lake build SizzLeanTests
```

## What's here

* **SHA-256 FFI ≡ spec equivalence**: `Sha256Equivalence.lean`
  (scalar `hash` / `combine`) and `Sha256BatchEquivalence.lean`
  (batched combine). These are the cross-checks that need *both* the
  FFI binding (`LeanHazmatSha256`) and the pure-Lean spec
  (`LeanSha256`), so they live here rather than in either package's
  own test lib. They are the empirical evidence behind SizzLean's
  `sha256{Hash,Combine,BatchCombine}_eq_spec` axioms. The pure
  byte-level CAVP KAT of the FFI shim (the FFI ≡ NIST direction) lives
  in `LeanHazmatSha256Tests`.
* **Tree machinery**: `Node.setAt` and `Node.setManyAt` PRNG
  property tests (`SetAtRandom.lean`).
* **Cache machinery on example containers**: `TreeBacked`
  coherence (`hashTreeRootCached = SSZ.hashTreeRoot`),
  `sszUpdate` multi-field batched updates, vector-index `sszUpdate`.
  Containers used as test fixtures are defined locally in
  `ExampleContainers.lean`, small SSZ-shaped types analogous to
  `Fork` / `SignedBeaconBlockHeader` / `HistoricalBatch`
  but with no dependency on the consensus container surface.

Eth-driven conformance (real Fulu / Gloas containers,
`ssz_static` CLI dispatch) lives in `EthCLSpecs`. The
two libraries share the same property-test patterns but operate on
different container surfaces.

## Why split

The default `lake build` doesn't rebuild these files; on iterative
work the heavy `native_decide` batches don't recompile until you
ask. Keeping Eth-using tests in `EthCLSpecs`
keeps the SSZ-library gates fast and dependency-light.
-/
