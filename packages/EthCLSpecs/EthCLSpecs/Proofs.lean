import EthCLSpecs.Proofs.Gloas
import EthCLSpecs.Proofs.Heze
import EthCLSpecs.Proofs.OrdVector
import EthCLSpecs.Proofs.Run
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs`: consensus-spec theorems (index)

Mathlib-free proofs about `EthCLSpecs` declarations, colocated with the specs
the way `SizzLean.Proofs` is colocated with `SizzLean`: same package, same
build. Each theorem is closed by whichever tactic its goal needs, `bv_decide`,
`decide`, `native_decide`, or plain case analysis. Always over the spec's own
types, never mathlib. A theorem that turns out to need mathlib moves to the standalone
`EthCLProofs` package instead (`docs/SPECS_ARCHITECTURE.md` §11), following the
`LeanPoseidonProofs` containment pattern. Mathlib never reaches this library,
the framework, the runner, or the conformance path.

A theorem that states its subject's main contract carries
`@[characterizes <function>]` (`EthCLLib.Internal.ProofLedger`). The tag is a
claim, so the attribute rejects a target no `forkdef` declared and a target the
statement never mentions. `just proof-coverage` counts the tags, audits every
theorem's axioms, and its committed baseline fails the build when a claim
disappears. Supporting lemmas stay untagged and count as touched.

## One directory per fork

`Proofs/Gloas/` holds the Gloas theorems, and a later fork's theorems get their
own directory beside it. The rule is the one `docs/SPECS_ARCHITECTURE.md` §3.4
sets for the fork bodies, and it holds here for the reason inheritance gives:
a child fork re-elaborates a parent declaration into its own namespace, so
`EthCLSpecs.Fulu.f` and `EthCLSpecs.Gloas.f` are two constants, and a proof about
one claims nothing about the other. The coverage report counts the two apart for
the same reason, and it rejects a `@[characterizes]` tag written outside its
target fork's directory.

Re-exports:

* `EthCLSpecs.Proofs.Gloas`: the Gloas fork's theorems, one module per subject.
* `EthCLSpecs.Proofs.Heze`: the Heze fork's theorems, one module per subject.
* `EthCLSpecs.Proofs.OrdVector`: the byte-vector order on `Root` is reflexive
  (`compare_vectorUInt8_self`). Fork-choice proofs use it when two nodes have the
  same root.
* `EthCLSpecs.Proofs.Run`: `run_bind`, `run_pure`, `run_throw`, `except_bind_ok`,
  and `except_bind_error`, the `StateT`-over-`Except` facts every pure runner
  shares. Fork-neutral, so Gloas and Heze both import this module.
* `EthCLSpecs.Proofs.StoreRun`: `ForkChoiceStoreRun`, the pure store-machine
  runner every fork's fork-choice proofs pin at that fork's `Store`, and the
  store-specific `throwArithmetic_run` equation.
-/
