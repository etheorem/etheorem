import EthCLSpecs.Proofs.Heze.ShouldExtendPayload

/-!
# `EthCLSpecs.Proofs.Heze`: the Heze fork's theorems (index)

Every theorem about an `EthCLSpecs.Heze` declaration, one module per subject.
The directory mirrors `EthCLSpecs/Heze/`, for the reason `Proofs/Gloas.lean`
states: a fork elaborates its own constant for every declaration, inherited ones
included, so a theorem here is about the Heze constant and about no other fork's.
`shouldExtendPayload` is the case that shows it. Gloas declares it and Heze
overrides it with the FOCIL gate, so the Gloas theorems say nothing about the
Heze constant.

Every declaration here sits in the `EthCLSpecs.Proofs.Heze` namespace.

Re-exports:

* `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's verified,
  recorded-unsatisfied FOCIL rejection theorem
  (`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied`), proved with
  `ForkChoiceStoreRun`.
-/
