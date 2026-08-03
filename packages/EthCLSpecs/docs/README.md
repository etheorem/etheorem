# EthCLSpecs, architecture documents

EthCLSpecs is a Lean 4 library for Ethereum consensus-spec types, SSZ, the
state-transition function, and fork choice, covering the Fulu, Gloas, and Heze forks.

Three documents define the design. Read them in order.

1. [SPEC_AUTHORING_MODEL.md](SPEC_AUTHORING_MODEL.md), the contract: what a spec
   author writes versus what the framework provides, the boundary table, and the
   canonical glossary. Start here.
2. [FRAMEWORK_ARCHITECTURE.md](FRAMEWORK_ARCHITECTURE.md), the framework and DSL that
   implement the contract.
3. [SPECS_ARCHITECTURE.md](SPECS_ARCHITECTURE.md), how the fork specs (Fulu, Gloas,
   Heze) are organized, ported, and tested.

The glossary in the first document is the single source of truth for shared
vocabulary; the other two quote it.

[PLAN.md](PLAN.md) sequences the implementation into phases over the `EthCLLib`,
`EthCLSpecs`, and `EthCLProofs` packages, and opens with the background an
implementor needs. During implementation, deviations and notable findings go in
`IMPLEMENTATION_NOTES.md` (created then), not into these four documents, which stay
the design of record.

[DISCREPANCIES.md](DISCREPANCIES.md) is the narrow spec-vs-vector ledger: it records
only cases where a released vector contradicts the spec text (upstream pyspec bugs)
and resolved vector-level gaps, keyed by vector id. Deliberate implementation
divergences that no vector observes belong in `IMPLEMENTATION_NOTES.md` instead,
catalogued per fork.

[FUTURE_WORK.md](FUTURE_WORK.md) records deferred changes: what is left, why it waits,
and the shape it will take, so a later pass picks each one up whole. The current entry is
the provability of the pure indexed reads: a proof parameter or a refined index-list type,
plus the invariant lemmas they rest on.

[CONSENSUS_PROOF_CANDIDATES.md](CONSENSUS_PROOF_CANDIDATES.md) is a shortlist of Lean
theorem candidates across the Fulu and Gloas specs, to help contributors pick proof targets.
