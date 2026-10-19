# EthCLSpecs: spec-vs-vector discrepancies

The directional discrepancy policy (`SPEC_AUTHORING_MODEL.md` §10,
`SPECS_ARCHITECTURE.md` §12.1): the upstream `consensus-spec-tests` vectors are
the operational reference, so a Lean-versus-vector divergence almost always means
the Lean is wrong and the fix goes in Lean. The spec markdown is the ultimate
authority, and "spec wins" bites only in the rare case a vector contradicts the
spec text (an upstream pyspec bug): then Lean follows the text, the vector fails,
and the divergence is **recorded here** rather than papered over by bending Lean
to a wrong vector.

Each entry carries the vector id, the spec-text citation, and the upstream issue
link, so the audit trail is one grep away. Resolved Lean-versus-vector divergences
stay logged here for the audit trail even when the fix landed in Lean.

Deliberate implementation divergences that no vector observes live in
`IMPLEMENTATION_NOTES.md`, catalogued per fork; the FOCIL set is under "Heze diff".

Pin: `v1.7.0-alpha.12` (all forks).

Spec-markdown line citations (`<file>.md:NN`) resolve under `specs/` in
`ethereum/consensus-specs` at the pinned version; every re-pin re-checks them
alongside the divergences they anchor.

## Fulu

_No open discrepancies._ Every collected in-scope minimal and mainnet vector passes
by root or rejects faithfully (`epoch_processing`, `operations` incl. standalone
`execution_payload`, `sanity/blocks`, `sanity/slots`, `finality`, `random`,
`rewards`, `fork_choice` incl. the PeerDAS data-availability `on_block` cases and
`get_proposer_head`), with zero `xfail`. The only Fulu vectors not run are the
deselected out-of-scope ones (`IMPLEMENTATION_NOTES.md`, "Scope and conformance"): the Fulu `fork` /
`transition` formats (the Electra→Fulu upgrade / boundary, needing an Electra parent
fork) and the `light_client` / `networking` / `merkle_proof` / `sync` runners.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `epoch_processing/registry_updates/pyspec_tests/invalid_large_withdrawable_epoch` | `electra/beacon-chain.md`, `initiate_validator_exit` | none (Lean-side gap) | Fixed in Lean |

The one resolved entry was a Lean-side gap: Lean's `UInt64`
wrapped where the pyspec raises a `ValueError` serializing the overflowed
`withdrawable_epoch`. Closed by asserting the `exit_epoch +
MIN_VALIDATOR_WITHDRAWABILITY_DELAY` bound in `initiateValidatorExit`, so the case
now rejects faithfully.

## Gloas

_No open discrepancies._ Gloas is fully ported (the EIP-7732 ePBS spine, that is the
state-transition pipeline, plus operations, fork choice, and the Fulu→Gloas
transition); every in-scope minimal and mainnet vector passes by root or rejects
faithfully, with no `xfail`. Gloas inherits the Fulu `registry_updates` substep (the
DSL re-elaborates the captured `forkdef` in the Gloas namespace), so the overflow fix
above propagated to Gloas with no Gloas-side change. Deliberate divergences are
catalogued in `IMPLEMENTATION_NOTES.md`, "Gloas diff" and "Fork choice".

## Heze

One open discrepancy. The Gloas→Heze `fork` vectors are in scope. On both presets the
`after_fork_deactivate_validators_from_gloas_to_heze` and
`after_fork_deactivate_validators_wo_block_from_gloas_to_heze` cases are genuine Gloas
pre-states, and `upgrade_to_heze` matches their post roots. `fork_base_state` is not a
Gloas state and is not the output of `upgrade_to_heze`. Lean follows the spec text.
The harness reports the two cases as `xfail`; a future pass fails the run so the row
gets removed. FOCIL's deliberate divergences from the spec text stay in
`IMPLEMENTATION_NOTES.md`, "Heze diff".

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `minimal/heze/fork/fork/pyspec_tests/fork_base_state` | `heze/fork.md:36`, `upgrade_to_heze` | none | Open. Lean follows the spec. |
| `mainnet/heze/fork/fork/pyspec_tests/fork_base_state` | `heze/fork.md:36`, `upgrade_to_heze` | none | Open. Lean follows the spec. |

The pre-state's fork current version is already Heze (`0x08000001` minimal,
`0x08000000` mainnet). On minimal the bid's first variable offset is 226, where a
Gloas bid's prefix is 224, so the bid is the 13-field Heze container. On both presets
the pre-state is two bytes larger than the sibling Gloas pre-states. The post-state's
`fork.current_version` is the bytes `e8 14 80 00`, which is not `HEZE_FORK_VERSION`.
A correct upgrade of a Gloas state grows by those two inclusion-list bytes; these
posts grow by 516 bytes (minimal) and 2052 bytes (mainnet).
