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

Pin: `v1.7.0-alpha.11` (all forks).

Spec-markdown line citations (`<file>.md:NN`) resolve under `specs/` in
`ethereum/consensus-specs` at the pinned version (also a git tag there) and are valid
at this pin; every re-pin re-checks them alongside the divergences they anchor.

## Fulu

_No open discrepancies._ Every collected in-scope minimal and mainnet vector passes
by root or rejects faithfully (`epoch_processing`, `operations` incl. standalone
`execution_payload`, `sanity/blocks`, `sanity/slots`, `finality`, `random`,
`rewards`, `fork_choice` incl. the PeerDAS data-availability `on_block` cases and
`get_proposer_head`), with zero `xfail`. The only Fulu vectors not run are the
deselected out-of-scope ones (`IMPLEMENTATION_NOTES.md`, "Scope and conformance"): the Fulu `fork` /
`transition` formats (the Electra→Fulu upgrade / boundary, needing an Electra parent
fork) and the `ssz_static` / `light_client` / `networking` / `merkle_proof` / `sync`
runners.

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
above propagated to Gloas with no Gloas-side change. The fork-choice asserts and plain-`Dict`
reads throw faithfully, including `get_forkchoice_store`'s anchor-root assert (shared with Fulu
and Heze) and the PTC block-replay vote writes (`notify_ptc_messages` routes through the
throwing `on_payload_attestation_message`). `compute_pulled_up_tip` now propagates its
`process_justification_and_finalization` reject instead of swallowing it, and
`get_block_root_at_slot` carries the pyspec recency assert (`slot < state.slot <= slot +
SLOTS_PER_HISTORICAL_ROOT`) again, so that reject is reachable rather than dead. All
catalogued in `IMPLEMENTATION_NOTES.md`, "Fork choice" and "Heze diff".

## Heze

_No open discrepancies._ EIP-7805 (FOCIL) ships no behavioral conformance vector at
`v1.7.0-alpha.11`; the two new containers pass their full `ssz_static` suites, and the
inherited Gloas spine and fork choice pass every in-scope Heze vector by root or reject
faithfully, with no `xfail`. The vectorless FOCIL layer carries deliberate divergences
from the spec text; those are implementation choices no vector observes, catalogued in
`IMPLEMENTATION_NOTES.md`, "Heze diff". Where a build-enforced pin covers one, the
entry names it.
