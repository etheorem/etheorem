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
link, so the audit trail is one grep away.

Pin: `v1.7.0-alpha.10` (both forks).

## Fulu

_No open discrepancies._ Every collected in-scope minimal and mainnet vector passes
by root or rejects faithfully (`epoch_processing`, `operations` incl. standalone
`execution_payload`, `sanity/blocks`, `sanity/slots`, `finality`, `random`,
`rewards`, `fork_choice` incl. the PeerDAS data-availability `on_block` cases and
`get_proposer_head`), with zero `xfail`. The only Fulu vectors not run are the
deselected out-of-scope ones (`IMPLEMENTATION_NOTES.md` §2.x): the Fulu `fork` /
`transition` formats (the Electra→Fulu upgrade / boundary, needing an Electra parent
fork) and the `ssz_static` / `light_client` / `networking` / `merkle_proof` / `sync`
runners.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| — | — | — | — |

**Resolved.** `epoch_processing/registry_updates/.../invalid_large_withdrawable_epoch`
was an open Lean-side gap (Lean's `UInt64` wrapped where the pyspec raises a
`ValueError` serializing the overflowed `withdrawable_epoch`). Closed by asserting
the `exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` bound in
`initiateValidatorExit`, so the case now rejects faithfully.

## Gloas

_No open discrepancies._ Gloas is fully ported (the EIP-7732 ePBS spine, operations,
fork choice, and the Fulu→Gloas transition); every in-scope minimal and mainnet
vector passes by root or rejects faithfully, with no `xfail`. Gloas inherits the Fulu
`registry_updates` substep (`forkdef` replay), so the overflow fix above propagated to
Gloas with no Gloas-side change.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| — | — | — | — |
