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

Pin: `v1.7.0-beta.4` (all forks).

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

The v1.7.0-beta.4 re-pin found four Lean-side gaps against the spec text that no vector
observed. Three are in the deposit path: the tree had kept its Electra forms after Fulu
removed the old deposit mechanism (consensus-specs #4704, in the text since alpha.12). The
fourth is a missing blob-count assert in `process_execution_payload`. All four are fixed in
Lean. The Fulu
vectors passed before and after, so the rows cite the spec text alone.

| Spec citation | Lean-side gap | Resolution |
|---|---|---|
| `fulu/beacon-chain.md:178`, `process_operations` | ran the Electra deposit-count gate and the `process_deposit` loop; the text asserts `len(body.deposits) == 0` | Fixed in Lean |
| `fulu/beacon-chain.md:206`, `process_deposit_request` | wrote `deposit_requests_start_index` on the first request; the text no longer does | Fixed in Lean |
| `fulu/beacon-chain.md:415`, `process_pending_deposits` | stopped at the eth1 bridge; the text has no such stop | Fixed in Lean |
| `fulu/beacon-chain.md:115`, `process_execution_payload` | no bound on the blob count; the text asserts `len(body.blob_kzg_commitments) <= get_blob_parameters(get_current_epoch(state)).max_blobs_per_block` | Fixed in Lean (`BLOB_SCHEDULE`, `get_blob_parameters`) |

The checked-arithmetic port (`SPEC_ARITHMETIC.md`) found four more Lean-side gaps that no vector
observed: four sites where Lean's raw `UInt64` wrapped and the pyspec raises. `Epoch` and `Slot`
moved to the checked type, all four sites now raise where the pyspec raises, and
`EthCLSpecs/Tests/FuluArithPins.lean` pins each raise at a value near `2^64`. The Gloas
`registry_updates` substep is inherited, so the `initiate_validator_exit` fix propagated as the
overflow fix above did.

| Spec citation | Lean-side gap | Resolution |
|---|---|---|
| `phase0/beacon-chain.md`, `compute_start_slot_at_epoch` | `epoch * SLOTS_PER_EPOCH` wrapped; the pyspec raises at the multiply's out-of-range product | Fixed in Lean, pinned in `FuluArithPins.lean` |
| `phase0/beacon-chain.md`, `compute_activation_exit_epoch` | `epoch + 1 + MAX_SEED_LOOKAHEAD` wrapped at the top of the chain | Fixed in Lean, pinned in `FuluArithPins.lean` |
| `electra/beacon-chain.md`, `initiate_validator_exit` | `withdrawable_epoch = exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` wrapped | Fixed in Lean, pinned in `FuluArithPins.lean` |
| `electra/beacon-chain.md`, `process_withdrawal_request` | the same sum at the partial withdrawal's `withdrawable_epoch` bind | Fixed in Lean, pinned in `FuluArithPins.lean` |

Two corners of the checked arithmetic are recorded rather than fixed. No vector reaches either,
and both stay on the record per the policy above.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| none; no vector reaches it | `electra/beacon-chain.md`, `process_attestation` (the committee-coverage checks) | none | Recorded. On a state slot near `2^64`, a later committee's arithmetic fault can preempt an earlier rung's caught assert reject in `verifyCommitteeCoverage`. The fault order differs from the pyspec; both sides reject, and the harness classifies both as rejects. |
| none; no shipped config reaches it | `phase0/beacon-chain.md`, `compute_slot_at_time_ms` | none | Recorded. `computeSlotAtTimeMs` divides by the config value `slotDurationMs` with no positivity premise, so Lean returns `0` where the pyspec raises `ZeroDivisionError`. Both shipped configs are nonzero. `SPEC_ARITHMETIC.md` §7 lists the wrapper that closes it. |

## Gloas

_No open discrepancies._ Gloas is fully ported (the EIP-7732 ePBS spine, that is the
state-transition pipeline, plus operations, fork choice, and the Fulu→Gloas
transition); every in-scope minimal and mainnet vector passes by root or rejects
faithfully, with no `xfail`. Gloas inherits the Fulu `registry_updates` substep (the
DSL re-elaborates the captured `forkdef` in the Gloas namespace), so the overflow fix
above propagated to Gloas with no Gloas-side change. Deliberate divergences are
catalogued in `IMPLEMENTATION_NOTES.md`, "Gloas diff" and "Fork choice".

The Gloas `process_pending_deposits` (`gloas/beacon-chain.md:1659`) is a Gloas override, and
it carried the same stale eth1-bridge stop as the Fulu body above. The beta.4 re-pin removed
it with the Fulu fix; no vector observed it.

## Heze

_No open discrepancies._ The Gloas→Heze `fork` vectors are in scope, and at v1.7.0-beta.4
every in-scope minimal and mainnet vector passes by root or rejects faithfully, with no
`xfail`. FOCIL's deliberate divergences from the spec text stay in `IMPLEMENTATION_NOTES.md`,
"Heze diff".

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `minimal/heze/fork/fork/pyspec_tests/fork_base_state` | `heze/fork.md:41`, `upgrade_to_heze` | none | Resolved upstream at v1.7.0-beta.4 |
| `mainnet/heze/fork/fork/pyspec_tests/fork_base_state` | `heze/fork.md:41`, `upgrade_to_heze` | none | Resolved upstream at v1.7.0-beta.4 |

At alpha.12 both rows were open. Their pre-state was not a Gloas state, and their post-state
was not the output of `upgrade_to_heze`, so Lean followed the spec text and the harness
reported the two cases as `xfail`. The beta.4 vectors are a Gloas pre-state and its
`upgrade_to_heze` output, Lean matches them, and the harness's `SPEC_TEXT_DIVERGENCES` set
is empty. The alpha.12 evidence, kept for the audit trail:

The pre-state's fork current version was already Heze (`0x08000001` minimal,
`0x08000000` mainnet). On minimal the bid's first variable offset was 226, where a
Gloas bid's prefix is 224, so the bid was the 13-field Heze container. On both presets
the pre-state was two bytes larger than the sibling Gloas pre-states. The post-state's
`fork.current_version` was the bytes `e8 14 80 00`, which is not `HEZE_FORK_VERSION`.
A correct upgrade of a Gloas state grows by those two inclusion-list bytes; those
posts grew by 516 bytes (minimal) and 2052 bytes (mainnet).
