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

Every collected in-scope Gloas vector passes by root or rejects faithfully,
except the Gloas-state records the client-divergence subsection below
table-skips at this pin.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `formats/function/gloas/minimal/EthCLSpecs.Gloas.initiateBuilderExit/EthCLSpecs.Proofs.Gloas.initiateBuilderExit_run_eq_0` | `gloas/beacon-chain.md`, `initiate_builder_exit` (the bare `state.builders[builder_index]`) | etheorem/etheorem#129 | Fixed in Lean |

The one resolved entry was a Lean-side gap: Lean's
`[i]!` write answered `default` and no-op where the pyspec's bare
`state.builders[builder_index]` read raises `IndexError`. Closed by reading
the registry through `sszGetIdx` in `initiateBuilderExit`, so the case now
rejects faithfully.

### Client divergence: Prysm v7.2.1 merkleizes Gloas states progressively

Discovered by the stage-10 conformance harness (`clients/prysm/`, THEOREM_VECTORS_PLAN.md
step 3): every function-format record whose input is a Gloas `BeaconState` fails
the harness's root gate, at both presets, on every input the record carries.
Fulu states, the PTC window entries, and every scalar-mapped record pass the
same gate, so the divergence is Gloas-state-specific.

- Records: `records/gloas/{minimal,mainnet}/processBuilderPendingPayments_run/000`,
  `records/gloas/minimal/canBuilderCoverBid_iff/{000_t,001_f,002_f}`,
  `records/gloas/minimal/initiateBuilderExit_run_eq/000`.
- Both answers, on the upstream archive's own `ssz_static/BeaconState/ssz_zero/case_0`
  bytes (`tests/minimal/gloas/ssz_static/BeaconState/ssz_zero/case_0`, decompressed):
  upstream `roots.yaml` says `0x1246d33091795ab43bd13acfacda2e1d5a284948ea2c76f591ecfdd62363c4d3`;
  the Lean engine computes exactly that root (and reproduces the record file roots
  byte for byte); Prysm v7.2.1's generated `HashTreeRoot` computes
  `0xade6916205e64fddd2390239e6d2a971b7cc30eb34d80e459295ad43bbdcad09`, and its
  native state hasher computes a third value,
  `0xe87d50c6faa4c9d53fb2a311e3ede4e69a9c435725e501f7343bf5b137272148`.
- Root cause, read off the pinned client's generated code
  (`proto/prysm/v1alpha1/gloas.ssz.go`): `BeaconStateGloas.HashTreeRootWith`
  delegates to `ProgressiveHashTreeRootWith`, and the whole Gloas container
  family hashes through the progressive merkleization helpers
  (`MerkleizeProgressiveWithActiveFields`, `PutProgressiveBitlist`,
  `MerkleizeProgressiveWithMixin`). That is the EIP-7495 progressive format,
  which this repository's scope statement puts outside the SSZ universe.
  The pinned vector archive (`v1.7.0-alpha.11`) carries classic roots, and the
  Lean engine matches them; Prysm's decode of the same bytes round-trips
  byte-identically, so only the merkleization diverges.
- Client-side evidence: Prysm's own gloas `ssz_static` runner appends both its
  generated (progressive) root and its native root and checks both against the
  single classic `root` key; on the pinned archive's BeaconState cases both
  checks measure red, so the client does not concretely pass these vectors
  either at this pin.

Not closable by bending either side: the Lean side matches the pinned upstream
vectors, and the client implements a newer merkleization format than the
repository's pin. Decision taken (stage 10): the Gloas-state records table-skip
in the coverage table with this reason, and the migration is tracked upstream in
etheorem/etheorem#128 (the progressive forms in `SizzLean`, the Gloas switch,
the regeneration). Byte-level agreement of the mapped functions is proven there.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `client/prysm-v7.2.1` vs every Gloas `BeaconState` root (stage 10) | `gloas/beacon-chain.md` (classic merkleization at the pin) vs EIP-7495 progressive containers in the client | etheorem/etheorem#128 | tabled skip at this pin; closes with #128 |

## Heze

_No open discrepancies._ EIP-7805 (FOCIL) ships no behavioral conformance vector at
`v1.7.0-alpha.11`, so there is no Lean-versus-vector divergence to record for the FOCIL
layer. Its deliberate divergences from the spec text are catalogued in
`IMPLEMENTATION_NOTES.md`, "Heze diff".
