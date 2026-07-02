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

Pin: `v1.7.0-alpha.11` (all forks).

Spec-markdown line citations (`<file>.md:NN`) are valid at this pin; every re-pin
re-checks them alongside the divergences they anchor.

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

## Heze

_No open vector discrepancies._ EIP-7805 (FOCIL) ships no behavioral conformance vector at
`v1.7.0-alpha.11` (the two new containers do get full `ssz_static` suites, which pass), so there
is no Lean-versus-vector divergence to record: the inherited Gloas spine and fork choice pass
every in-scope Heze vector by root or reject faithfully, with no `xfail`. The vectorless FOCIL
layer does carry deliberate divergences from the spec *text*, each pinned by the `Heze/*.lean`
`#guard`s rather than exercised by a runner, and each recorded here so the audit trail is one
grep away.

`is_inclusion_list_satisfied` (`heze/fork-choice.md:54-62`) defers its verdict to
`ExecutionEngine.is_inclusion_list_satisfied`, an Engine-API call against an external EL. This
harness has no execution layer, so the call routes through the `[ExecutionEngine]` seam
(`EthCLLib.Spec.Engine`), whose default instance answers the constant `true`, the same treatment
Gloas gives `verify_and_notify_new_payload` and `is_data_available`. That default is the residual
EL trust boundary of the FOCIL gate; no conformance vector reaches the discriminating `false`
branch, which the `pinRecordRefuted` pin drives end-to-end under a local refuting instance instead.
The sibling `is_payload_inclusion_list_satisfied` (`heze/fork-choice.md:199-212`) opens with `assert
root in store.payload_inclusion_list_satisfaction`; a pure `Bool` predicate cannot throw, so the Lean
reads a missing key as `false` through `lookupD`. That default sits off the spec path, since the
`payloads` / `payload_inclusion_list_satisfaction` co-write in `on_execution_payload_envelope` keeps
the key present whenever `root ∈ payloads`. The `timeliness` read in
`get_inclusion_list_transactions` is the same shape one store over: a plain dict read in the spec,
`lookupD false` in Lean, off-path through `process_inclusion_list`'s own co-write
(`Heze/InclusionList.lean`).

The other two are representational. `cyclicSample` (`heze/beacon-chain.md:95-110`) resamples the
committee as `indices[i % len(indices)]`, which raises `ZeroDivisionError` on an empty concatenation;
the Lean read is total (`i % 0 = i`, then the `getD` default), and a real beacon chain never reaches a
zero-active-validator slot, so the branch is unreachable (`Heze/Focil.lean`). The
`InclusionListStore` is folded into the fork-choice `Store` as a field: the spec keeps it as a
process-lifetime singleton (`heze/inclusion-list.md:28-38`, reached through
`get_inclusion_list_store()`), but this framework's pure `EStateM` fork choice has no ambient
mutable singleton to hang it off, so it rides inside `Store` and threads like every other piece of
state, behavior-complete at zero coverage cost (`Heze/InclusionList.lean`).

The rest are total-function elisions of a spec `assert`/raise, the same class as
`is_payload_inclusion_list_satisfied` above: latent (no alpha.11 vector reaches the branch) and
each guarded or bounded at its call site. `record_payload_inclusion_list_satisfaction`
(`heze/fork-choice.md`) reads `Slot(state.slot - 1)`; on a slot-0 state the pyspec raises the
uint64 underflow, invalidating the whole `on_execution_payload_envelope` call with the store
unmodified, while the Lean guards the underflow, records the verdict over an empty required set,
and proceeds (`Heze/ForkChoice.lean`, `recordPayloadInclusionListSatisfaction`). Only an envelope
whose target block state sits at slot 0 (the genesis anchor) could tell the difference, and no
vector produces one. `should_extend_payload` (`heze/fork-choice.md`) opens with `assert
store.blocks[root].slot + 1 == get_current_slot(store)`; a pure `Bool` forkdef cannot throw, so
the Lean elides the assert, and its one caller (`get_payload_status_tiebreaker`) is gated by
`is_previous_slot_payload_decision`, which enforces the same slot equation. The Gloas
`should_extend_payload` carries the identical elision, so this is inherited shape, recorded here
with the Heze layer that restates the body. Inside the same function, the spec also reads
`store.blocks[proposer_root]` unguarded (a `KeyError` on a boost root absent from `blocks`); the
Lean's `| none => true` extends instead, a miss-default in the *accepting* direction, unreachable
while the boost root is always a stored block (`on_block` sets it).
`is_valid_inclusion_list_signature`
(`heze/beacon-chain.md:76-87`) reads `state.validators[message.validator_index]`, which raises
`IndexError` on an out-of-range wire index; the Lean bounds the index and returns `false` instead
(`Heze/Focil.lean`). Same rejection, different mechanism, and no in-model caller by design.
`get_forkchoice_store` (`heze/fork-choice.md:140-166`) opens with `assert anchor_block.state_root
== hash_tree_root(anchor_state)`; the Lean restatement elides it (a pure constructor), so an
inconsistent anchor pair would seed a store instead of raising. Every fork_choice vector runs
through this constructor, but the harness always derives the anchor block and state from the same
vector's files, so the branch is unreachable in conformance; the Gloas and Fulu constructors carry
the identical elision. Below this threshold, one framework-wide note: the inherited time
arithmetic (`timeIntoSlotMs`, the store-time seed) wraps `UInt64` where the pyspec saturates or
raises, observable only at astronomically unreachable uptimes.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| — | — | — | — |
