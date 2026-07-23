import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.Signing`: the EIP-7805 (FOCIL) inclusion-list signature predicate

Heze inherits the domain accessor and the rest of the signing surface from Fulu; this file adds
the one new predicate EIP-7805 introduces. `is_valid_inclusion_list_signature` (the "Predicates"
section, `consensus-specs/specs/heze/beacon-chain.md:76-87`) checks a `SignedInclusionList`'s BLS
signature under `DOMAIN_INCLUSION_LIST_COMMITTEE`. `blsVerifySigned` is the residual trust
boundary (the `[CryptoBackend]` seam), as for every other signature predicate; no pure assertion
pins it. FOCIL adds no state transition, so this is a predicate rather than a transition step,
though it throws on an out-of-range `validator_index` (the spec's `state.validators[index]`
`IndexError`) rather than returning a verdict there.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

state_section

/-- `is_valid_inclusion_list_signature(state, signed_inclusion_list)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:76-87`): the `InclusionList` carries a valid BLS
signature by its committee member's key under `DOMAIN_INCLUSION_LIST_COMMITTEE` at the
message's epoch. Mirrors the Python step-for-step: read `message`, the validator `pubkey` at
`validator_index`, the domain, `compute_signing_root(message, domain)`, then `bls.Verify`.

The signature check itself, `blsVerifySigned`, goes through the `[CryptoBackend]` seam
(`FRAMEWORK_ARCHITECTURE.md` §1), and no build-enforced pin fixes its verdict. That is the
same trust boundary every signature predicate keeps (Gloas's bid and builder-deposit
signatures included).

The predicate has no in-model caller, by design. Its sole consumer in the spec is the p2p
`inclusion_list` gossip `[REJECT]` rule (`p2p-interface.md:100`), and EthCLSpecs models the
state-transition and fork-choice layers, not p2p gossip (`networking` is out of the
conformance scope). `on_inclusion_list` carries no signature check of its own
(`fork-choice.md:256-267`), so the fork-choice path mirrors the spec faithfully. Kept as the
beacon-chain surface for spec-completeness.

It throws (`StateTransition`) rather than returning a `Bool` purely, because `state.validators[index]`
is a bare list index in the spec, raising `IndexError` on an out-of-range `validator_index`, not
returning `False`. -/
forkdef isValidInclusionListSignature (state : State) (signed : SignedInclusionList) :
    StateTransition Bool := do
  let message := signed.message
  let index := message.validatorIndex
  -- `validator_index` arrives off the wire, so the spec's `state.validators[index]` raises
  -- `IndexError` for an out-of-range index rather than yielding a verdict: `sszGetIdx`
  -- (→ `outOfBounds`), the monadic safe read, in place of an `if index < size` guard that would
  -- mask the raise as a `false` and read the `Inhabited` default (zero-pubkey) validator.
  let validator ← sszGetIdx (sszGet state validators) index.toNat
  let pubkey := validator.pubkey
  let domain := getDomain state Const.domainInclusionListCommittee (computeEpochAtSlot message.slot)
  return blsVerifySigned pubkey message domain signed.signature

end

end EthCLSpecs.Heze
