import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.Signing`: the EIP-7805 (FOCIL) inclusion-list signature predicate

Heze inherits the domain accessor and the rest of the signing surface from Fulu; this file adds
the one new predicate EIP-7805 introduces. `is_valid_inclusion_list_signature` (the "Predicates"
section, `consensus-specs/specs/heze/beacon-chain.md:76-87`) checks a `SignedInclusionList`'s BLS
signature under `DOMAIN_INCLUSION_LIST_COMMITTEE`. `blsVerifySigned` is the residual trust
boundary (the `[CryptoBackend]` seam), as for every other signature predicate; no pure assertion
pins it. FOCIL adds no state transition, so this is a pure predicate rather than a transition step.
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
beacon-chain surface for spec-completeness. -/
forkdef isValidInclusionListSignature (state : State) (signed : SignedInclusionList) : Bool :=
  let message := signed.message
  let index := message.validatorIndex
  let vs := sszGet state validators
  -- `validator_index` arrives off the wire, so bound it: the spec's `state.validators[index]`
  -- raises `IndexError` for an out-of-range index, rejecting the list. Reject explicitly rather
  -- than reading the `Inhabited` default (zero-pubkey) validator through `[…]!`.
  if index.toNat < vs.size then
    let pubkey := (vs[index.toNat]!).pubkey
    let domain := getDomain state Const.domainInclusionListCommittee (computeEpochAtSlot message.slot)
    blsVerifySigned pubkey message domain signed.signature
  else
    false

end

end EthCLSpecs.Heze
