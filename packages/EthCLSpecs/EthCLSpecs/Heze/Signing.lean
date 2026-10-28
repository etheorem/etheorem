import EthCLSpecs.Heze.EpochProcessing
import EthCLSpecs.Heze.Containers

/-!
# `EthCLSpecs.Heze.Signing`: the EIP-7805 (FOCIL) inclusion-list signature predicate

Heze inherits the domain accessor and the rest of the signing surface from its
lineage; this file adds
the one new predicate EIP-7805 introduces. `is_valid_inclusion_list_signature` (the "Predicates"
section, `consensus-specs/specs/heze/beacon-chain.md:241-256`) checks a `SignedInclusionList`'s
BLS signature under `DOMAIN_INCLUSION_LIST_COMMITTEE`. At v1.7.0-beta.4 the domain comes from
the fork schedule at the list's epoch (`compute_fork_version`), not from the state's own fork,
so the file also carries Heze's `compute_fork_version`. `blsVerifySigned` is the residual trust
boundary (the `[CryptoBackend]` seam), as for every other signature predicate; no pure assertion
pins it. FOCIL adds no state transition, so this is a predicate rather than a transition step,
though it throws on an out-of-range `validator_index` (the spec's `state.validators[index]`
`IndexError`) rather than returning an answer there.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

state_section

/-- `compute_fork_version(epoch)` (Heze, `heze/p2p-interface.md:100-120`): the fork version
in effect at `epoch` under the config's fork schedule, from the latest fork whose epoch has
been reached, down to `GENESIS_FORK_VERSION`. The spec declares it in the p2p document, and
the beacon-chain predicate `is_valid_inclusion_list_signature` calls it, so it is modeled
here. The schedule is config, so a vector's fork-epoch overrides reach it. Pure. -/
forkdef computeForkVersion (epoch : Epoch) : Version :=
  if epoch ≥ Const.hezeForkEpoch then Const.hezeForkVersion
  else if epoch ≥ Const.gloasForkEpoch then Const.gloasForkVersion
  else if epoch ≥ Const.fuluForkEpoch then Const.fuluForkVersion
  else if epoch ≥ Const.electraForkEpoch then Const.electraForkVersion
  else if epoch ≥ Const.denebForkEpoch then Const.denebForkVersion
  else if epoch ≥ Const.capellaForkEpoch then Const.capellaForkVersion
  else if epoch ≥ Const.bellatrixForkEpoch then Const.bellatrixForkVersion
  else if epoch ≥ Const.altairForkEpoch then Const.altairForkVersion
  else Const.genesisForkVersion

/-- `is_valid_inclusion_list_signature(state, signed_inclusion_list)` (EIP-7805,
`consensus-specs/specs/heze/beacon-chain.md:241-256`): the `InclusionList` carries a valid BLS
signature by its committee member's key under `DOMAIN_INCLUSION_LIST_COMMITTEE` at the
message's epoch. Mirrors the Python step-for-step: read `message`, the validator `pubkey` at
`validator_index`, the domain, `compute_signing_root(message, domain)`, then `bls.Verify`.

v1.7.0-beta.4 computes the domain as `compute_domain(DOMAIN_INCLUSION_LIST_COMMITTEE,
compute_fork_version(compute_epoch_at_slot(message.slot)), state.genesis_validators_root)`.
alpha.12 used `get_domain(state, …)`, which takes the fork version from the state's own
`fork` field. The new form signs under the version scheduled for the list's slot, so a list
validates against the right version even when the state that judges it sits on the other
side of a fork boundary.

The signature check itself, `blsVerifySigned`, goes through the `[CryptoBackend]` seam
(`FRAMEWORK_ARCHITECTURE.md` §1), and no build-enforced pin fixes its answer. That is the
same trust boundary every signature predicate keeps (Gloas's bid and builder-deposit
signatures included).

Its in-model caller is `on_inclusion_list`, which asserts it at v1.7.0-beta.4. The p2p
`inclusion_list` gossip `[REJECT]` rule also calls it, and EthCLSpecs models the
state-transition and fork-choice layers, not p2p gossip.

It throws (`StateTransition`) rather than returning a `Bool` purely, because `state.validators[index]`
is a bare list index in the spec, raising `IndexError` on an out-of-range `validator_index`, not
returning `False`. -/
forkdef isValidInclusionListSignature (state : State) (signed : SignedInclusionList) :
    StateTransition Bool := do
  let message := signed.message
  let index := message.validatorIndex
  -- `validator_index` arrives off the wire, so the spec's `state.validators[index]` raises
  -- `IndexError` for an out-of-range index rather than yielding an answer: `sszGetIdx`
  -- (→ `outOfBounds`), the monadic safe read, in place of an `if index < size` guard that would
  -- mask the raise as a `false` and read the `Inhabited` default (zero-pubkey) validator.
  let validator ← sszGetIdx (sszGet state validators) index.toNat
  let pubkey := validator.pubkey
  let domain := computeDomain Const.domainInclusionListCommittee
    (computeForkVersion (computeEpochAtSlot message.slot)) (sszGet state genesisValidatorsRoot)
  return blsVerifySigned pubkey message domain signed.signature

end

end EthCLSpecs.Heze
