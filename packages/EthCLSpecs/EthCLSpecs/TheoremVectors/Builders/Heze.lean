import EthCLLib.TheoremVectors.Types
import EthCLSpecs.TheoremVectors.Builders.Gloas
import EthCLSpecs.Heze.Operations
import EthCLSpecs.Heze.Upgrade
import EthCLSpecs.Heze.Transition

/-!
# `EthCLSpecs.TheoremVectors.Builders.Heze`: the Heze state-builder catalog

The Heze state-builder catalog of `THEOREM_VECTORS_ARCHITECTURE.md` §9.9: fork
functions that run the spec itself to produce a reachable state from a few
knobs, the `built` witness searcher's raw material. Four builders, cheapest
first:

- `genesis`: the fork's genesis state over `validators` deposits of
  `balance`, every validator active. It reproduces the deposit side of
  the pyspec's `create_genesis_state`: the effective balance rounds down
  to the increment the way `get_validator_from_deposit` rounds it, and
  activation sits at the genesis epoch. The fork record carries the
  fork's own version on both sides; the RANDAO mixes and the genesis
  block header keep their defaults, which is the empty chain's own state
  of them.
- `advanced`: `genesis`, then `processSlots` to the target slot, so the
  epoch boundaries the target passes run `process_epoch` and the state
  carries real justification, committees, and RANDAO mixes. The
  `processSlots` is Heze's own inherited replay of the Gloas body.
- `upgraded`: the parent fork's `advanced` state
  (`Builders.Gloas.advanced`) through `upgradeToHeze`, so the fork
  boundary's fork record names two versions, the Gloas one as the
  previous and the config's Heze one as the current.
- `withQueue`: `advanced`, plus `queue` pending deposits appended and
  drained through the spec's own onboarding step
  (`onboardBuildersFromPendingDeposits`, the Heze replay of Gloas's
  body), so the builder registry holds builders the registry's own path
  put there. Even-indexed deposits carry the builder
  withdrawal-credential prefix and land in the registry; odd-indexed
  ones carry the eth1 prefix for fresh pubkeys above the genesis
  registry and stay queued as new-validator deposits.

Deposit identities come from the index-derived identity layer in
`Builders.Fulu` (`pubkeyOf`, `credentialsOf`, `builderPubkeyOf`), the
one home every fork's catalog shares; Gloas's catalog uses it the same
way. Under the verify-off backend any 48-byte value verifies, so the
catalog derives both from the deposit's index. Builder identities sit
above every validator identity, so a builder pubkey never collides with
a validator pubkey. That is what the registry lookups by pubkey need
(`validatorIndexByPubkey?`, the onboarding dedup). A builder that needs
a real signature is outside this catalog (§9.9).

The transitions run at the fast config over `SSZ.FastBox`, the
configuration the pyspec runner runs. A reject falls back to the state
the builder started from, so a builder never fails its vector.
`upgraded` runs the parent fork's `advanced` under the Heze preset
through the `Downgrade` bridge, the same reach `Upgrade.lean` takes at
the fork boundary. The fork record's version reads the config tier's
`hezeForkVersion`, the seam `Heze/Constants.lean` carries beside its
pinned plain defs. The hasher is the binding's `fastHasherTag`, pinned
locally the way the fork interface pins it, so a builder constant
carries only the binders its own body names: `[Preset] [Config]`, plus
`[CryptoBackend]` where the spec's signature checks reach the seam
(§9.9's sketch names `[Preset] [Config]` alone;
`IMPLEMENTATION_NOTES.md` records the deviation).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.TheoremVectors (Knobs)
open EthCLSpecs.Heze
open SizzLean.Cache
open SizzLean.Hasher

-- The fork boundary: like `Upgrade.lean`, this file reaches the parent
-- fork's spine, and the downgrade bridge is what lets a Gloas state build
-- under a single Heze `[Preset]` binder.
open scoped EthCLSpecs.Heze.Downgrade

namespace EthCLSpecs.TheoremVectors.Builders.Heze

/-! ## The builders -/

/-- The genesis validator at `index`: the deposit's balance rounded down
to the increment and capped at the eth1-credential maximum, the way
`get_validator_from_deposit` computes a deposit's effective balance, and
active from the genesis epoch, the way the pyspec's `create_genesis_state`
leaves its deposits. -/
def genesisValidator [Preset] (index : Nat) (balance : Gwei) : Validator :=
  { pubkey := Fulu.pubkeyOf index
    withdrawalCredentials := Fulu.credentialsOf Const.eth1AddressWithdrawalPrefix index
    effectiveBalance :=
      umin (balance - balance % Const.effectiveBalanceIncrementG)
        Const.maxEffectiveBalanceG
    slashed := false
    activationEligibilityEpoch := Const.genesisEpoch
    activationEpoch := Const.genesisEpoch
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- `genesis`: the fork's genesis state over `knobs.validators` deposits of
`knobs.balance`, every validator active. The two participation lists and
`inactivityScores` hold one zero entry per validator.
`eth1_data.deposit_count` and `eth1_deposit_index` name the same count
the registry holds. The fork record carries the config's
`hezeForkVersion` on both sides. The pyspec's `create_genesis_state`
names the parent fork's version as the previous one at a later fork;
this builder keeps the fork's own on both sides, so a client that reads
`previous_version` as the true parent version reads the Heze one.
`upgraded` is the one builder whose fork record names two versions. -/
def genesis [Preset] [Config] (knobs : Knobs) : BeaconState :=
  let balance : Gwei := UInt64.ofNat knobs.balance
  let vs : SSZList Validator Const.validatorRegistryLimit :=
    (Array.range knobs.validators).foldl
      (fun xs i => xs.push (genesisValidator i balance)) default
  let bs : SSZList Gwei Const.validatorRegistryLimit :=
    (Array.range knobs.validators).foldl (fun xs _ => xs.push balance) default
  -- the per-validator lists the epoch step indexes by validator index:
  -- one zero entry per validator, the way `create_genesis_state` appends
  -- one per deposit
  let flags : SSZList ParticipationFlags Const.validatorRegistryLimit :=
    vs.mapCap fun _ => 0
  let scores : SSZList UInt64 Const.validatorRegistryLimit :=
    vs.mapCap fun _ => 0
  { (default : BeaconState) with
    validators := vs
    balances := bs
    previousEpochParticipation := flags
    currentEpochParticipation := flags
    inactivityScores := scores
    eth1Data := { (default : Eth1Data) with depositCount := UInt64.ofNat knobs.validators }
    eth1DepositIndex := UInt64.ofNat knobs.validators
    forkData :=
      { previousVersion := Const.hezeForkVersion
        currentVersion := Const.hezeForkVersion
        epoch := Const.genesisEpoch } }

/-- Run one state-transition action at the fast config over
`SSZ.FastBox`, the configuration the pyspec runner runs. A reject falls
back to the input state, so a builder never fails its vector. The box
spells `Sha256`, the tag the binding's `fastHasherTag` names, because the
run needs one concrete hasher to typecheck against. -/
private def runState [Preset]
    (act : EStateM StateTransitionError (SSZ.Box Sha256 BeaconState) Unit)
    (s : BeaconState) : BeaconState :=
  match act.run (SSZ.FastBox s) with
  | .ok _ st => st.view
  | .error _ _ => s

/-- `advanced`: `genesis`, then `processSlots` to `knobs.slot`, the Heze
replay of the inherited Gloas body. Slot `0` fails `process_slots`'s own
`slot < target` assert and falls back to `genesis`, which is the same
state. The hasher is the binding's `fastHasherTag`, pinned locally the
way the fork interface pins it, so the builder constant carries only the
binders its body names. -/
def advanced [Preset] [Config] [CryptoBackend] (knobs : Knobs) :
    BeaconState :=
  letI : HasherTag := fastHasherTag
  runState (processSlots (UInt64.ofNat knobs.slot)) (genesis knobs)

/-- `upgraded`: the parent fork's `advanced` state
(`Builders.Gloas.advanced`) through the fork's own `upgradeToHeze`, with
the config's `hezeForkVersion`. The fork record at the boundary names two
versions: the previous version is the Gloas version the pre-state
carries, and the current version is the config's Heze version. The
runner's onboarding step follows the upgrade in the real path; here the
queue is empty, so it is a no-op and the builder skips it. The parent's
builders run under the Heze preset through the `Downgrade` bridge, the
same reach `Upgrade.lean` takes at the fork boundary. -/
def upgraded [Preset] [Config] [CryptoBackend] (knobs : Knobs) :
    BeaconState :=
  upgradeToHeze Const.hezeForkVersion (Gloas.advanced knobs)

/-- The pending deposit the queue's `i`-th slot carries, for a genesis
registry of `registrySize` validators: even-indexed slots hold a builder
deposit, whose credential prefix sends it to the registry; odd-indexed
slots hold a validator deposit for a fresh pubkey above the registry,
which the onboarding step keeps queued as a new-validator deposit. The
signature is the zero value, which the verify-off backend accepts, and
the slot stamps the deposit epoch at genesis. -/
def queueDeposit [Preset] (registrySize : Nat) (i : Nat) (amount : Gwei) :
    PendingDeposit :=
  if i % 2 == 0 then
    { pubkey := Fulu.builderPubkeyOf (i / 2)
      withdrawalCredentials := Fulu.credentialsOf Const.builderWithdrawalPrefix (i / 2)
      amount, signature := default, slot := Const.genesisSlot }
  else
    { pubkey := Fulu.pubkeyOf (registrySize + i / 2)
      withdrawalCredentials :=
        Fulu.credentialsOf Const.eth1AddressWithdrawalPrefix (registrySize + i / 2)
      amount, signature := default, slot := Const.genesisSlot }

/-- `withQueue`: `advanced`, plus `knobs.queue` pending deposits appended
and drained through the spec's own `onboardBuildersFromPendingDeposits`
(the Heze replay of Gloas's body), so the builder registry holds builders
the registry's own path put there and the queue holds what it kept.
§9.9's catalog row also lists withdrawals and builder payments; those
queues wait for a theorem that reads them. The crypto backend is the
caller's, as every spec operation's is; the builders run under whatever
backend the binding fixes, and the deposit signature checks accept under
verify-off. -/
def withQueue [Preset] [Config] [CryptoBackend] (knobs : Knobs) :
    BeaconState :=
  letI : HasherTag := fastHasherTag
  let balance : Gwei := UInt64.ofNat knobs.balance
  runState (do
    modifyState fun state =>
      sszUpdate state with pendingDeposits :=
        (Array.range knobs.queue).foldl
          (fun xs i => xs.push (queueDeposit knobs.validators i balance))
          (sszGet state pendingDeposits)
    onboardBuildersFromPendingDeposits)
    (advanced knobs)

end EthCLSpecs.TheoremVectors.Builders.Heze
