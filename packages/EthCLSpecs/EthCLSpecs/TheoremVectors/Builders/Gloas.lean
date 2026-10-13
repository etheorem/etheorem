import EthCLLib.TheoremVectors.Types
import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Gloas.Transition

/-!
# `EthCLSpecs.TheoremVectors.Builders.Gloas`: the Gloas state-builder catalog

The state-builder catalog of `THEOREM_VECTORS_ARCHITECTURE.md` §9.9: fork functions
that run the spec itself to produce a reachable state from a few knobs, the
`built` witness source's raw material. Four builders, cheapest first:

- `genesis`: the fork's genesis state over `validators` deposits of
  `balance`, every validator active. It reproduces the deposit side of
  the pyspec's `create_genesis_state`: the effective balance rounds down
  to the increment the way `get_validator_from_deposit` rounds it, and
  activation sits at the genesis epoch. The fork versions, the RANDAO
  mixes, and the genesis block header keep their defaults, which is the
  empty chain's own state of them.
- `advanced`: `genesis`, then `processSlots` to the target slot, so the
  epoch boundaries the target passes run `process_epoch` and the state
  carries real justification, committees, and RANDAO mixes.
- `upgraded`: the parent fork's `advanced` state through `upgradeToGloas`,
  so the fork-specific fields (`latestBlockHash`, `ptcWindow`, the ePBS
  block) hold the values the fork boundary gives them.
- `withQueue`: `advanced`, plus `queue` pending deposits appended and
  drained through the spec's own onboarding step
  (`onboardBuildersFromPendingDeposits`), so the builder registry holds
  builders the registry's own path put there. Even-indexed deposits carry
  the builder withdrawal-credential prefix and land in the registry;
  odd-indexed ones carry the eth1 prefix for fresh pubkeys above the
  genesis registry and stay queued as new-validator deposits.

Deposits need pubkeys and credentials. Under the verify-off backend any
48-byte value verifies, so the catalog derives both from the deposit's
index. Builder identities sit above every validator identity, so a
builder pubkey never collides with a validator pubkey. That is what the
registry lookups by pubkey need (`validatorIndexByPubkey?`, the
onboarding dedup). A builder that needs a real signature is outside
this catalog (§9.9).

The transitions run at the fast config over `SSZ.FastBox`, the
configuration the pyspec runner runs. A reject falls back to the state
the builder started from, so a builder never fails its vector. The
Fulu-side helpers run under the Gloas preset through the `Downgrade`
bridge, the same reach `Upgrade.lean` takes at the fork boundary. The
hasher is the binding's `fastHasherTag`, pinned locally the way the fork
interface pins it, so a builder constant carries only the binders its
own body names: `[Preset] [Config]`, plus `[CryptoBackend]` where the
spec's signature checks reach the seam (§9.9's sketch names `[Preset]
[Config]` alone; `IMPLEMENTATION_NOTES.md` records the deviation).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.TheoremVectors (Knobs)
open EthCLSpecs.Gloas
open SizzLean.Cache
open SizzLean.Hasher

-- The fork boundary: like `Upgrade.lean`, this file reaches the parent
-- fork's spine, and the downgrade bridge is what lets a Fulu state build
-- under a single Gloas `[Preset]` binder.
open scoped EthCLSpecs.Gloas.Downgrade

namespace EthCLSpecs.TheoremVectors.Builders.Gloas

/-! ## Index-derived identity -/

/-- The little-endian bytes of `index`, at byte width `w`, the shared
shape of every index-derived identity below. -/
private def indexBytes (w : Nat) (index : Nat) (i : Nat) : UInt8 :=
  if i < w then UInt8.ofNat ((index / 2 ^ (8 * i)) % 256) else 0

/-- The pubkey of the identity at `index`: the index in the first 8
bytes, little-endian, the rest zero. -/
def pubkeyOf (index : Nat) : BLSPubkey :=
  Vector.ofFn (fun i : Fin 48 => indexBytes 8 index i.val)

/-- The withdrawal credentials of the identity at `index`: the prefix
byte, then the index in the next 8 bytes, the rest zero. `tag` carries
the prefix because `prefix` is a Lean keyword. -/
def credentialsOf (tag : UInt8) (index : Nat) : Bytes32 :=
  Vector.ofFn (fun i : Fin 32 =>
    if i.val == 0 then tag else indexBytes 8 index (i.val - 1))

/-- The base every builder identity's pubkey sits above, so a builder
pubkey never collides with a validator pubkey: a validator index is far
below `2 ^ 40`, and the derivation puts the index in the low 8 bytes. -/
def builderPubkeyBase : Nat := 0x10000000000

/-- The pubkey of the builder at `index`, above the validator range. -/
def builderPubkeyOf (index : Nat) : BLSPubkey := pubkeyOf (builderPubkeyBase + index)

/-! ## The builders -/

/-- The genesis validator at `index`: the deposit's balance rounded down
to the increment and capped at the eth1-credential maximum, the way
`get_validator_from_deposit` computes a deposit's effective balance, and
active from the genesis epoch, the way the pyspec's `create_genesis_state`
leaves its deposits. -/
def genesisValidator [Preset] (index : Nat) (balance : Gwei) : Validator :=
  { pubkey := pubkeyOf index
    withdrawalCredentials := credentialsOf Const.eth1AddressWithdrawalPrefix index
    effectiveBalance :=
      umin (balance - balance % Const.effectiveBalanceIncrementG)
        Const.maxEffectiveBalanceG
    slashed := false
    activationEligibilityEpoch := Const.genesisEpoch
    activationEpoch := Const.genesisEpoch
    exitEpoch := Const.farFutureEpoch
    withdrawableEpoch := Const.farFutureEpoch }

/-- `genesis`: the fork's genesis state over `knobs.validators` deposits
of `knobs.balance`, every validator active. `eth1_data.deposit_count` and
`eth1_deposit_index` name the same count the registry holds, and the fork
version is the config's own, both sides of the fork record at the genesis
epoch, the way the pyspec's `create_genesis_state` leaves the fork
record. A client that reads `previous_version` as the true parent
version reads the Gloas one. `upgraded` is the one builder whose fork
record names two versions. -/
def genesis [Preset] [Config] (knobs : Knobs) : BeaconState :=
  let balance : Gwei := UInt64.ofNat knobs.balance
  let vs : SSZList Validator Const.validatorRegistryLimit :=
    (Array.range knobs.validators).foldl
      (fun xs i => xs.push (genesisValidator i balance)) default
  let bs : SSZList Gwei Const.validatorRegistryLimit :=
    (Array.range knobs.validators).foldl (fun xs _ => xs.push balance) default
  { (default : BeaconState) with
    validators := vs
    balances := bs
    eth1Data := { (default : Eth1Data) with depositCount := UInt64.ofNat knobs.validators }
    eth1DepositIndex := UInt64.ofNat knobs.validators
    forkData :=
      { previousVersion := Const.gloasForkVersion
        currentVersion := Const.gloasForkVersion
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

/-- `advanced`: `genesis`, then `processSlots` to `knobs.slot`. Slot `0`
fails `process_slots`'s own `slot < target` assert and falls back to
`genesis`, which is the same state. The hasher is the binding's
`fastHasherTag`, pinned locally the way the fork interface pins it, so
the builder constant carries only the binders its body names. -/
def advanced [Preset] [Config] [CryptoBackend] (knobs : Knobs) :
    BeaconState :=
  letI : HasherTag := fastHasherTag
  runState (processSlots (UInt64.ofNat knobs.slot)) (genesis knobs)

/-! ### The parent fork's side of `upgraded`

Stage 9's `Builders/Fulu.lean` catalog will own these; they live here as
private helpers until that stage, because `upgraded` is the only
consumer and the catalog must not grow a public surface twice. -/

/-- The Fulu genesis validator, the parent's copy of `genesisValidator`,
with the same increment rounding. The helpers carry `EthCLSpecs.Fulu`
names because the two forks' containers are distinct types at the
boundary (`Gloas.Inherited` replays them). -/
private def fuluGenesisValidator [Preset] (index : Nat) (balance : Gwei) :
    EthCLSpecs.Fulu.Validator :=
  { pubkey := pubkeyOf index
    withdrawalCredentials := credentialsOf EthCLSpecs.Fulu.Const.eth1AddressWithdrawalPrefix index
    effectiveBalance :=
      umin (balance - balance % EthCLSpecs.Fulu.Const.effectiveBalanceIncrementG)
        EthCLSpecs.Fulu.Const.maxEffectiveBalanceG
    slashed := false
    activationEligibilityEpoch := EthCLSpecs.Fulu.Const.genesisEpoch
    activationEpoch := EthCLSpecs.Fulu.Const.genesisEpoch
    exitEpoch := EthCLSpecs.Fulu.Const.farFutureEpoch
    withdrawableEpoch := EthCLSpecs.Fulu.Const.farFutureEpoch }

/-- The Fulu genesis state, the parent's copy of `genesis`. Its fork
record carries the chain's genesis fork version on both sides, the
version a Fulu state holds at genesis, so `upgraded`'s
`previous_version` reads the chain's pre-Gloas version rather than the
zero version. -/
private def fuluGenesis [Preset] [Config] (knobs : Knobs) :
    EthCLSpecs.Fulu.BeaconState :=
  let balance : EthCLSpecs.Fulu.Gwei := UInt64.ofNat knobs.balance
  let vs : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Validator
      EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    (Array.range knobs.validators).foldl
      (fun xs i => xs.push (fuluGenesisValidator i balance)) default
  let bs : SizzLean.Repr.SSZList EthCLSpecs.Fulu.Gwei
      EthCLSpecs.Fulu.Const.validatorRegistryLimit :=
    (Array.range knobs.validators).foldl (fun xs _ => xs.push balance) default
  { (default : EthCLSpecs.Fulu.BeaconState) with
    validators := vs
    balances := bs
    eth1Data := { (default : EthCLSpecs.Fulu.Eth1Data) with
                  depositCount := UInt64.ofNat knobs.validators }
    eth1DepositIndex := UInt64.ofNat knobs.validators
    forkData :=
      { previousVersion := EthCLSpecs.Fulu.Const.genesisForkVersion
        currentVersion := EthCLSpecs.Fulu.Const.genesisForkVersion
        epoch := EthCLSpecs.Fulu.Const.genesisEpoch } }

/-- The Fulu `advanced`, the parent's copy over the Fulu spine, under the
same local hasher pin. -/
private def fuluAdvanced [Preset] [Config] [CryptoBackend]
    (knobs : Knobs) : EthCLSpecs.Fulu.BeaconState :=
  letI : HasherTag := fastHasherTag
  let box : SSZ.Box Sha256 (EthCLSpecs.Fulu.BeaconState) := SSZ.FastBox (fuluGenesis knobs)
  let act : EStateM StateTransitionError
      (SSZ.Box Sha256 EthCLSpecs.Fulu.BeaconState) Unit :=
    EthCLSpecs.Fulu.processSlots (UInt64.ofNat knobs.slot)
  match act.run box with
  | .ok _ st => st.view
  | .error _ _ => fuluGenesis knobs

/-- `upgraded`: the parent fork's `advanced` state through the fork's own
`upgradeToGloas`, with the config's fork version, so the fork-specific
fields hold the values the upgrade gives them. The runner's onboarding
step follows the upgrade in the real path; here the queue is empty, so it
is a no-op and the builder skips it. -/
def upgraded [Preset] [Config] [CryptoBackend] (knobs : Knobs) :
    BeaconState :=
  letI : HasherTag := fastHasherTag
  upgradeToGloas Const.gloasForkVersion (fuluAdvanced knobs)

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
    { pubkey := builderPubkeyOf (i / 2)
      withdrawalCredentials := credentialsOf Const.builderWithdrawalPrefix (i / 2)
      amount, signature := default, slot := Const.genesisSlot }
  else
    { pubkey := pubkeyOf (registrySize + i / 2)
      withdrawalCredentials :=
        credentialsOf Const.eth1AddressWithdrawalPrefix (registrySize + i / 2)
      amount, signature := default, slot := Const.genesisSlot }

/-- `withQueue`: `advanced`, plus `knobs.queue` pending deposits appended
and drained through the spec's own `onboardBuildersFromPendingDeposits`,
so the builder registry holds builders the registry's own path put there
and the queue holds what it kept. §9.9's catalog row also lists
withdrawals and builder payments; those queues wait for a theorem that
reads them. The crypto backend is the caller's, as every spec
operation's is; the builders run under whatever backend the binding
fixes, and the deposit signature checks accept under verify-off. -/
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

end EthCLSpecs.TheoremVectors.Builders.Gloas
