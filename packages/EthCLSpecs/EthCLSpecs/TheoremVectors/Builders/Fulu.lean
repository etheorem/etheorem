import EthCLLib.TheoremVectors.Types
import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Fulu.Transition

/-!
# `EthCLSpecs.TheoremVectors.Builders.Fulu`: the Fulu state-builder catalog

The Fulu state-builder catalog of `THEOREM_VECTORS_ARCHITECTURE.md` §9.9, two rows,
cheapest first:

- `genesis`: the fork's genesis state over `validators` deposits of `balance`,
  every validator active. It reproduces the deposit side of the pyspec's
  `create_genesis_state`: the effective balance rounds down to the increment the
  way `get_validator_from_deposit` rounds it, and activation sits at the genesis
  epoch. The fork record carries the chain's genesis fork version on
  both sides; the RANDAO mixes and the genesis block header keep their
  defaults, which is the empty chain's own state of them.
- `advanced`: `genesis`, then `processSlots` to the target slot, so the epoch
  boundaries the target passes run `process_epoch` and the state carries real
  justification, committees, and RANDAO mixes.

The catalog stops at those two rows because Fulu is the base fork. It has no
parent to upgrade from, so §9.9's `upgraded` row has no Fulu analogue, and it
predates the builder registry, so `withQueue` has none either. Gloas's `upgraded`
builds on this catalog's `advanced` through the fork boundary.

This module also owns the index-derived identity layer every fork's catalog
shares: `pubkeyOf` and `credentialsOf` derive a deposit's pubkey and withdrawal
credentials from its index, and `builderPubkeyOf` lifts that above the validator
range. Deposits need pubkeys and credentials. Under the verify-off backend any
48-byte value verifies, so the catalog derives both from the deposit's index.
Builder identities sit above every validator identity, so a builder pubkey never
collides with a validator pubkey. That is what the registry lookups by pubkey
need (`validatorIndexByPubkey?`, the onboarding dedup). A builder that needs a
real signature is outside this catalog (§9.9).

The transitions run at the fast config over `SSZ.FastBox`, the configuration the
pyspec runner runs. A reject falls back to the state the builder started from,
so a builder never fails its vector. The hasher is the binding's
`fastHasherTag`, pinned locally the way the fork interface pins it, so a builder
constant carries only the binders its own body names: `[Preset] [Config]`, plus
`[CryptoBackend]` where the spec's signature checks reach the seam (§9.9's
sketch names `[Preset] [Config]` alone; `IMPLEMENTATION_NOTES.md` records the
deviation).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.TheoremVectors (Knobs)
open EthCLSpecs.Fulu
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.TheoremVectors.Builders.Fulu

/-! ## Index-derived identity -/

/-- The little-endian bytes of `index`, at byte width `w`, the shared
shape of every index-derived identity below. -/
private def indexBytes (w : Nat) (index : Nat) (i : Nat) : UInt8 :=
  if i < w then UInt8.ofNat ((index / 2 ^ (8 * i)) % 256) else 0

/-- The pubkey of the identity at `index`: the index in the first 8
bytes, little-endian, the rest zero. This is the one home the identity
layer has: every fork's builder catalog names these helpers, so two
forks never derive one identity's bytes two ways. -/
def pubkeyOf (index : Nat) : BLSPubkey :=
  Vector.ofFn (fun i : Fin 48 => indexBytes 8 index i.val)

/-- The withdrawal credentials of the identity at `index`: the prefix
byte, then the index in the next 8 bytes, the rest zero. `tag` carries
the prefix because `prefix` is a Lean keyword. Like `pubkeyOf`, this is
the one home every fork's catalog shares. -/
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

/-- `genesis`: the fork's genesis state over `knobs.validators` deposits of
`knobs.balance`, every validator active. The two participation lists and
`inactivityScores` hold one zero entry per validator.
`eth1_data.deposit_count` and `eth1_deposit_index` name the same count
the registry holds. The fork record carries the chain's genesis fork
version on both sides. The pyspec's `create_genesis_state` names the
parent fork's version as the previous one and the fork's own as the
current one; this builder writes the pre-fork record instead, the one
version the chain holds before any upgrade runs. -/
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
      { previousVersion := Const.genesisForkVersion
        currentVersion := Const.genesisForkVersion
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
the builder constant carries only the binders its body names. This is
the row Gloas's `upgraded` builds on, through the fork's `Downgrade`
bridge. -/
def advanced [Preset] [Config] [CryptoBackend] (knobs : Knobs) :
    BeaconState :=
  letI : HasherTag := fastHasherTag
  runState (processSlots (UInt64.ofNat knobs.slot)) (genesis knobs)

end EthCLSpecs.TheoremVectors.Builders.Fulu
