import EthCLSpecs.Fulu.State
import EthCLSpecs.Gloas.State
import EthCLSpecs.Gloas.Block
import EthCLLib.Proofs.ContainerBranch
import SizzLean.Spec.SupportedCheck

/-!
# `EthCLSpecs.Tests.GindexPins`: the spec's generalized indices on our schemas

The light-client and sidecar call sites pass generalized indices the spec writes
as constants, each one `get_generalized_index` over a fork container. These
`#guard`s run `SSZType.generalizedIndex` over our own container shapes and
compare against the value the spec states. A field that moves, or a container
that gains enough fields to change depth, fails the build here.

Values come from the pinned `consensus-specs` (`v1.7.0-alpha.11`):
`electra/light-client/sync-protocol.md:54-56`,
`gloas/light-client/sync-protocol.md:53-55`, and `fulu/p2p-interface.md:60`.
The schemas are preset-independent in field count, so the `mainnet` preset
stands for both.

The branch theorems these gindices feed are `isValidMerkleBranch_of_container_gindex`,
`isValidMerkleBranch_of_container₂_gindex`, and
`isValidMerkleBranch_of_container₃_gindex` (`EthCLLib/Proofs/ContainerBranch.lean`).
Two `example`s apply the two-step and three-step forms to real schemas.

The checks run on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.GindexPins

open SizzLean
open SizzLean.Spec
open SizzLean.Proofs.Merkle
open EthCLLib.Spec
open EthCLLib.Proofs

/-- The field list of a container shape, and `[]` for any other shape. -/
private def fieldsOf : SSZType → List SSZType
  | .container fs => fs
  | _ => []

section Fulu

open EthCLSpecs.Fulu

/-- The Fulu `BeaconState` schema: 38 fields, so the field block is depth 6. -/
private abbrev fuluState : SSZType := SSZRepr.shape (T := @BeaconState mainnet)

/-- The Fulu `BeaconBlockBody` schema: 13 fields, so the field block is depth 4. -/
private abbrev fuluBody : SSZType := SSZRepr.shape (T := @BeaconBlockBody mainnet)

-- `FINALIZED_ROOT_GINDEX_ELECTRA`: `finalized_checkpoint` (field 20), then `root`
-- (field 1 of `Checkpoint`).
#guard fuluState.generalizedIndex [.field 20, .field 1] == some 169
-- `CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA` and `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA`.
#guard fuluState.generalizedIndex [.field 22] == some 86
#guard fuluState.generalizedIndex [.field 23] == some 87
-- `EXECUTION_BLOCK_HASH_GINDEX_DENEB`, stated over `deneb.BeaconBlockBody`. Fulu's
-- body keeps `execution_payload` at field 9 and the depth at 4, and its
-- `ExecutionPayload` keeps `block_hash` at field 12 of 17.
#guard fuluBody.generalizedIndex [.field 9, .field 12] == some 812
-- `KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH` is `floorlog2` of the
-- `blob_kzg_commitments` gindex (field 11).
#guard (fuluBody.generalizedIndex [.field 11]).map Nat.log2 == some 4

-- The `SSZRepr` instances of the nested containers take the preset as an
-- instance. The fork presets are plain definitions, so name `mainnet` here.
attribute [local instance] mainnet

/-- The Fulu `Checkpoint` schema. -/
private abbrev fuluCheckpoint : SSZType := SSZRepr.shape (T := @Checkpoint mainnet)

/-- The two-step theorem at `FINALIZED_ROOT_GINDEX_ELECTRA`, applied to the real
schemas. `decide` proves both `checkSupportedFields` results and both field
bounds. `rfl` proves `hfield`, `hinner`, and the gindex. `hinner` is `rfl`
because the derived `toRepr` of a `BeaconState` puts the `toRepr` of
`finalizedCheckpoint` at field 20. -/
example [HasherTag] [CombineWidth32 HasherTag.H] (s : @BeaconState mainnet) :
    isValidMerkleBranch
        (bytesToRoot (fieldRoot HasherTag.H (fieldsOf fuluCheckpoint)
          (SSZRepr.toRepr s.finalizedCheckpoint) 1))
        ((containerOpening HasherTag.H (fieldsOf fuluState) (SSZRepr.toRepr s) 20
            ++ containerOpening HasherTag.H (fieldsOf fuluCheckpoint)
              (SSZRepr.toRepr s.finalizedCheckpoint) 1).map bytesToRoot).toArray.reverse
        (Nat.log2 169) (169 % 2 ^ Nat.log2 169)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container (fieldsOf fuluState))
          (SSZRepr.toRepr s)))
      = true :=
  isValidMerkleBranch_of_container₂_gindex
    (SSZType.supportedFields_of_checkSupportedFields _ (by decide))
    (SSZType.supportedFields_of_checkSupportedFields _ (by decide))
    (SSZRepr.toRepr s) (SSZRepr.toRepr s.finalizedCheckpoint) 20 1
    (by decide) (by decide) rfl rfl 169 rfl

end Fulu

section Gloas

open EthCLSpecs.Gloas

/-- The Gloas `BeaconState` schema, still inside the depth-6 field block. -/
private abbrev gloasState : SSZType := SSZRepr.shape (T := @BeaconState mainnet)

/-- The Gloas `BeaconBlockBody` schema: 13 fields, depth 4. -/
private abbrev gloasBody : SSZType := SSZRepr.shape (T := @BeaconBlockBody mainnet)

-- The Electra state gindices keep their values: Gloas keeps fields 20 to 23 in place,
-- and stays within 64 fields.
#guard gloasState.generalizedIndex [.field 20, .field 1] == some 169
#guard gloasState.generalizedIndex [.field 22] == some 86
#guard gloasState.generalizedIndex [.field 23] == some 87
-- `EXECUTION_BLOCK_HASH_GINDEX_GLOAS`: `signed_execution_payload_bid` (field 10),
-- `message` (field 0), `parent_block_hash` (field 0).
#guard gloasBody.generalizedIndex [.field 10, .field 0, .field 0] == some 832

attribute [local instance] mainnet

/-- The Gloas `SignedExecutionPayloadBid` schema: `message`, then `signature`. -/
private abbrev gloasSignedBid : SSZType :=
  SSZRepr.shape (T := @SignedExecutionPayloadBid mainnet)

/-- The Gloas `ExecutionPayloadBid` schema. -/
private abbrev gloasBid : SSZType := SSZRepr.shape (T := @ExecutionPayloadBid mainnet)

/-- The three-step theorem at `EXECUTION_BLOCK_HASH_GINDEX_GLOAS`, applied to the
real schemas. `decide` proves the three `checkSupportedFields` results and the
three field bounds. `rfl` proves both `hfield`s, both `hinner`s, and the gindex. -/
example [HasherTag] [CombineWidth32 HasherTag.H] (b : @BeaconBlockBody mainnet) :
    isValidMerkleBranch
        (bytesToRoot (fieldRoot HasherTag.H (fieldsOf gloasBid)
          (SSZRepr.toRepr b.signedExecutionPayloadBid.message) 0))
        ((containerOpening HasherTag.H (fieldsOf gloasBody) (SSZRepr.toRepr b) 10
            ++ containerOpening HasherTag.H (fieldsOf gloasSignedBid)
              (SSZRepr.toRepr b.signedExecutionPayloadBid) 0
            ++ containerOpening HasherTag.H (fieldsOf gloasBid)
              (SSZRepr.toRepr b.signedExecutionPayloadBid.message) 0).map
            bytesToRoot).toArray.reverse
        (Nat.log2 832) (832 % 2 ^ Nat.log2 832)
        (bytesToRoot (SSZType.hashTreeRoot HasherTag.H (.container (fieldsOf gloasBody))
          (SSZRepr.toRepr b)))
      = true :=
  isValidMerkleBranch_of_container₃_gindex
    (SSZType.supportedFields_of_checkSupportedFields _ (by decide))
    (SSZType.supportedFields_of_checkSupportedFields _ (by decide))
    (SSZType.supportedFields_of_checkSupportedFields _ (by decide))
    (SSZRepr.toRepr b) (SSZRepr.toRepr b.signedExecutionPayloadBid)
    (SSZRepr.toRepr b.signedExecutionPayloadBid.message) 10 0 0
    (by decide) (by decide) (by decide) rfl rfl rfl rfl 832 rfl

end Gloas

end EthCLSpecs.Tests.GindexPins
