import EthCLSpecs.Heze.Fork

/-!
# `EthCLSpecs.Heze.Types`: consensus type aliases (load order row 1)

Heze's primitive vocabulary, replayed from Gloas's (and through Gloas, Fulu's:
Gloas declared each of these itself, so the lineage walk stops one generation
up). EIP-7805 changes none of them, and the fork still declares all of them, so
`Root` in a Heze signature is `EthCLSpecs.Heze.Root` and the fork's body code
names only its own namespace (`SPEC_AUTHORING_MODEL.md` §8).

`inherit` replays each as an `abbrev`, so reducibility survives and SSZRepr
synthesis still sees through `Root` to `Vector UInt8 32`.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

inherit Slot Epoch ValidatorIndex BuilderIndex
inherit CommitteeIndex WithdrawalIndex Gwei Root
inherit Bytes32 Hash32 Version DomainType
inherit Domain BLSPubkey BLSSignature ExecutionAddress
inherit ParticipationFlags KZGCommitment KZGProof Cell
inherit ColumnIndex CellIndex Transaction

end EthCLSpecs.Heze
