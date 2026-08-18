import EthCLSpecs.Gloas.Fork

/-!
# `EthCLSpecs.Gloas.Types`: consensus type aliases (load order row 1)

Gloas's primitive vocabulary, replayed from Fulu's. EIP-7732 changes none of
these aliases, and the fork still declares all of them: a fork's body code names
its own namespace and the framework, nothing else, so `Root` in a Gloas
signature has to be `EthCLSpecs.Gloas.Root` (`SPEC_AUTHORING_MODEL.md` §8).

`inherit` replays each as an `abbrev`, so reducibility survives and SSZRepr
synthesis still sees through `Root` to `Vector UInt8 32`. Related aliases share a
line; the discipline is one name per entry, not one entry per line.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Gloas

inherit Slot Epoch ValidatorIndex BuilderIndex
inherit CommitteeIndex WithdrawalIndex Gwei Root
inherit Bytes32 Hash32 Version DomainType
inherit Domain BLSPubkey BLSSignature ExecutionAddress
inherit ParticipationFlags KZGCommitment KZGProof Cell
inherit ColumnIndex CellIndex Transaction

end EthCLSpecs.Gloas
