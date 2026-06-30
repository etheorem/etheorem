import EthCLSpecs.Gloas.State
import EthCLSpecs.Gloas.Block

/-!
# `EthCLSpecs.Gloas.Containers`: the Gloas container re-export root

Gloas is a diff over Fulu (`SPECS_ARCHITECTURE.md` §2, §4.1). This module
re-exports the Gloas container layer so a single `import EthCLSpecs.Gloas.Containers`
brings it all into scope; it holds no declarations of its own. The pieces:

- the `fork Gloas from Fulu` lineage and fork-version values (`Constants`);
- the ePBS containers, one file per container under `Containers/`: the builder
  registry (`Builder`), the payload bid (`PayloadBid`), the builder-payment queue
  (`BuilderPayment`), the EIP-8282 builder requests and the extended
  `ExecutionRequests` (`ExecutionRequests`), the payload-attestation family
  (`PayloadAttestation`), and the revealed payload / envelope (`Execution`);
- the changed `BeaconState` and its boxed view (`State`);
- the ePBS `BeaconBlockBody` / `BeaconBlock` (`Block`).

The unchanged component and operation containers (`Validator`, `Eth1Data`,
`Checkpoint`, `Withdrawal`, the attestation / slashing / deposit / exit families,
`SyncAggregate`, …) are reused from Fulu directly (`open EthCLSpecs.Fulu`); Gloas
redefines only the containers whose shape changed (EIP-8282 makes `ExecutionRequests`
one of them).
-/
