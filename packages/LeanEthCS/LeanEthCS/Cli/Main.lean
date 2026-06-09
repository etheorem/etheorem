import SizzLean.Hasher.Sha256
import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.HashTreeRoot
import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Phase0.Block
import LeanEthCS.Forks.Phase0.State
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Altair.LightClient
import LeanEthCS.Forks.Altair.Block
import LeanEthCS.Forks.Altair.State
import LeanEthCS.Forks.Altair.Inherited
import LeanEthCS.Forks.Bellatrix.Execution
import LeanEthCS.Forks.Bellatrix.Block
import LeanEthCS.Forks.Bellatrix.State
import LeanEthCS.Forks.Bellatrix.Inherited
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Capella.Execution
import LeanEthCS.Forks.Capella.LightClient
import LeanEthCS.Forks.Capella.Block
import LeanEthCS.Forks.Capella.State
import LeanEthCS.Forks.Capella.Inherited
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.Forks.Deneb.Block
import LeanEthCS.Forks.Deneb.State
import LeanEthCS.Forks.Deneb.Blob
import LeanEthCS.Forks.Deneb.LightClient
import LeanEthCS.Forks.Deneb.Inherited
import LeanEthCS.Forks.Electra.PendingOperations
import LeanEthCS.Forks.Electra.Requests
import LeanEthCS.Forks.Electra.Attestation
import LeanEthCS.Forks.Electra.Block
import LeanEthCS.Forks.Electra.State
import LeanEthCS.Forks.Electra.LightClient
import LeanEthCS.Forks.Electra.Inherited
import LeanEthCS.Forks.Fulu.Primitives
import LeanEthCS.Forks.Fulu.DataColumn
import LeanEthCS.Forks.Fulu.Block
import LeanEthCS.Forks.Fulu.State
import LeanEthCS.Forks.Fulu.LightClient
import LeanEthCS.Forks.Fulu.Inherited

/-!
# `LeanEthCS.Cli.Main`: `eth_ssz_vector_runner` driver binary

Pure-Lean driver that the Python `scripts/run_conformance.py`
orchestrator invokes per test case. Its single purpose is to be
driven by the conformance harness, nothing in the library proper
depends on it.
Argv contract:

```
eth_ssz_vector_runner root  <fork>:<type> <input.ssz>
eth_ssz_vector_runner check <fork>:<type> <input.ssz> <expected_root_hex>
```

* `root`: deserialize the SSZ file, compute
  `SSZ.hashTreeRoot` (via the FFI SHA-256 instance), print the
  resulting 32-byte root as lowercase hex to stdout. Exit 0.
* `check`: deserialize, re-serialize (must equal input
  bytes-for-bytes), compute root, compare against the expected
  hex. Exit 0 on success; non-zero with a diagnostic on any
  failure.

The `<fork>:<type>` dispatch is a hand-rolled match table over the
known Lean types. Adding a new consensus type means one more arm in
`runRoot` / `runCheck`. This is *intentional*, the alternative
(reflection-based dispatch) would require carrying SSZType /
SSZRepr metadata at runtime, which conflicts with the kernel-opaque
treatment of `Hasher` and would complicate the trust boundary.

## What types are dispatched

The dispatcher in `runRoot` / `runCheck` enumerates the Phase 0
through Fulu containers exposed by `LeanEthCS.Forks.*`. Adding a
new consensus type means one more arm under the appropriate fork
and, for preset-sensitive types (`BeaconState`, `BeaconBlockBody`,
…), a sub-match on `Preset.Minimal` / `Preset.Mainnet`.

## Hex helpers

The CLI converts a 32-byte `ByteArray` to/from a 64-char hex string
for I/O. Lowercase output (matches consensus-spec-tests's
`roots.yaml` convention).
-/

set_option autoImplicit false

namespace LeanEthCS.Cli

open SizzLean.Repr

open SizzLean.Hasher

open SizzLean
open LeanEthCS
open SizzLean.Spec

/-- Convert a `ByteArray` to a lowercase hex string. -/
private def toHex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char :=
    let v := n.toNat
    if v < 10 then Char.ofNat (v + 48)        -- '0'..'9'
    else Char.ofNat (v - 10 + 97)             -- 'a'..'f'
  let step (acc : String) (byte : UInt8) : String :=
    (acc.push (digit (byte >>> 4))).push (digit (byte &&& 0xf))
  b.foldl step ""

/-- Parse a single hex digit char into `0..15`. Returns `none` on
non-hex input. -/
private def hexDigit (c : Char) : Option UInt8 :=
  let n := c.toNat
  if n ≥ 48 && n ≤ 57 then        some (UInt8.ofNat (n - 48))
  else if n ≥ 97 && n ≤ 102 then  some (UInt8.ofNat (n - 97 + 10))
  else if n ≥ 65 && n ≤ 70 then   some (UInt8.ofNat (n - 65 + 10))
  else                            none

/-- Parse a hex string (must be even length) into a `ByteArray`.
Returns `none` on any non-hex character. -/
private def fromHex (s : String) : Option ByteArray := do
  let cs := s.toList
  if cs.length % 2 ≠ 0 then none
  else
    let rec go : List Char → Option ByteArray
      | []           => some ByteArray.empty
      | _ :: []      => none
      | c1 :: c2 :: rest => do
          let d1 ← hexDigit c1
          let d2 ← hexDigit c2
          let byte := (d1 <<< 4) ||| d2
          let tail ← go rest
          some (ByteArray.empty.push byte ++ tail)
    go cs

/-- Read the entire contents of a file as raw bytes. Wraps
`IO.FS.readBinFile`. -/
private def readFile (path : System.FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

-- BEGIN AUTO-GENERATED DISPATCH (regenerate via `just gen-cli-dispatch`) --

/-- Preset selector parsed from the `<preset>/<fork>:<type>` identifier. -/
private inductive Preset where
  | Minimal
  | Mainnet
  deriving Repr, DecidableEq

private def parseTypeId (typeId : String) : Preset × String :=
  if typeId.startsWith "minimal/" then
    (.Minimal, (typeId.drop "minimal/".length).toString)
  else if typeId.startsWith "mainnet/" then
    (.Mainnet, (typeId.drop "mainnet/".length).toString)
  else
    (.Minimal, typeId)

private def runRoot (T : Type) [SSZRepr T] (raw : ByteArray) :
    Except String String :=
  match SSZ.deserialize (T := T) raw with
  | .ok v   => .ok (toHex (SSZ.hashTreeRoot Sha256 v))
  | .error e => .error s!"deserialize failed: {repr e}"

private def runCheck (T : Type) [SSZRepr T] (raw : ByteArray)
    (expectedRoot : ByteArray) : Except String Unit :=
  match SSZ.deserialize (T := T) raw with
  | .error e => .error s!"deserialize failed: {repr e}"
  | .ok v =>
      let reSerialized := SSZ.serialize v
      if reSerialized ≠ raw then
        .error s!"re-serialize mismatch: serialized {reSerialized.size} bytes, input was {raw.size}"
      else
        let root := SSZ.hashTreeRoot Sha256 v
        if root ≠ expectedRoot then
          .error s!"root mismatch: got {toHex root}, expected {toHex expectedRoot}"
        else .ok ()

private def dispatchRoot_phase0 (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Phase0.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Phase0.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Phase0.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Phase0.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Phase0.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Phase0.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Phase0.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Phase0.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Phase0.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Phase0.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Phase0.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Phase0.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Phase0.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Phase0.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Phase0.Eth1Block) raw)
  | "IndexedAttestation" => some (runRoot (T := LeanEthCS.Forks.Phase0.IndexedAttestation) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Phase0.PendingAttestation) raw)
  | "Attestation" => some (runRoot (T := LeanEthCS.Forks.Phase0.Attestation) raw)
  | "AttesterSlashing" => some (runRoot (T := LeanEthCS.Forks.Phase0.AttesterSlashing) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Phase0.Deposit) raw)
  | "AggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Phase0.AggregateAndProof) raw)
  | "SignedAggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Phase0.SignedAggregateAndProof) raw)
  | "BeaconBlockBody" => some (runRoot (T := LeanEthCS.Forks.Phase0.BeaconBlockBody) raw)
  | "BeaconBlock" => some (runRoot (T := LeanEthCS.Forks.Phase0.BeaconBlock) raw)
  | "SignedBeaconBlock" => some (runRoot (T := LeanEthCS.Forks.Phase0.SignedBeaconBlock) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Phase0.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Phase0.HistoricalBatch.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Phase0.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Phase0.BeaconState.Mainnet) raw)
  | _ => none

private def dispatchRoot_altair (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Altair.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Altair.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Altair.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Altair.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Altair.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Altair.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Altair.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Altair.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Altair.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Altair.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Altair.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Altair.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Altair.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Altair.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Altair.Eth1Block) raw)
  | "IndexedAttestation" => some (runRoot (T := LeanEthCS.Forks.Altair.IndexedAttestation) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Altair.PendingAttestation) raw)
  | "Attestation" => some (runRoot (T := LeanEthCS.Forks.Altair.Attestation) raw)
  | "AttesterSlashing" => some (runRoot (T := LeanEthCS.Forks.Altair.AttesterSlashing) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Altair.Deposit) raw)
  | "AggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Altair.AggregateAndProof) raw)
  | "SignedAggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Altair.SignedAggregateAndProof) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.HistoricalBatch.Mainnet) raw)
  | "SyncCommitteeMessage" => some (runRoot (T := LeanEthCS.Forks.Altair.SyncCommitteeMessage) raw)
  | "SyncAggregatorSelectionData" => some (runRoot (T := LeanEthCS.Forks.Altair.SyncAggregatorSelectionData) raw)
  | "LightClientHeader" => some (runRoot (T := LeanEthCS.Forks.Altair.LightClientHeader) raw)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.SyncAggregate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.SyncAggregate.Mainnet) raw)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.SyncCommittee.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.SyncCommittee.Mainnet) raw)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.SyncCommitteeContribution.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.SyncCommitteeContribution.Mainnet) raw)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.ContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.ContributionAndProof.Mainnet) raw)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.SignedContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.SignedContributionAndProof.Mainnet) raw)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.BeaconBlockBody.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.BeaconBlockBody.Mainnet) raw)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.BeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.BeaconBlock.Mainnet) raw)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.SignedBeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.SignedBeaconBlock.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.BeaconState.Mainnet) raw)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.LightClientBootstrap.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.LightClientBootstrap.Mainnet) raw)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.LightClientUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.LightClientUpdate.Mainnet) raw)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.LightClientFinalityUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.LightClientFinalityUpdate.Mainnet) raw)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Altair.LightClientOptimisticUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Altair.LightClientOptimisticUpdate.Mainnet) raw)
  | _ => none

private def dispatchRoot_bellatrix (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Eth1Block) raw)
  | "IndexedAttestation" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.IndexedAttestation) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.PendingAttestation) raw)
  | "Attestation" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Attestation) raw)
  | "AttesterSlashing" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.AttesterSlashing) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.Deposit) raw)
  | "AggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.AggregateAndProof) raw)
  | "SignedAggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.SignedAggregateAndProof) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.HistoricalBatch.Mainnet) raw)
  | "SyncCommitteeMessage" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.SyncCommitteeMessage) raw)
  | "SyncAggregatorSelectionData" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.SyncAggregatorSelectionData) raw)
  | "LightClientHeader" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientHeader) raw)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.SyncAggregate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.SyncAggregate.Mainnet) raw)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.SyncCommittee.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.SyncCommittee.Mainnet) raw)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.SyncCommitteeContribution.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.SyncCommitteeContribution.Mainnet) raw)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.ContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.ContributionAndProof.Mainnet) raw)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.SignedContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.SignedContributionAndProof.Mainnet) raw)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientBootstrap.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientBootstrap.Mainnet) raw)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientUpdate.Mainnet) raw)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientFinalityUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientFinalityUpdate.Mainnet) raw)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientOptimisticUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.LightClientOptimisticUpdate.Mainnet) raw)
  | "ExecutionPayload" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.ExecutionPayload) raw)
  | "ExecutionPayloadHeader" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.ExecutionPayloadHeader) raw)
  | "PowBlock" => some (runRoot (T := LeanEthCS.Forks.Bellatrix.PowBlock) raw)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconBlockBody.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconBlockBody.Mainnet) raw)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconBlock.Mainnet) raw)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.SignedBeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.SignedBeaconBlock.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Bellatrix.BeaconState.Mainnet) raw)
  | _ => none

private def dispatchRoot_capella (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Capella.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Capella.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Capella.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Capella.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Capella.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Capella.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Capella.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Capella.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Capella.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Capella.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Capella.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Capella.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Capella.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Capella.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Capella.Eth1Block) raw)
  | "IndexedAttestation" => some (runRoot (T := LeanEthCS.Forks.Capella.IndexedAttestation) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Capella.PendingAttestation) raw)
  | "Attestation" => some (runRoot (T := LeanEthCS.Forks.Capella.Attestation) raw)
  | "AttesterSlashing" => some (runRoot (T := LeanEthCS.Forks.Capella.AttesterSlashing) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Capella.Deposit) raw)
  | "AggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Capella.AggregateAndProof) raw)
  | "SignedAggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Capella.SignedAggregateAndProof) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.HistoricalBatch.Mainnet) raw)
  | "SyncCommitteeMessage" => some (runRoot (T := LeanEthCS.Forks.Capella.SyncCommitteeMessage) raw)
  | "SyncAggregatorSelectionData" => some (runRoot (T := LeanEthCS.Forks.Capella.SyncAggregatorSelectionData) raw)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.SyncAggregate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.SyncAggregate.Mainnet) raw)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.SyncCommittee.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.SyncCommittee.Mainnet) raw)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.SyncCommitteeContribution.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.SyncCommitteeContribution.Mainnet) raw)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.ContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.ContributionAndProof.Mainnet) raw)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.SignedContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.SignedContributionAndProof.Mainnet) raw)
  | "PowBlock" => some (runRoot (T := LeanEthCS.Forks.Capella.PowBlock) raw)
  | "Withdrawal" => some (runRoot (T := LeanEthCS.Forks.Capella.Withdrawal) raw)
  | "BLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Capella.BLSToExecutionChange) raw)
  | "SignedBLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Capella.SignedBLSToExecutionChange) raw)
  | "HistoricalSummary" => some (runRoot (T := LeanEthCS.Forks.Capella.HistoricalSummary) raw)
  | "ExecutionPayloadHeader" => some (runRoot (T := LeanEthCS.Forks.Capella.ExecutionPayloadHeader) raw)
  | "LightClientHeader" => some (runRoot (T := LeanEthCS.Forks.Capella.LightClientHeader) raw)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.BeaconBlockBody.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.BeaconBlockBody.Mainnet) raw)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.BeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.BeaconBlock.Mainnet) raw)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.SignedBeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.SignedBeaconBlock.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.BeaconState.Mainnet) raw)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.ExecutionPayload.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.ExecutionPayload.Mainnet) raw)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.LightClientBootstrap.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.LightClientBootstrap.Mainnet) raw)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.LightClientUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.LightClientUpdate.Mainnet) raw)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.LightClientFinalityUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.LightClientFinalityUpdate.Mainnet) raw)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Capella.LightClientOptimisticUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Capella.LightClientOptimisticUpdate.Mainnet) raw)
  | _ => none

private def dispatchRoot_deneb (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Deneb.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Deneb.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Deneb.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Deneb.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Deneb.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Deneb.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Deneb.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Deneb.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Deneb.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Deneb.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Deneb.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Deneb.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Deneb.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Deneb.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Deneb.Eth1Block) raw)
  | "IndexedAttestation" => some (runRoot (T := LeanEthCS.Forks.Deneb.IndexedAttestation) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Deneb.PendingAttestation) raw)
  | "Attestation" => some (runRoot (T := LeanEthCS.Forks.Deneb.Attestation) raw)
  | "AttesterSlashing" => some (runRoot (T := LeanEthCS.Forks.Deneb.AttesterSlashing) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Deneb.Deposit) raw)
  | "AggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Deneb.AggregateAndProof) raw)
  | "SignedAggregateAndProof" => some (runRoot (T := LeanEthCS.Forks.Deneb.SignedAggregateAndProof) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.HistoricalBatch.Mainnet) raw)
  | "SyncCommitteeMessage" => some (runRoot (T := LeanEthCS.Forks.Deneb.SyncCommitteeMessage) raw)
  | "SyncAggregatorSelectionData" => some (runRoot (T := LeanEthCS.Forks.Deneb.SyncAggregatorSelectionData) raw)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.SyncAggregate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.SyncAggregate.Mainnet) raw)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.SyncCommittee.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.SyncCommittee.Mainnet) raw)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.SyncCommitteeContribution.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.SyncCommitteeContribution.Mainnet) raw)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.ContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.ContributionAndProof.Mainnet) raw)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.SignedContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.SignedContributionAndProof.Mainnet) raw)
  | "PowBlock" => some (runRoot (T := LeanEthCS.Forks.Deneb.PowBlock) raw)
  | "Withdrawal" => some (runRoot (T := LeanEthCS.Forks.Deneb.Withdrawal) raw)
  | "BLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Deneb.BLSToExecutionChange) raw)
  | "SignedBLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Deneb.SignedBLSToExecutionChange) raw)
  | "HistoricalSummary" => some (runRoot (T := LeanEthCS.Forks.Deneb.HistoricalSummary) raw)
  | "BlobIdentifier" => some (runRoot (T := LeanEthCS.Forks.Deneb.BlobIdentifier) raw)
  | "ExecutionPayloadHeader" => some (runRoot (T := LeanEthCS.Forks.Deneb.ExecutionPayloadHeader) raw)
  | "LightClientHeader" => some (runRoot (T := LeanEthCS.Forks.Deneb.LightClientHeader) raw)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.BeaconBlockBody.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.BeaconBlockBody.Mainnet) raw)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.BeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.BeaconBlock.Mainnet) raw)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.SignedBeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.SignedBeaconBlock.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.BeaconState.Mainnet) raw)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.ExecutionPayload.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.ExecutionPayload.Mainnet) raw)
  | "BlobSidecar" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.BlobSidecar.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.BlobSidecar.Mainnet) raw)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.LightClientBootstrap.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.LightClientBootstrap.Mainnet) raw)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.LightClientUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.LightClientUpdate.Mainnet) raw)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.LightClientFinalityUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.LightClientFinalityUpdate.Mainnet) raw)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Deneb.LightClientOptimisticUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Deneb.LightClientOptimisticUpdate.Mainnet) raw)
  | _ => none

private def dispatchRoot_electra (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Electra.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Electra.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Electra.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Electra.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Electra.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Electra.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Electra.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Electra.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Electra.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Electra.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Electra.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Electra.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Electra.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Electra.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Electra.Eth1Block) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Electra.PendingAttestation) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Electra.Deposit) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.HistoricalBatch.Mainnet) raw)
  | "SyncCommitteeMessage" => some (runRoot (T := LeanEthCS.Forks.Electra.SyncCommitteeMessage) raw)
  | "SyncAggregatorSelectionData" => some (runRoot (T := LeanEthCS.Forks.Electra.SyncAggregatorSelectionData) raw)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.SyncAggregate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.SyncAggregate.Mainnet) raw)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.SyncCommittee.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.SyncCommittee.Mainnet) raw)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.SyncCommitteeContribution.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.SyncCommitteeContribution.Mainnet) raw)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.ContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.ContributionAndProof.Mainnet) raw)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.SignedContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.SignedContributionAndProof.Mainnet) raw)
  | "PowBlock" => some (runRoot (T := LeanEthCS.Forks.Electra.PowBlock) raw)
  | "Withdrawal" => some (runRoot (T := LeanEthCS.Forks.Electra.Withdrawal) raw)
  | "BLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Electra.BLSToExecutionChange) raw)
  | "SignedBLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Electra.SignedBLSToExecutionChange) raw)
  | "HistoricalSummary" => some (runRoot (T := LeanEthCS.Forks.Electra.HistoricalSummary) raw)
  | "BlobIdentifier" => some (runRoot (T := LeanEthCS.Forks.Electra.BlobIdentifier) raw)
  | "ExecutionPayloadHeader" => some (runRoot (T := LeanEthCS.Forks.Electra.ExecutionPayloadHeader) raw)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.ExecutionPayload.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.ExecutionPayload.Mainnet) raw)
  | "BlobSidecar" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.BlobSidecar.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.BlobSidecar.Mainnet) raw)
  | "PendingDeposit" => some (runRoot (T := LeanEthCS.Forks.Electra.PendingDeposit) raw)
  | "PendingPartialWithdrawal" => some (runRoot (T := LeanEthCS.Forks.Electra.PendingPartialWithdrawal) raw)
  | "PendingConsolidation" => some (runRoot (T := LeanEthCS.Forks.Electra.PendingConsolidation) raw)
  | "DepositRequest" => some (runRoot (T := LeanEthCS.Forks.Electra.DepositRequest) raw)
  | "WithdrawalRequest" => some (runRoot (T := LeanEthCS.Forks.Electra.WithdrawalRequest) raw)
  | "ConsolidationRequest" => some (runRoot (T := LeanEthCS.Forks.Electra.ConsolidationRequest) raw)
  | "ExecutionRequests" => some (runRoot (T := LeanEthCS.Forks.Electra.ExecutionRequests) raw)
  | "SingleAttestation" => some (runRoot (T := LeanEthCS.Forks.Electra.SingleAttestation) raw)
  | "LightClientHeader" => some (runRoot (T := LeanEthCS.Forks.Electra.LightClientHeader) raw)
  | "Attestation" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.Attestation.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.Attestation.Mainnet) raw)
  | "IndexedAttestation" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.IndexedAttestation.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.IndexedAttestation.Mainnet) raw)
  | "AttesterSlashing" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.AttesterSlashing.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.AttesterSlashing.Mainnet) raw)
  | "AggregateAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.AggregateAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.AggregateAndProof.Mainnet) raw)
  | "SignedAggregateAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.SignedAggregateAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.SignedAggregateAndProof.Mainnet) raw)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.BeaconBlockBody.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.BeaconBlockBody.Mainnet) raw)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.BeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.BeaconBlock.Mainnet) raw)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.SignedBeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.SignedBeaconBlock.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.BeaconState.Mainnet) raw)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.LightClientBootstrap.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.LightClientBootstrap.Mainnet) raw)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.LightClientUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.LightClientUpdate.Mainnet) raw)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.LightClientFinalityUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.LightClientFinalityUpdate.Mainnet) raw)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Electra.LightClientOptimisticUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Electra.LightClientOptimisticUpdate.Mainnet) raw)
  | _ => none

private def dispatchRoot_fulu (preset : Preset) (suffix : String) (raw : ByteArray) : Option (Except String String) :=
  match suffix with
  | "BeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Fulu.BeaconBlockHeader) raw)
  | "Validator" => some (runRoot (T := LeanEthCS.Forks.Fulu.Validator) raw)
  | "Fork" => some (runRoot (T := LeanEthCS.Forks.Fulu.Fork) raw)
  | "Checkpoint" => some (runRoot (T := LeanEthCS.Forks.Fulu.Checkpoint) raw)
  | "AttestationData" => some (runRoot (T := LeanEthCS.Forks.Fulu.AttestationData) raw)
  | "DepositMessage" => some (runRoot (T := LeanEthCS.Forks.Fulu.DepositMessage) raw)
  | "DepositData" => some (runRoot (T := LeanEthCS.Forks.Fulu.DepositData) raw)
  | "VoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Fulu.VoluntaryExit) raw)
  | "SignedVoluntaryExit" => some (runRoot (T := LeanEthCS.Forks.Fulu.SignedVoluntaryExit) raw)
  | "SignedBeaconBlockHeader" => some (runRoot (T := LeanEthCS.Forks.Fulu.SignedBeaconBlockHeader) raw)
  | "ProposerSlashing" => some (runRoot (T := LeanEthCS.Forks.Fulu.ProposerSlashing) raw)
  | "Eth1Data" => some (runRoot (T := LeanEthCS.Forks.Fulu.Eth1Data) raw)
  | "ForkData" => some (runRoot (T := LeanEthCS.Forks.Fulu.ForkData) raw)
  | "SigningData" => some (runRoot (T := LeanEthCS.Forks.Fulu.SigningData) raw)
  | "Eth1Block" => some (runRoot (T := LeanEthCS.Forks.Fulu.Eth1Block) raw)
  | "PendingAttestation" => some (runRoot (T := LeanEthCS.Forks.Fulu.PendingAttestation) raw)
  | "Deposit" => some (runRoot (T := LeanEthCS.Forks.Fulu.Deposit) raw)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.HistoricalBatch.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.HistoricalBatch.Mainnet) raw)
  | "SyncCommitteeMessage" => some (runRoot (T := LeanEthCS.Forks.Fulu.SyncCommitteeMessage) raw)
  | "SyncAggregatorSelectionData" => some (runRoot (T := LeanEthCS.Forks.Fulu.SyncAggregatorSelectionData) raw)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.SyncAggregate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.SyncAggregate.Mainnet) raw)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.SyncCommittee.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.SyncCommittee.Mainnet) raw)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.SyncCommitteeContribution.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.SyncCommitteeContribution.Mainnet) raw)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.ContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.ContributionAndProof.Mainnet) raw)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.SignedContributionAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.SignedContributionAndProof.Mainnet) raw)
  | "PowBlock" => some (runRoot (T := LeanEthCS.Forks.Fulu.PowBlock) raw)
  | "Withdrawal" => some (runRoot (T := LeanEthCS.Forks.Fulu.Withdrawal) raw)
  | "BLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Fulu.BLSToExecutionChange) raw)
  | "SignedBLSToExecutionChange" => some (runRoot (T := LeanEthCS.Forks.Fulu.SignedBLSToExecutionChange) raw)
  | "HistoricalSummary" => some (runRoot (T := LeanEthCS.Forks.Fulu.HistoricalSummary) raw)
  | "BlobIdentifier" => some (runRoot (T := LeanEthCS.Forks.Fulu.BlobIdentifier) raw)
  | "ExecutionPayloadHeader" => some (runRoot (T := LeanEthCS.Forks.Fulu.ExecutionPayloadHeader) raw)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.ExecutionPayload.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.ExecutionPayload.Mainnet) raw)
  | "BlobSidecar" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.BlobSidecar.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.BlobSidecar.Mainnet) raw)
  | "PendingDeposit" => some (runRoot (T := LeanEthCS.Forks.Fulu.PendingDeposit) raw)
  | "PendingPartialWithdrawal" => some (runRoot (T := LeanEthCS.Forks.Fulu.PendingPartialWithdrawal) raw)
  | "PendingConsolidation" => some (runRoot (T := LeanEthCS.Forks.Fulu.PendingConsolidation) raw)
  | "DepositRequest" => some (runRoot (T := LeanEthCS.Forks.Fulu.DepositRequest) raw)
  | "WithdrawalRequest" => some (runRoot (T := LeanEthCS.Forks.Fulu.WithdrawalRequest) raw)
  | "ConsolidationRequest" => some (runRoot (T := LeanEthCS.Forks.Fulu.ConsolidationRequest) raw)
  | "ExecutionRequests" => some (runRoot (T := LeanEthCS.Forks.Fulu.ExecutionRequests) raw)
  | "SingleAttestation" => some (runRoot (T := LeanEthCS.Forks.Fulu.SingleAttestation) raw)
  | "Attestation" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.Attestation.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.Attestation.Mainnet) raw)
  | "IndexedAttestation" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.IndexedAttestation.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.IndexedAttestation.Mainnet) raw)
  | "AttesterSlashing" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.AttesterSlashing.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.AttesterSlashing.Mainnet) raw)
  | "AggregateAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.AggregateAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.AggregateAndProof.Mainnet) raw)
  | "SignedAggregateAndProof" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.SignedAggregateAndProof.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.SignedAggregateAndProof.Mainnet) raw)
  | "MatrixEntry" => some (runRoot (T := LeanEthCS.Forks.Fulu.MatrixEntry) raw)
  | "DataColumnsByRootIdentifier" => some (runRoot (T := LeanEthCS.Forks.Fulu.DataColumnsByRootIdentifier) raw)
  | "LightClientHeader" => some (runRoot (T := LeanEthCS.Forks.Fulu.LightClientHeader) raw)
  | "DataColumnSidecar" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.DataColumnSidecar.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.DataColumnSidecar.Mainnet) raw)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.BeaconBlockBody.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.BeaconBlockBody.Mainnet) raw)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.BeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.BeaconBlock.Mainnet) raw)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.SignedBeaconBlock.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.SignedBeaconBlock.Mainnet) raw)
  | "BeaconState" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.BeaconState.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.BeaconState.Mainnet) raw)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.LightClientBootstrap.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.LightClientBootstrap.Mainnet) raw)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.LightClientUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.LightClientUpdate.Mainnet) raw)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.LightClientFinalityUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.LightClientFinalityUpdate.Mainnet) raw)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runRoot (T := LeanEthCS.Forks.Fulu.LightClientOptimisticUpdate.Minimal) raw
      | .Mainnet => runRoot (T := LeanEthCS.Forks.Fulu.LightClientOptimisticUpdate.Mainnet) raw)
  | _ => none

private def dispatchRoot (typeId : String) (raw : ByteArray)
    : Except String String :=
  let (preset, key) := parseTypeId typeId
  match key.splitOn ":" with
  | [fork, suffix] =>
    match fork with
    | "phase0" =>
        (dispatchRoot_phase0 preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | "altair" =>
        (dispatchRoot_altair preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | "bellatrix" =>
        (dispatchRoot_bellatrix preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | "capella" =>
        (dispatchRoot_capella preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | "deneb" =>
        (dispatchRoot_deneb preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | "electra" =>
        (dispatchRoot_electra preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | "fulu" =>
        (dispatchRoot_fulu preset suffix raw).getD
          (.error s!"unknown type identifier: {typeId}")
    | _ => .error s!"unknown type identifier: {typeId}"
  | _ => .error s!"unknown type identifier: {typeId}"

private def dispatchCheck_phase0 (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Phase0.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Phase0.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Phase0.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Phase0.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Phase0.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Phase0.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Phase0.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Phase0.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Phase0.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Phase0.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Phase0.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Phase0.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Phase0.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Phase0.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Phase0.Eth1Block) raw expected)
  | "IndexedAttestation" => some (runCheck (T := LeanEthCS.Forks.Phase0.IndexedAttestation) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Phase0.PendingAttestation) raw expected)
  | "Attestation" => some (runCheck (T := LeanEthCS.Forks.Phase0.Attestation) raw expected)
  | "AttesterSlashing" => some (runCheck (T := LeanEthCS.Forks.Phase0.AttesterSlashing) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Phase0.Deposit) raw expected)
  | "AggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Phase0.AggregateAndProof) raw expected)
  | "SignedAggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Phase0.SignedAggregateAndProof) raw expected)
  | "BeaconBlockBody" => some (runCheck (T := LeanEthCS.Forks.Phase0.BeaconBlockBody) raw expected)
  | "BeaconBlock" => some (runCheck (T := LeanEthCS.Forks.Phase0.BeaconBlock) raw expected)
  | "SignedBeaconBlock" => some (runCheck (T := LeanEthCS.Forks.Phase0.SignedBeaconBlock) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Phase0.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Phase0.HistoricalBatch.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Phase0.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Phase0.BeaconState.Mainnet) raw expected)
  | _ => none

private def dispatchCheck_altair (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Altair.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Altair.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Altair.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Altair.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Altair.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Altair.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Altair.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Altair.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Altair.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Altair.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Altair.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Altair.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Altair.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Altair.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Altair.Eth1Block) raw expected)
  | "IndexedAttestation" => some (runCheck (T := LeanEthCS.Forks.Altair.IndexedAttestation) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Altair.PendingAttestation) raw expected)
  | "Attestation" => some (runCheck (T := LeanEthCS.Forks.Altair.Attestation) raw expected)
  | "AttesterSlashing" => some (runCheck (T := LeanEthCS.Forks.Altair.AttesterSlashing) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Altair.Deposit) raw expected)
  | "AggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Altair.AggregateAndProof) raw expected)
  | "SignedAggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Altair.SignedAggregateAndProof) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.HistoricalBatch.Mainnet) raw expected)
  | "SyncCommitteeMessage" => some (runCheck (T := LeanEthCS.Forks.Altair.SyncCommitteeMessage) raw expected)
  | "SyncAggregatorSelectionData" => some (runCheck (T := LeanEthCS.Forks.Altair.SyncAggregatorSelectionData) raw expected)
  | "LightClientHeader" => some (runCheck (T := LeanEthCS.Forks.Altair.LightClientHeader) raw expected)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.SyncAggregate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.SyncAggregate.Mainnet) raw expected)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.SyncCommittee.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.SyncCommittee.Mainnet) raw expected)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.SyncCommitteeContribution.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.SyncCommitteeContribution.Mainnet) raw expected)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.ContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.ContributionAndProof.Mainnet) raw expected)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.SignedContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.SignedContributionAndProof.Mainnet) raw expected)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.BeaconBlockBody.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.BeaconBlockBody.Mainnet) raw expected)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.BeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.BeaconBlock.Mainnet) raw expected)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.SignedBeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.SignedBeaconBlock.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.BeaconState.Mainnet) raw expected)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.LightClientBootstrap.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.LightClientBootstrap.Mainnet) raw expected)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.LightClientUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.LightClientUpdate.Mainnet) raw expected)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.LightClientFinalityUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.LightClientFinalityUpdate.Mainnet) raw expected)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Altair.LightClientOptimisticUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Altair.LightClientOptimisticUpdate.Mainnet) raw expected)
  | _ => none

private def dispatchCheck_bellatrix (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Eth1Block) raw expected)
  | "IndexedAttestation" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.IndexedAttestation) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.PendingAttestation) raw expected)
  | "Attestation" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Attestation) raw expected)
  | "AttesterSlashing" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.AttesterSlashing) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.Deposit) raw expected)
  | "AggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.AggregateAndProof) raw expected)
  | "SignedAggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.SignedAggregateAndProof) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.HistoricalBatch.Mainnet) raw expected)
  | "SyncCommitteeMessage" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.SyncCommitteeMessage) raw expected)
  | "SyncAggregatorSelectionData" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.SyncAggregatorSelectionData) raw expected)
  | "LightClientHeader" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientHeader) raw expected)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.SyncAggregate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.SyncAggregate.Mainnet) raw expected)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.SyncCommittee.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.SyncCommittee.Mainnet) raw expected)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.SyncCommitteeContribution.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.SyncCommitteeContribution.Mainnet) raw expected)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.ContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.ContributionAndProof.Mainnet) raw expected)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.SignedContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.SignedContributionAndProof.Mainnet) raw expected)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientBootstrap.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientBootstrap.Mainnet) raw expected)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientUpdate.Mainnet) raw expected)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientFinalityUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientFinalityUpdate.Mainnet) raw expected)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientOptimisticUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.LightClientOptimisticUpdate.Mainnet) raw expected)
  | "ExecutionPayload" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.ExecutionPayload) raw expected)
  | "ExecutionPayloadHeader" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.ExecutionPayloadHeader) raw expected)
  | "PowBlock" => some (runCheck (T := LeanEthCS.Forks.Bellatrix.PowBlock) raw expected)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconBlockBody.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconBlockBody.Mainnet) raw expected)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconBlock.Mainnet) raw expected)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.SignedBeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.SignedBeaconBlock.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Bellatrix.BeaconState.Mainnet) raw expected)
  | _ => none

private def dispatchCheck_capella (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Capella.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Capella.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Capella.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Capella.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Capella.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Capella.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Capella.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Capella.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Capella.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Capella.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Capella.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Capella.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Capella.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Capella.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Capella.Eth1Block) raw expected)
  | "IndexedAttestation" => some (runCheck (T := LeanEthCS.Forks.Capella.IndexedAttestation) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Capella.PendingAttestation) raw expected)
  | "Attestation" => some (runCheck (T := LeanEthCS.Forks.Capella.Attestation) raw expected)
  | "AttesterSlashing" => some (runCheck (T := LeanEthCS.Forks.Capella.AttesterSlashing) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Capella.Deposit) raw expected)
  | "AggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Capella.AggregateAndProof) raw expected)
  | "SignedAggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Capella.SignedAggregateAndProof) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.HistoricalBatch.Mainnet) raw expected)
  | "SyncCommitteeMessage" => some (runCheck (T := LeanEthCS.Forks.Capella.SyncCommitteeMessage) raw expected)
  | "SyncAggregatorSelectionData" => some (runCheck (T := LeanEthCS.Forks.Capella.SyncAggregatorSelectionData) raw expected)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.SyncAggregate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.SyncAggregate.Mainnet) raw expected)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.SyncCommittee.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.SyncCommittee.Mainnet) raw expected)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.SyncCommitteeContribution.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.SyncCommitteeContribution.Mainnet) raw expected)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.ContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.ContributionAndProof.Mainnet) raw expected)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.SignedContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.SignedContributionAndProof.Mainnet) raw expected)
  | "PowBlock" => some (runCheck (T := LeanEthCS.Forks.Capella.PowBlock) raw expected)
  | "Withdrawal" => some (runCheck (T := LeanEthCS.Forks.Capella.Withdrawal) raw expected)
  | "BLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Capella.BLSToExecutionChange) raw expected)
  | "SignedBLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Capella.SignedBLSToExecutionChange) raw expected)
  | "HistoricalSummary" => some (runCheck (T := LeanEthCS.Forks.Capella.HistoricalSummary) raw expected)
  | "ExecutionPayloadHeader" => some (runCheck (T := LeanEthCS.Forks.Capella.ExecutionPayloadHeader) raw expected)
  | "LightClientHeader" => some (runCheck (T := LeanEthCS.Forks.Capella.LightClientHeader) raw expected)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.BeaconBlockBody.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.BeaconBlockBody.Mainnet) raw expected)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.BeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.BeaconBlock.Mainnet) raw expected)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.SignedBeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.SignedBeaconBlock.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.BeaconState.Mainnet) raw expected)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.ExecutionPayload.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.ExecutionPayload.Mainnet) raw expected)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.LightClientBootstrap.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.LightClientBootstrap.Mainnet) raw expected)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.LightClientUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.LightClientUpdate.Mainnet) raw expected)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.LightClientFinalityUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.LightClientFinalityUpdate.Mainnet) raw expected)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Capella.LightClientOptimisticUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Capella.LightClientOptimisticUpdate.Mainnet) raw expected)
  | _ => none

private def dispatchCheck_deneb (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Deneb.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Deneb.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Deneb.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Deneb.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Deneb.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Deneb.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Deneb.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Deneb.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Deneb.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Deneb.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Deneb.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Deneb.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Deneb.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Deneb.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Deneb.Eth1Block) raw expected)
  | "IndexedAttestation" => some (runCheck (T := LeanEthCS.Forks.Deneb.IndexedAttestation) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Deneb.PendingAttestation) raw expected)
  | "Attestation" => some (runCheck (T := LeanEthCS.Forks.Deneb.Attestation) raw expected)
  | "AttesterSlashing" => some (runCheck (T := LeanEthCS.Forks.Deneb.AttesterSlashing) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Deneb.Deposit) raw expected)
  | "AggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Deneb.AggregateAndProof) raw expected)
  | "SignedAggregateAndProof" => some (runCheck (T := LeanEthCS.Forks.Deneb.SignedAggregateAndProof) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.HistoricalBatch.Mainnet) raw expected)
  | "SyncCommitteeMessage" => some (runCheck (T := LeanEthCS.Forks.Deneb.SyncCommitteeMessage) raw expected)
  | "SyncAggregatorSelectionData" => some (runCheck (T := LeanEthCS.Forks.Deneb.SyncAggregatorSelectionData) raw expected)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.SyncAggregate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.SyncAggregate.Mainnet) raw expected)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.SyncCommittee.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.SyncCommittee.Mainnet) raw expected)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.SyncCommitteeContribution.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.SyncCommitteeContribution.Mainnet) raw expected)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.ContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.ContributionAndProof.Mainnet) raw expected)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.SignedContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.SignedContributionAndProof.Mainnet) raw expected)
  | "PowBlock" => some (runCheck (T := LeanEthCS.Forks.Deneb.PowBlock) raw expected)
  | "Withdrawal" => some (runCheck (T := LeanEthCS.Forks.Deneb.Withdrawal) raw expected)
  | "BLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Deneb.BLSToExecutionChange) raw expected)
  | "SignedBLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Deneb.SignedBLSToExecutionChange) raw expected)
  | "HistoricalSummary" => some (runCheck (T := LeanEthCS.Forks.Deneb.HistoricalSummary) raw expected)
  | "BlobIdentifier" => some (runCheck (T := LeanEthCS.Forks.Deneb.BlobIdentifier) raw expected)
  | "ExecutionPayloadHeader" => some (runCheck (T := LeanEthCS.Forks.Deneb.ExecutionPayloadHeader) raw expected)
  | "LightClientHeader" => some (runCheck (T := LeanEthCS.Forks.Deneb.LightClientHeader) raw expected)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.BeaconBlockBody.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.BeaconBlockBody.Mainnet) raw expected)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.BeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.BeaconBlock.Mainnet) raw expected)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.SignedBeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.SignedBeaconBlock.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.BeaconState.Mainnet) raw expected)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.ExecutionPayload.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.ExecutionPayload.Mainnet) raw expected)
  | "BlobSidecar" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.BlobSidecar.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.BlobSidecar.Mainnet) raw expected)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.LightClientBootstrap.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.LightClientBootstrap.Mainnet) raw expected)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.LightClientUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.LightClientUpdate.Mainnet) raw expected)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.LightClientFinalityUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.LightClientFinalityUpdate.Mainnet) raw expected)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Deneb.LightClientOptimisticUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Deneb.LightClientOptimisticUpdate.Mainnet) raw expected)
  | _ => none

private def dispatchCheck_electra (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Electra.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Electra.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Electra.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Electra.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Electra.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Electra.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Electra.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Electra.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Electra.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Electra.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Electra.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Electra.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Electra.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Electra.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Electra.Eth1Block) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Electra.PendingAttestation) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Electra.Deposit) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.HistoricalBatch.Mainnet) raw expected)
  | "SyncCommitteeMessage" => some (runCheck (T := LeanEthCS.Forks.Electra.SyncCommitteeMessage) raw expected)
  | "SyncAggregatorSelectionData" => some (runCheck (T := LeanEthCS.Forks.Electra.SyncAggregatorSelectionData) raw expected)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.SyncAggregate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.SyncAggregate.Mainnet) raw expected)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.SyncCommittee.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.SyncCommittee.Mainnet) raw expected)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.SyncCommitteeContribution.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.SyncCommitteeContribution.Mainnet) raw expected)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.ContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.ContributionAndProof.Mainnet) raw expected)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.SignedContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.SignedContributionAndProof.Mainnet) raw expected)
  | "PowBlock" => some (runCheck (T := LeanEthCS.Forks.Electra.PowBlock) raw expected)
  | "Withdrawal" => some (runCheck (T := LeanEthCS.Forks.Electra.Withdrawal) raw expected)
  | "BLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Electra.BLSToExecutionChange) raw expected)
  | "SignedBLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Electra.SignedBLSToExecutionChange) raw expected)
  | "HistoricalSummary" => some (runCheck (T := LeanEthCS.Forks.Electra.HistoricalSummary) raw expected)
  | "BlobIdentifier" => some (runCheck (T := LeanEthCS.Forks.Electra.BlobIdentifier) raw expected)
  | "ExecutionPayloadHeader" => some (runCheck (T := LeanEthCS.Forks.Electra.ExecutionPayloadHeader) raw expected)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.ExecutionPayload.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.ExecutionPayload.Mainnet) raw expected)
  | "BlobSidecar" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.BlobSidecar.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.BlobSidecar.Mainnet) raw expected)
  | "PendingDeposit" => some (runCheck (T := LeanEthCS.Forks.Electra.PendingDeposit) raw expected)
  | "PendingPartialWithdrawal" => some (runCheck (T := LeanEthCS.Forks.Electra.PendingPartialWithdrawal) raw expected)
  | "PendingConsolidation" => some (runCheck (T := LeanEthCS.Forks.Electra.PendingConsolidation) raw expected)
  | "DepositRequest" => some (runCheck (T := LeanEthCS.Forks.Electra.DepositRequest) raw expected)
  | "WithdrawalRequest" => some (runCheck (T := LeanEthCS.Forks.Electra.WithdrawalRequest) raw expected)
  | "ConsolidationRequest" => some (runCheck (T := LeanEthCS.Forks.Electra.ConsolidationRequest) raw expected)
  | "ExecutionRequests" => some (runCheck (T := LeanEthCS.Forks.Electra.ExecutionRequests) raw expected)
  | "SingleAttestation" => some (runCheck (T := LeanEthCS.Forks.Electra.SingleAttestation) raw expected)
  | "LightClientHeader" => some (runCheck (T := LeanEthCS.Forks.Electra.LightClientHeader) raw expected)
  | "Attestation" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.Attestation.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.Attestation.Mainnet) raw expected)
  | "IndexedAttestation" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.IndexedAttestation.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.IndexedAttestation.Mainnet) raw expected)
  | "AttesterSlashing" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.AttesterSlashing.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.AttesterSlashing.Mainnet) raw expected)
  | "AggregateAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.AggregateAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.AggregateAndProof.Mainnet) raw expected)
  | "SignedAggregateAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.SignedAggregateAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.SignedAggregateAndProof.Mainnet) raw expected)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.BeaconBlockBody.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.BeaconBlockBody.Mainnet) raw expected)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.BeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.BeaconBlock.Mainnet) raw expected)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.SignedBeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.SignedBeaconBlock.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.BeaconState.Mainnet) raw expected)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.LightClientBootstrap.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.LightClientBootstrap.Mainnet) raw expected)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.LightClientUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.LightClientUpdate.Mainnet) raw expected)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.LightClientFinalityUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.LightClientFinalityUpdate.Mainnet) raw expected)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Electra.LightClientOptimisticUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Electra.LightClientOptimisticUpdate.Mainnet) raw expected)
  | _ => none

private def dispatchCheck_fulu (preset : Preset) (suffix : String) (raw : ByteArray) (expected : ByteArray) : Option (Except String Unit) :=
  match suffix with
  | "BeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Fulu.BeaconBlockHeader) raw expected)
  | "Validator" => some (runCheck (T := LeanEthCS.Forks.Fulu.Validator) raw expected)
  | "Fork" => some (runCheck (T := LeanEthCS.Forks.Fulu.Fork) raw expected)
  | "Checkpoint" => some (runCheck (T := LeanEthCS.Forks.Fulu.Checkpoint) raw expected)
  | "AttestationData" => some (runCheck (T := LeanEthCS.Forks.Fulu.AttestationData) raw expected)
  | "DepositMessage" => some (runCheck (T := LeanEthCS.Forks.Fulu.DepositMessage) raw expected)
  | "DepositData" => some (runCheck (T := LeanEthCS.Forks.Fulu.DepositData) raw expected)
  | "VoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Fulu.VoluntaryExit) raw expected)
  | "SignedVoluntaryExit" => some (runCheck (T := LeanEthCS.Forks.Fulu.SignedVoluntaryExit) raw expected)
  | "SignedBeaconBlockHeader" => some (runCheck (T := LeanEthCS.Forks.Fulu.SignedBeaconBlockHeader) raw expected)
  | "ProposerSlashing" => some (runCheck (T := LeanEthCS.Forks.Fulu.ProposerSlashing) raw expected)
  | "Eth1Data" => some (runCheck (T := LeanEthCS.Forks.Fulu.Eth1Data) raw expected)
  | "ForkData" => some (runCheck (T := LeanEthCS.Forks.Fulu.ForkData) raw expected)
  | "SigningData" => some (runCheck (T := LeanEthCS.Forks.Fulu.SigningData) raw expected)
  | "Eth1Block" => some (runCheck (T := LeanEthCS.Forks.Fulu.Eth1Block) raw expected)
  | "PendingAttestation" => some (runCheck (T := LeanEthCS.Forks.Fulu.PendingAttestation) raw expected)
  | "Deposit" => some (runCheck (T := LeanEthCS.Forks.Fulu.Deposit) raw expected)
  | "HistoricalBatch" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.HistoricalBatch.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.HistoricalBatch.Mainnet) raw expected)
  | "SyncCommitteeMessage" => some (runCheck (T := LeanEthCS.Forks.Fulu.SyncCommitteeMessage) raw expected)
  | "SyncAggregatorSelectionData" => some (runCheck (T := LeanEthCS.Forks.Fulu.SyncAggregatorSelectionData) raw expected)
  | "SyncAggregate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.SyncAggregate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.SyncAggregate.Mainnet) raw expected)
  | "SyncCommittee" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.SyncCommittee.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.SyncCommittee.Mainnet) raw expected)
  | "SyncCommitteeContribution" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.SyncCommitteeContribution.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.SyncCommitteeContribution.Mainnet) raw expected)
  | "ContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.ContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.ContributionAndProof.Mainnet) raw expected)
  | "SignedContributionAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.SignedContributionAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.SignedContributionAndProof.Mainnet) raw expected)
  | "PowBlock" => some (runCheck (T := LeanEthCS.Forks.Fulu.PowBlock) raw expected)
  | "Withdrawal" => some (runCheck (T := LeanEthCS.Forks.Fulu.Withdrawal) raw expected)
  | "BLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Fulu.BLSToExecutionChange) raw expected)
  | "SignedBLSToExecutionChange" => some (runCheck (T := LeanEthCS.Forks.Fulu.SignedBLSToExecutionChange) raw expected)
  | "HistoricalSummary" => some (runCheck (T := LeanEthCS.Forks.Fulu.HistoricalSummary) raw expected)
  | "BlobIdentifier" => some (runCheck (T := LeanEthCS.Forks.Fulu.BlobIdentifier) raw expected)
  | "ExecutionPayloadHeader" => some (runCheck (T := LeanEthCS.Forks.Fulu.ExecutionPayloadHeader) raw expected)
  | "ExecutionPayload" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.ExecutionPayload.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.ExecutionPayload.Mainnet) raw expected)
  | "BlobSidecar" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.BlobSidecar.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.BlobSidecar.Mainnet) raw expected)
  | "PendingDeposit" => some (runCheck (T := LeanEthCS.Forks.Fulu.PendingDeposit) raw expected)
  | "PendingPartialWithdrawal" => some (runCheck (T := LeanEthCS.Forks.Fulu.PendingPartialWithdrawal) raw expected)
  | "PendingConsolidation" => some (runCheck (T := LeanEthCS.Forks.Fulu.PendingConsolidation) raw expected)
  | "DepositRequest" => some (runCheck (T := LeanEthCS.Forks.Fulu.DepositRequest) raw expected)
  | "WithdrawalRequest" => some (runCheck (T := LeanEthCS.Forks.Fulu.WithdrawalRequest) raw expected)
  | "ConsolidationRequest" => some (runCheck (T := LeanEthCS.Forks.Fulu.ConsolidationRequest) raw expected)
  | "ExecutionRequests" => some (runCheck (T := LeanEthCS.Forks.Fulu.ExecutionRequests) raw expected)
  | "SingleAttestation" => some (runCheck (T := LeanEthCS.Forks.Fulu.SingleAttestation) raw expected)
  | "Attestation" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.Attestation.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.Attestation.Mainnet) raw expected)
  | "IndexedAttestation" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.IndexedAttestation.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.IndexedAttestation.Mainnet) raw expected)
  | "AttesterSlashing" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.AttesterSlashing.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.AttesterSlashing.Mainnet) raw expected)
  | "AggregateAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.AggregateAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.AggregateAndProof.Mainnet) raw expected)
  | "SignedAggregateAndProof" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.SignedAggregateAndProof.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.SignedAggregateAndProof.Mainnet) raw expected)
  | "MatrixEntry" => some (runCheck (T := LeanEthCS.Forks.Fulu.MatrixEntry) raw expected)
  | "DataColumnsByRootIdentifier" => some (runCheck (T := LeanEthCS.Forks.Fulu.DataColumnsByRootIdentifier) raw expected)
  | "LightClientHeader" => some (runCheck (T := LeanEthCS.Forks.Fulu.LightClientHeader) raw expected)
  | "DataColumnSidecar" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.DataColumnSidecar.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.DataColumnSidecar.Mainnet) raw expected)
  | "BeaconBlockBody" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.BeaconBlockBody.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.BeaconBlockBody.Mainnet) raw expected)
  | "BeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.BeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.BeaconBlock.Mainnet) raw expected)
  | "SignedBeaconBlock" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.SignedBeaconBlock.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.SignedBeaconBlock.Mainnet) raw expected)
  | "BeaconState" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.BeaconState.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.BeaconState.Mainnet) raw expected)
  | "LightClientBootstrap" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.LightClientBootstrap.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.LightClientBootstrap.Mainnet) raw expected)
  | "LightClientUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.LightClientUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.LightClientUpdate.Mainnet) raw expected)
  | "LightClientFinalityUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.LightClientFinalityUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.LightClientFinalityUpdate.Mainnet) raw expected)
  | "LightClientOptimisticUpdate" => some (match preset with
      | .Minimal => runCheck (T := LeanEthCS.Forks.Fulu.LightClientOptimisticUpdate.Minimal) raw expected
      | .Mainnet => runCheck (T := LeanEthCS.Forks.Fulu.LightClientOptimisticUpdate.Mainnet) raw expected)
  | _ => none

private def dispatchCheck (typeId : String) (raw : ByteArray)
    (expected : ByteArray) : Except String Unit :=
  let (preset, key) := parseTypeId typeId
  match key.splitOn ":" with
  | [fork, suffix] =>
    match fork with
    | "phase0" =>
        (dispatchCheck_phase0 preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | "altair" =>
        (dispatchCheck_altair preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | "bellatrix" =>
        (dispatchCheck_bellatrix preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | "capella" =>
        (dispatchCheck_capella preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | "deneb" =>
        (dispatchCheck_deneb preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | "electra" =>
        (dispatchCheck_electra preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | "fulu" =>
        (dispatchCheck_fulu preset suffix raw expected).getD
          (.error s!"unknown type identifier: {typeId}")
    | _ => .error s!"unknown type identifier: {typeId}"
  | _ => .error s!"unknown type identifier: {typeId}"

-- END AUTO-GENERATED DISPATCH --

/-! ### `ssz_generic` shape parsing

`ssz_generic` test cases address SSZ shapes by string identifiers
embedded in the case directory name (e.g. `uint_64_zero`,
`vec_bool_16_max`, `bitvec_8_random`). The CLI receives the
SHAPE PREFIX (variant stripped by the Python orchestrator) and
parses it into an `SSZType`.

Supported shape prefixes (consensus-spec-tests phase0/ssz_generic
layout):

* `bool`
* `uint_<N>` for N ∈ {8, 16, 32, 64, 128, 256}
* `vec_<elem>_<size>` where `elem ∈ {bool, uint8, …, uint256}`
* `bitvec_<size>`
* `bitlist_<cap>`

`containers` tests use named test-only structures
(`SingleFieldTestStruct`, `VarTestStruct`, …); those are not parsed
here, they'd require defining the test container types as Lean
structures with `deriving SSZRepr`, and the CLI does not. -/

/-- Parse a uintN element identifier (`uint8`, `uint16`, …). -/
private def parseUintElem (s : String) : Option SSZType :=
  match s with
  | "uint8"   => some (.uintN 8)
  | "uint16"  => some (.uintN 16)
  | "uint32"  => some (.uintN 32)
  | "uint64"  => some (.uintN 64)
  | "uint128" => some (.uintN 128)
  | "uint256" => some (.uintN 256)
  | _         => none

/-- Parse a basic-type element identifier (uintN, bool). -/
private def parseElem (s : String) : Option SSZType :=
  if s == "bool" then some .bool
  else parseUintElem s

/-! ### Test-only container shapes

The `ssz_generic/containers` tests define a small fixed set of
test-only container types, see consensus-spec-tests
`formats/ssz_generic/containers.md`. The CLI hard-codes their SSZ
shapes so `ssz_generic_check <ContainerName> …` works against the
upstream vectors without us defining matching Lean `structure`s
(which would also need `deriving SSZRepr`, and we'd still need a
dispatch arm here).

The encoded shapes match the spec definitions:

* `SingleFieldTestStruct = Container { A: byte }`
* `SmallTestStruct = Container { A: uint16, B: uint16 }`
* `FixedTestStruct = Container { A: uint8, B: uint64, C: uint32 }`
* `VarTestStruct = Container { A: uint16, B: List[uint16, 1024], C: uint8 }`
* `ComplexTestStruct = Container { A: uint16, B: List[uint16, 128],
    C: uint8, D: List[byte, 256], E: VarTestStruct,
    F: Vector[FixedTestStruct, 4], G: Vector[VarTestStruct, 2] }`
* `BitsStruct = Container { A: Bitlist[5], B: Bitvector[2],
    C: Bitvector[1], D: Bitlist[6], E: Bitvector[8] }`
-/

private def varTestStructShape : SSZType :=
  .container [.uintN 16, .list (.uintN 16) 1024, .uintN 8]

private def fixedTestStructShape : SSZType :=
  .container [.uintN 8, .uintN 64, .uintN 32]

private def complexTestStructShape : SSZType :=
  .container [
    .uintN 16,
    .list (.uintN 16) 128,
    .uintN 8,
    .list (.uintN 8) 256,
    varTestStructShape,
    .vector fixedTestStructShape 4,
    .vector varTestStructShape 2
  ]

private def bitsStructShape : SSZType :=
  .container [.bitlist 5, .bitvector 2, .bitvector 1, .bitlist 6, .bitvector 8]

/-- Parse a shape prefix into an `SSZType`. Returns `none` on
unrecognised input. -/
private def parseShape (s : String) : Option SSZType :=
  if s == "bool" then
    some .bool
  else if s == "SingleFieldTestStruct" then
    some (.container [.uintN 8])
  else if s == "SmallTestStruct" then
    some (.container [.uintN 16, .uintN 16])
  else if s == "FixedTestStruct" then
    some fixedTestStructShape
  else if s == "VarTestStruct" then
    some varTestStructShape
  else if s == "ComplexTestStruct" then
    some complexTestStructShape
  else if s == "BitsStruct" then
    some bitsStructShape
  else if s.startsWith "uint_" then
    -- `uint_<N>`: convert to `uintN<N>` by dropping the underscore
    -- and parsing the suffix as a Nat.
    let n? := (s.drop 5).toString.toNat?
    match n? with
    | some 8   => some (.uintN 8)
    | some 16  => some (.uintN 16)
    | some 32  => some (.uintN 32)
    | some 64  => some (.uintN 64)
    | some 128 => some (.uintN 128)
    | some 256 => some (.uintN 256)
    | _        => none
  else if s.startsWith "bitvec_" then
    (s.drop 7).toString.toNat?.map .bitvector
  else if s.startsWith "bitlist_" then
    (s.drop 8).toString.toNat?.map .bitlist
  else if s.startsWith "vec_" then
    -- `vec_<elem>_<size>`: split the last `_<size>` off and recurse
    -- on the element identifier.
    let body := (s.drop 4).toString
    let parts := body.splitOn "_"
    match parts.reverse with
    | sizeStr :: elemRevParts =>
        let elemStr := String.intercalate "_" elemRevParts.reverse
        match parseElem elemStr, sizeStr.toNat? with
        | some elemShape, some n => some (.vector elemShape n)
        | _, _ => none
    | _ => none
  else none

/-- Round-trip + root check on a bare `SSZType` shape. The
`shape.interp` dependent type is opaque to the caller; we only
expose the byte-level invariants (re-serialize equals input, root
equals expected). -/
private def runSSZGenericCheck (shape : SSZType) (raw : ByteArray)
    (expectedRoot : ByteArray) : Except String Unit :=
  match SSZType.deserialize shape raw with
  | .error e =>
      .error s!"deserialize failed: {repr e}"
  | .ok (v, used) =>
      if used ≠ raw.size then
        .error s!"trailing bytes: consumed {used}/{raw.size}"
      else
        let reSerialized := SSZType.serialize shape v
        if reSerialized ≠ raw then
          .error s!"re-serialize mismatch: {reSerialized.size} vs {raw.size}"
        else
          let root := Spec.hashTreeRoot (H := Sha256) shape v
          if root ≠ expectedRoot then
            .error s!"root mismatch: got {toHex root}, expected {toHex expectedRoot}"
          else .ok ()

/-- For an `invalid` case: must FAIL to deserialize (or consume the
wrong number of bytes). Returns `.ok ()` if the failure mode matches
the invalid-case contract. -/
private def runSSZGenericInvalid (shape : SSZType) (raw : ByteArray) :
    Except String Unit :=
  match SSZType.deserialize shape raw with
  | .error _ => .ok ()
  | .ok (_, used) =>
      if used ≠ raw.size then .ok ()
      else .error "expected deserialize to fail, but it succeeded"

/-- Entry point. Parses argv and dispatches. Returns exit code via
`IO.UInt32`. -/
-- ### `batch` mode: streaming protocol over stdin/stdout
--
-- To amortise the Lean-runtime startup cost across many test cases the
-- conformance harness invokes `eth_ssz_vector_runner batch` once per
-- sweep and feeds requests through stdin. Each line is a tab-separated
-- record matching one of the per-case argv forms (`check`, `root`,
-- `ssz_generic_check`, `ssz_generic_invalid`); the CLI emits one
-- tab-separated response line per request, flushed immediately so the
-- caller can stream progress.
--
-- Wire format (each line, terminated by `\n`):
--
-- * Request: `<command>\t<arg₁>\t<arg₂>[\t<arg₃>]`
-- * Response on success: `ok` for `check` / `ssz_generic_*`, or
--   `ok\t<hex>` for `root`.
-- * Response on failure: `fail\t<one-line-reason>`. Embedded `\t`, `\n`,
--   `\r` in the reason are replaced with single spaces so the response
--   stays single-line.
--
-- EOF on stdin terminates the loop with exit code 0. Any malformed
-- request is reported as a `fail` for that case and the loop continues,
-- the batch as a whole only fails if the CLI itself can't run.

private def escapeRespMsg (msg : String) : String :=
  msg.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "

/-- Process a single batch request line and return the response line to
emit (without trailing `\n`). Exceptions inside per-case work
(missing files, malformed hex, etc.) are caught and reported as
`fail` so a single bad case doesn't terminate the whole sweep. -/
private def runBatchRequest (line : String) : IO String := do
  try
    match line.splitOn "\t" with
    | ["root", typeId, path] => do
        let raw ← readFile path
        match dispatchRoot typeId raw with
        | .ok hex   => return s!"ok\t{hex}"
        | .error msg => return s!"fail\t{escapeRespMsg msg}"
    | ["check", typeId, path, expectedHex] => do
        let raw ← readFile path
        match fromHex expectedHex with
        | none => return s!"fail\tinvalid expected root hex: {expectedHex}"
        | some expected =>
            match dispatchCheck typeId raw expected with
            | .ok () => return "ok"
            | .error msg => return s!"fail\t{escapeRespMsg msg}"
    | ["ssz_generic_check", shapeSpec, path, expectedHex] => do
        let raw ← readFile path
        match parseShape shapeSpec with
        | none => return s!"fail\tunknown shape spec: {shapeSpec}"
        | some shape =>
            match fromHex expectedHex with
            | none => return s!"fail\tinvalid expected root hex: {expectedHex}"
            | some expected =>
                match runSSZGenericCheck shape raw expected with
                | .ok () => return "ok"
                | .error msg => return s!"fail\t{escapeRespMsg msg}"
    | ["ssz_generic_invalid", shapeSpec, path] => do
        let raw ← readFile path
        match parseShape shapeSpec with
        | none => return s!"fail\tunknown shape spec: {shapeSpec}"
        | some shape =>
            match runSSZGenericInvalid shape raw with
            | .ok () => return "ok"
            | .error msg => return s!"fail\t{escapeRespMsg msg}"
    | _ => return s!"fail\tmalformed request: {escapeRespMsg line}"
  catch e =>
    return s!"fail\texception: {escapeRespMsg e.toString}"

/-- Run the batch loop: read one request per stdin line, write one
response per stdout line, flush after each so the caller can drive a
progress indicator. Stops on stdin EOF. -/
private partial def runBatchLoop : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec go : IO UInt32 := do
    let raw ← stdin.getLine
    if raw.isEmpty then return 0  -- EOF
    -- Strip the trailing newline (and any \r from CRLF inputs)
    let line := raw.trimAsciiEnd.toString
    let response ← runBatchRequest line
    stdout.putStrLn response
    stdout.flush
    go
  go

def main (args : List String) : IO UInt32 := do
  match args with
  | ["batch"] => runBatchLoop
  | ["root", typeId, path] =>
      let raw ← readFile path
      match dispatchRoot typeId raw with
      | .ok hex => IO.println hex; return 0
      | .error msg => IO.eprintln s!"eth_ssz_vector_runner root: {msg}"; return 1
  | ["check", typeId, path, expectedHex] =>
      let raw ← readFile path
      match fromHex expectedHex with
      | none =>
          IO.eprintln s!"eth_ssz_vector_runner check: invalid expected root hex: {expectedHex}"
          return 2
      | some expected =>
          match dispatchCheck typeId raw expected with
          | .ok () => return 0
          | .error msg =>
              IO.eprintln s!"eth_ssz_vector_runner check {typeId}: {msg}"
              return 1
  | ["ssz_generic_check", shapeSpec, path, expectedHex] =>
      let raw ← readFile path
      match parseShape shapeSpec with
      | none =>
          IO.eprintln s!"eth_ssz_vector_runner ssz_generic_check: unknown shape spec: {shapeSpec}"
          return 2
      | some shape =>
          match fromHex expectedHex with
          | none =>
              IO.eprintln s!"eth_ssz_vector_runner ssz_generic_check: invalid expected root hex: {expectedHex}"
              return 2
          | some expected =>
              match runSSZGenericCheck shape raw expected with
              | .ok () => return 0
              | .error msg =>
                  IO.eprintln s!"eth_ssz_vector_runner ssz_generic_check {shapeSpec}: {msg}"
                  return 1
  | ["ssz_generic_invalid", shapeSpec, path] =>
      let raw ← readFile path
      match parseShape shapeSpec with
      | none =>
          IO.eprintln s!"eth_ssz_vector_runner ssz_generic_invalid: unknown shape spec: {shapeSpec}"
          return 2
      | some shape =>
          match runSSZGenericInvalid shape raw with
          | .ok () => return 0
          | .error msg =>
              IO.eprintln s!"eth_ssz_vector_runner ssz_generic_invalid {shapeSpec}: {msg}"
              return 1
  | _ =>
      IO.eprintln "usage:"
      IO.eprintln "  eth_ssz_vector_runner root                <fork>:<type> <input.ssz>"
      IO.eprintln "  eth_ssz_vector_runner check               <fork>:<type> <input.ssz> <expected_root_hex>"
      IO.eprintln "  eth_ssz_vector_runner ssz_generic_check   <shape_spec>  <input.ssz> <expected_root_hex>"
      IO.eprintln "  eth_ssz_vector_runner ssz_generic_invalid <shape_spec>  <input.ssz>"
      IO.eprintln "  eth_ssz_vector_runner batch  (read tab-separated requests from stdin; see Cli/Main.lean)"
      return 2

end LeanEthCS.Cli

/-- Top-level entry point. `lake exe eth_ssz_vector_runner --
<args>` invokes this through the `lean_exe` declaration in
`lakefile.toml`. On systems where Lean's bundled startup files
cannot link against glibc 2.34+ (which removes a few symbols the
startup objects reference), `lake env lean --run
LeanEthCS/Cli/Main.lean -- <args>` is the alternative route. -/
def main : List String → IO UInt32 := LeanEthCS.Cli.main
