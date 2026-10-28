import EthCLSpecs.Fulu.Time

/-!
# `EthCLSpecs.Fulu.BlobParameters`: the blob schedule lookup (EIP-7892, load order between rows 20 and 21)

Fulu's blob-parameter-only forks (EIP-7892) put the per-block blob limit on a config
schedule, `BLOB_SCHEDULE`, rather than in a constant. `get_blob_parameters(epoch)`
(`fulu/beacon-chain.md`, "New `get_blob_parameters`") returns the latest entry at or before
`epoch`, or Electra's `(ELECTRA_FORK_EPOCH, MAX_BLOBS_PER_BLOCK_ELECTRA)` when none applies.
`process_execution_payload` (Fulu), `process_execution_payload_bid` (Gloas), and
`verify_data_column_sidecar` bound the blob commitments by its `max_blobs_per_block`.

State-free, so the module sits low in the load order, beside the clock helpers.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `BlobParameters` (`fulu/beacon-chain.md`, "New `BlobParameters`"): one blob-schedule entry,
the epoch it starts at and the blob limit from then on. A `forkstruct`, so a later fork can
`inherit` it. -/
forkstruct BlobParameters where
  epoch            : Epoch
  maxBlobsPerBlock : Nat

/-- `get_blob_parameters(epoch)` (`fulu/beacon-chain.md`, "New `get_blob_parameters`"): scan
`BLOB_SCHEDULE` from the latest epoch down and return the first entry at or before `epoch`;
with none, Electra's limit at `ELECTRA_FORK_EPOCH`. The schedule's epochs are distinct (the
config MUST NOT repeat one), so the descending sort has no ties to break. Pure. -/
forkdef getBlobParameters (epoch : Epoch) : BlobParameters :=
  let descending := Const.blobSchedule.toArray.qsort (fun a b => a.1 > b.1)
  match descending.find? (fun entry => epoch ≥ entry.1) with
  | some (entryEpoch, maxBlobs) => { epoch := entryEpoch, maxBlobsPerBlock := maxBlobs }
  | none => { epoch := Const.electraForkEpoch, maxBlobsPerBlock := Const.maxBlobsPerBlockElectra }

end

end EthCLSpecs.Fulu
