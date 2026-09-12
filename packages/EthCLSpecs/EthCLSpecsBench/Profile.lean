import EthCLSpecs
import SizzLeanBench.Runner

/-!
# `EthCLSpecsBench.Profile`: per-container profile of a real state transition

Stage 17d pass 2 asks which consensus container types dominate the
encode, decode, and root cost of a real state-transition workload
(`packages/SizzLean/docs/OPTIMISATION.md`, "Stage 17d"). This module
answers that question with measurements, not guesses: it decodes an
upstream Gloas mainnet `sanity/blocks` vector and times each SSZ
operation separately, per container type.

The profile runs at the **mainnet** preset, on a `BeaconState` of a
few hundred kilobytes, so the row set reflects production sizes
rather than the minimal preset's toy registry.

## Why the profile lives here and not in `SizzLeanBench`

`SizzLeanBench` cannot import `EthCLSpecs`: the specs package already
depends on `SizzLean`, so the edge would close a cycle. `SizzLeanBench`
therefore profiles a hand-copied `ValidatorShape` fixture. The types
this profile must name (`BeaconState`, `Validator`, `SignedBeaconBlock`)
are the real spec containers, which only exist here. The bench runner
itself is reused across the boundary: `SizzLeanBench.Runner` supplies
the TSV row shape and the sampling loop, so both profiles emit the same
columns and `just sizzlean-bench-diff` compares either one.

## The row set

| Row group | What it isolates |
|---|---|
| `deserialize` | wire bytes → container value, per type |
| `serialize` | container value → wire bytes, per type |
| `htr` | merkleization of a container value, per type |
| `FastBox` | the cached path the pyspec driver actually takes |
| `stateTransition` | the end-to-end workload the hints must not slow |
| `ForkInterface` | the same work through the driver's preset-generic seam |

The `ForkInterface` rows matter for pass 2 specifically. Inside this
module the preset is a statically known instance, so the compiler
already sees which `SSZRepr` instance every call uses. The pyspec
driver instead injects the preset as a *runtime* value
(`gloasInterfaceFor mainnet mainnetConfig`), so its calls resolve the
instance through a dictionary. Comparing a `ForkInterface` row against
the matching direct row prices that dispatch, which is exactly what a
`@[specialize]` hint can remove.

Each per-type row hashes 1000 **distinct** values, built outside the
timed region. Distinct values matter: a loop that re-hashes one value
lets the compiler hoist the call out of the loop, and the row would
then measure an empty loop.

## Anti-DCE

Every row sinks a byte of its result into an `IO.Ref Nat`. The sink
crosses an `IO.modify` boundary, so the compiler cannot drop the work
that produced it. The state-level rows additionally vary `genesisTime`
by the iteration index, which changes the root and defeats both
hoisting and any root memo.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open SizzLeanBench.Runner

namespace EthCLSpecsBench.Profile

open EthCLSpecs.Gloas

/-- Distinct values per per-type row. Large enough that one row's
median sits well above the clock's resolution, small enough that the
whole profile runs in a minute. -/
private def perTypeCount : Nat := 1000

/-- The mainnet instances every row runs at. `fastHasherTag` is the
FFI SHA-256 tag the pyspec driver uses; the profile must measure the
same hasher the production path does. -/
local instance : Preset := mainnet
local instance : Config := mainnetConfig
local instance : HasherTag := fastHasherTag

/-- Sink one byte of a root (or of any buffer) so the work survives
dead-code elimination. -/
@[inline] private def sinkBytes (sink : IO.Ref Nat) (b : ByteArray) : IO Unit :=
  sink.modify (· + b[0]!.toNat)

/-- Sink a root held as the spec's `Root` vector. -/
@[inline] private def sinkRoot (sink : IO.Ref Nat) (r : Vector UInt8 32) : IO Unit :=
  sink.modify (· + (vget r 0).toNat)

/-- Time `perTypeCount` `htr` calls over an array of distinct values
of one container type, and report them as one row. -/
private def rowHtr {T : Type} [SSZRepr T] (label : String) (iterations : Nat)
    (values : Array T) (sink : IO.Ref Nat) : IO Unit :=
  runBench s!"htr {label} ×{values.size}" iterations do
    let mut acc : Nat := 0
    for v in values do
      acc := acc + (vget (htr v) 0).toNat
    sink.modify (· + acc)

/-- Time `perTypeCount` `serialize` calls over distinct values of one
container type. -/
private def rowSerialize {T : Type} [SSZRepr T] (label : String) (iterations : Nat)
    (values : Array T) (sink : IO.Ref Nat) : IO Unit :=
  runBench s!"serialize {label} ×{values.size}" iterations do
    let mut acc : Nat := 0
    for v in values do
      acc := acc + (SSZ.serialize v).size
    sink.modify (· + acc)

/-- Time `perTypeCount` `deserialize` calls over distinct encodings of
one container type. A decode failure would make the row meaningless,
so the buffer's own bytes feed the sink and a failure sinks nothing. -/
private def rowDeserialize {T : Type} [SSZRepr T] (label : String) (iterations : Nat)
    (buffers : Array ByteArray) (sink : IO.Ref Nat) : IO Unit :=
  runBench s!"deserialize {label} ×{buffers.size}" iterations do
    let mut acc : Nat := 0
    for b in buffers do
      match SSZ.deserialize (T := T) b with
      | .ok _    => acc := acc + 1
      | .error _ => pure ()
    sink.modify (· + acc)

/-- Build `perTypeCount` distinct validators off the vector's own
registry, each with its own `effectiveBalance`. Varying a fixed-size
`uint64` field keeps every value the same size, so the row measures
per-value cost and not a size ramp. -/
private def distinctValidators (st : BeaconState) : Array Validator :=
  let base := st.validators[0]!
  Array.ofFn (n := perTypeCount) fun i =>
    { base with effectiveBalance := UInt64.ofNat (i.val + 1) }

/-- Distinct block headers off the state's `latestBlockHeader`, varied
by `slot`. -/
private def distinctHeaders (st : BeaconState) : Array BeaconBlockHeader :=
  let base := st.latestBlockHeader
  Array.ofFn (n := perTypeCount) fun i =>
    { base with slot := UInt64.ofNat (i.val + 1) }

/-- Distinct checkpoints off the state's `finalizedCheckpoint`, varied
by `epoch`. The smallest hot container in the state: two chunks. -/
private def distinctCheckpoints (st : BeaconState) : Array Checkpoint :=
  let base := st.finalizedCheckpoint
  Array.ofFn (n := perTypeCount) fun i =>
    { base with epoch := UInt64.ofNat (i.val + 1) }

/-- Distinct attestations off the block's first attestation, varied by
the attestation data's `slot`. Falls back to the `Inhabited` default
when the vector's block carries none, which keeps the row present (an
empty `aggregationBits` bitlist, so a floor rather than a typical
cost). -/
private def distinctAttestations (blocks : Array (SignedBeaconBlock)) :
    Array Attestation :=
  let base : Attestation :=
    match blocks[0]? with
    | some sb => (sb.message.body.attestations[0]?).getD default
    | none    => default
  Array.ofFn (n := perTypeCount) fun i =>
    { base with data := { base.data with slot := UInt64.ofNat (i.val + 1) } }

/-- Prebuild one distinct buffer copy per iteration. Copies of one
buffer hold equal bytes but are separate runtime objects, so the
compiler cannot lift a call on `buffers[i]` out of the timed loop the
way it can lift a call on a single loop-invariant buffer. -/
private def copiesOf (b : ByteArray) (n : Nat) : Array ByteArray :=
  Array.ofFn (n := n) fun _ => b.extract 0 b.size

/-- One row through the driver's seam: `act` runs once per iteration on
its own copy of the pre-state bytes. The `Except` is folded into the
sink on both branches, so a rejected run still counts as work done. -/
private def rowInterface (label : String) (iterations : Nat) (buffers : Array ByteArray)
    (sink : IO.Ref Nat) (act : ByteArray → Except (RunError StateTransitionError) ByteArray) :
    IO Unit := do
  let counter ← IO.mkRef 0
  runBench label iterations do
    let i ← counter.modifyGet (fun n => (n + 1, n))
    match act (buffers[i % buffers.size]!) with
    | .ok r    => sinkBytes sink r
    | .error _ => sink.modify (· + 1)

/-- One state-level row: `act` runs once per iteration on a state whose
`genesisTime` carries the iteration index, so no two iterations hash
the same value. -/
private def rowState (label : String) (iterations : Nat) (st : BeaconState)
    (sink : IO.Ref Nat) (act : BeaconState → IO Unit) : IO Unit := do
  -- The counter lives in a ref, not a `let mut`: the timed action is a
  -- closure `runBench` calls, and a `let mut` cannot cross into it.
  let counter ← IO.mkRef 0
  runBench label iterations do
    let i ← counter.modifyGet (fun n => (n + 1, n + 1))
    act { st with genesisTime := UInt64.ofNat i }
  sink.modify (· + (← counter.get))

/-- Run the whole profile against one vector: a pre-state buffer and
its block sequence, both raw (snappy already removed). Emits one TSV
row per measurement; the caller prints the header. -/
def runAll (preBytes : ByteArray) (blockBuffers : Array ByteArray) : IO Unit := do
  let sink ← IO.mkRef 0

  -- Decode once, outside every timed region: the row set profiles the
  -- operations, not this setup.
  let st : BeaconState ←
    match SSZ.deserialize (T := BeaconState) preBytes with
    | .ok v    => pure v
    | .error _ => throw (IO.userError "profile: the pre-state buffer did not decode as a Gloas BeaconState")
  let blocks : Array SignedBeaconBlock ←
    blockBuffers.mapM fun b =>
      match SSZ.deserialize (T := SignedBeaconBlock) b with
      | .ok sb   => pure sb
      | .error _ => throw (IO.userError "profile: a block buffer did not decode as a Gloas SignedBeaconBlock")

  IO.eprintln s!"[profile] mainnet Gloas · state {preBytes.size} bytes · \
    {st.validators.size} validators · {blocks.size} block(s)"

  /- ## State-level rows: the whole `BeaconState`, one value per iteration. -/
  rowState "deserialize BeaconState" 20 st sink fun _ => do
    match SSZ.deserialize (T := BeaconState) preBytes with
    | .ok v    => sink.modify (· + v.validators.size)
    | .error _ => pure ()
  rowState "serialize BeaconState" 20 st sink fun s =>
    sinkBytes sink (SSZ.serialize s)
  rowState "htr BeaconState (pure)" 20 st sink fun s =>
    sinkRoot sink (htr s)
  rowState "FastBox.hashTreeRoot BeaconState (first root)" 20 st sink fun s =>
    sinkBytes sink (SSZ.FastBox s).hashTreeRoot.1

  /- ## Per-type rows: 1000 distinct values of one container type. -/
  let validators := distinctValidators st
  let headers    := distinctHeaders st
  let checkpoints := distinctCheckpoints st
  let attestations := distinctAttestations blocks

  rowHtr "Validator" 20 validators sink
  rowHtr "BeaconBlockHeader" 20 headers sink
  rowHtr "Checkpoint" 20 checkpoints sink
  rowHtr "Attestation" 20 attestations sink

  rowSerialize "Validator" 20 validators sink
  rowSerialize "BeaconBlockHeader" 20 headers sink
  rowSerialize "Attestation" 20 attestations sink

  -- `rowDeserialize` takes buffers, so its `T` is not inferable from an
  -- argument: each call names the container type it decodes into.
  rowDeserialize (T := Validator) "Validator" 20 (validators.map SSZ.serialize) sink
  rowDeserialize (T := BeaconBlockHeader) "BeaconBlockHeader" 20 (headers.map SSZ.serialize) sink
  rowDeserialize (T := Attestation) "Attestation" 20 (attestations.map SSZ.serialize) sink

  /- ## Block-level rows. -/
  runBench s!"deserialize SignedBeaconBlock ×{blockBuffers.size}" 50 do
    let mut acc : Nat := 0
    for b in blockBuffers do
      match SSZ.deserialize (T := SignedBeaconBlock) b with
      | .ok _    => acc := acc + 1
      | .error _ => pure ()
    sink.modify (· + acc)
  runBench s!"htr SignedBeaconBlock ×{blocks.size}" 50 do
    let mut acc : Nat := 0
    for sb in blocks do
      acc := acc + (vget (htr sb) 0).toNat
    sink.modify (· + acc)

  /- ## The end-to-end workload, through the driver's own seam.

  `gloasInterfaceMainnet` is the instance the pyspec runner injects at
  mainnet, so these two rows are what a vector actually costs. Each
  iteration gets its own copy of the pre-state bytes (see `copiesOf`).
  `runBlocks` folds the vector's blocks with signature checks on, the
  `bls_setting: 0` behaviour. -/
  let iface := EthCLSpecs.Gloas.Interface.gloasInterfaceMainnet
  let preCopies := copiesOf preBytes 10
  rowInterface "ForkInterface.stateRoot BeaconState" 10 preCopies sink
    (fun b => iface.stateRoot b)
  rowInterface "ForkInterface.runBlocks (whole vector)" 10 preCopies sink
    (fun b => iface.runBlocks b blockBuffers { blsSetting := 0, blocksCount := blocks.size,
                                               forkEpoch := none, forkBlock := none,
                                               executionValid := true })

  -- Print the sink so no row can be eliminated as unobserved.
  IO.eprintln s!"[profile] sink = {← sink.get}"

end EthCLSpecsBench.Profile
