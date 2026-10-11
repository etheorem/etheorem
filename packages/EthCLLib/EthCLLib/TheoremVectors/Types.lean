import Lean

/-!
# `EthCLLib.TheoremVectors.Types`: the core data model

The scalar data model of the theorem-vector generator (`THEOREM_VECTORS_ARCHITECTURE.md`
§5, with the `Knobs` state-builder interface from §9.9). Every type here
lives in the framework half and names no fork: the record layer persists
them as JSON through `Lean.Json`, and the fork binding carries them across
the seam (`ForkBinding`).
-/

set_option autoImplicit false

open Lean

/-- The output root the generator commands write into, the one option the
lakefile fixes (`THEOREM_VECTORS_ARCHITECTURE.md` §2.3; the option table in §14.4 gives
the default). It registers here because every generator module imports
this module through some path, so Lake's weak `-D` setting reaches every
module that reads the option at elaboration time. An exe root builds
under the exe's own configuration, so the exe takes the path from the
spec-half root's `outDir` constant instead. -/
register_option theorem_vectors.outDir : String := {
  defValue := "theorem_vectors"
  descr    := "the output root the theorem-vector generator writes into"
}

namespace EthCLLib.TheoremVectors

/-! ## Presets -/

/-- The presets a run can fix (`THEOREM_VECTORS_ARCHITECTURE.md` §5.1). The generator, the
records, and the output paths all take the preset from this inductive; the
fork binding maps each one to the fork's own `Preset` and `Config`
instances. -/
inductive PresetId where
  | minimal
  | mainnet
  deriving DecidableEq, Repr, Inhabited

/-- The path segment and pyspec fork-axis name of a preset, as the records
and outcome lines write it. -/
def PresetId.tag : PresetId → String
  | .minimal => "minimal"
  | .mainnet => "mainnet"

/-- Read a preset back from its tag. The exe's `--preset` flag and the
report both go through this. -/
def PresetId.ofTag? : String → Option PresetId
  | "minimal" => some .minimal
  | "mainnet" => some .mainnet
  | _         => none

/-! ## Shapes and sources -/

/-- The direction of a `.bound` conclusion (`THEOREM_VECTORS_ARCHITECTURE.md` §5.3):
`lhs < b` or `lhs ≤ b`. -/
inductive BoundRel where
  | lt
  | le
  deriving DecidableEq, Repr, Inhabited

/-- The conclusion form of a theorem in the tags the records and outcomes
write (`THEOREM_VECTORS_ARCHITECTURE.md` §5.3). The `Shape` terms themselves live with the
statement reader. -/
inductive ShapeTag where
  | eq
  | iffTrue
  | bound
  | runOk
  | runError
  deriving DecidableEq, Repr, Inhabited

/-- The wire tag of a shape, as the records and the outcome files write
it. -/
def ShapeTag.tag : ShapeTag → String
  | .eq       => "eq"
  | .iffTrue  => "iffTrue"
  | .bound    => "bound"
  | .runOk    => "runOk"
  | .runError => "runError"

/-- Which witness source proposed a candidate (`THEOREM_VECTORS_ARCHITECTURE.md` §5.4).
The sources run in a fixed order, cheapest first, and the record names the
one that won. `.reused` marks a scalar witness carried over from an earlier
preset (§10), `.hinted` a witness rebuilt from a committed hint (§9.8). -/
inductive WitnessSourceTag where
  | base
  | bitVec
  | built
  | random
  | seed
  /-- A scalar witness from the preset it names. -/
  | reused (preset : PresetId)
  /-- Rebuilt from a committed hint; `orig` is the source the hint recorded. -/
  | hinted (orig : WitnessSourceTag)
  deriving BEq, Repr, Inhabited

/-- Why a case produced no vector (`THEOREM_VECTORS_ARCHITECTURE.md` §5.4). `unsat` means
the solver proved the hypotheses vacuous, `notFound` that every source ran
out, and `outOfScope` that a block input is in play and the base source
failed (§1.2). -/
inductive Failure where
  | unsat
  | notFound (tried : Array WitnessSourceTag)
  | outOfScope (inputs : Array Name)
  deriving BEq, Repr, Inhabited

/-! ## Record payloads -/

/-- The payload form of one recorded value (`THEOREM_VECTORS_ARCHITECTURE.md` §5.6). An
`.ssz` value carries its Merkle root in the record and its bytes in a side
file; a `.scalar` carries its literal for the reader and keeps its SSZ bytes
in the same side file, so the read-back needs no type width. -/
inductive ValueData where
  /-- An SSZ value: its bytes live in `<name>.ssz`, the root goes in the
  record. -/
  | ssz (root : ByteArray)
  /-- A scalar: its decimal (or boolean) literal for the reader. -/
  | scalar (literal : String)
  deriving BEq, Inhabited

/-! ## State-builder knobs -/

/-- The knobs one state-builder step fixes (`THEOREM_VECTORS_ARCHITECTURE.md` §9.9). One
framework type, so the `built` source can walk a builder grid without
naming a fork. The defaults are the cheapest grid step: a small genesis
committee at slot 0 with no queue. -/
structure Knobs where
  validators : Nat := 8
  slot       : Nat := 0
  balance    : Nat := 32000000000
  queue      : Nat := 0
  deriving Repr, BEq, Hashable, Inhabited

end EthCLLib.TheoremVectors
