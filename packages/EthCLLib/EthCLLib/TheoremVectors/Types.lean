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

/-- The DNF split's disjunct cap (`THEOREM_VECTORS_ARCHITECTURE.md` §8.2, the
option table in §14.4). A theorem whose unfolded hypotheses split into more
disjuncts than this falls back to one disjunct with the unsplit hypothesis,
and the pass reports the fallback (§8.2). -/
register_option theorem_vectors.maxDisjuncts : Nat := {
  defValue := 16
  descr    := "the cap on the prepare pass's DNF disjuncts per theorem"
}

/-- The heartbeat budget one theorem's run gets (`THEOREM_VECTORS_ARCHITECTURE.md`
§14.3, the option table in §14.4). The command sets it around each run, so
one line's solver calls and compiled-read evaluations never share a budget
with the theorems beside it. -/
register_option theorem_vectors.maxHeartbeats : Nat := {
  defValue := 1000000
  descr    := "the heartbeat budget the command sets around each run, in \
    the units `set_option maxHeartbeats` takes (the context value is this \
    times 1000)"
}

/-- The random searcher's redraw budget (`THEOREM_VECTORS_ARCHITECTURE.md`
§9.4, the option table in §14.4): how many draws one disjunct's search
tries before it answers `notFound`. -/
register_option theorem_vectors.randomDraws : Nat := {
  defValue := 64
  descr    := "the redraw budget of the random searcher, per disjunct"
}

/-- The `Gen` size parameter the random searcher draws with (§14.4). It
bounds the lists a draw produces, under the shapes' SSZ limits. -/
register_option theorem_vectors.randomSize : Nat := {
  defValue := 8
  descr    := "the `Gen` size parameter of the random searcher's draws"
}

/-- The shrink loop's step budget (`THEOREM_VECTORS_ARCHITECTURE.md` §9.6,
the option table in §14.4). A witness from the random searcher shrinks
until no candidate passes the check or the budget runs out. The default
is small, because the probe's `check` runs the disjunct's compiled `decide`
over a drawn state, and the interpreter bills every run of it; the
length cuts sit first in each call's candidate list, so the first steps
buy the size. -/
register_option theorem_vectors.shrinkSteps : Nat := {
  defValue := 40
  descr    := "the shrink budget of the random searcher, per witness"
}

/-- The random draw seed (§14.4). The same seed and size draw the same
bytes, so a build is reproducible; a hint (§9.8) replays it exactly. -/
register_option theorem_vectors.seed : Nat := {
  defValue := 0
  descr    := "the random seed of the random searcher's draws"
}

/-- The hint mode (§9.8, the option table in §14.4): `use` reads the
committed hints and searches around them, `ignore` searches everything,
and `require` turns a missing or failing hint into a build error. The
`THEOREM_VECTORS_HINTS` variable reads ahead of this option, which is how
the rebuild recipe overrides it without touching the declarative
lakefile. -/
register_option theorem_vectors.hints : String := {
  defValue := "use"
  descr    := "the hint searcher's mode: use, ignore, or require"
}

/-- The committed hints root (`THEOREM_VECTORS_ARCHITECTURE.md` §9.8), the
directory holding one `<fork>/<thm>.json` file per fork and theorem. The
lakefile fixes it the way it fixes `theorem_vectors.outDir`, with the same
repository-root-relative spelling; the empty default means the fork
commits no hints, and the hint searcher never applies. -/
register_option theorem_vectors.hintsDir : String := {
  defValue := ""
  descr    := "the committed hints root the hint searcher reads"
}

/-- How far down the builder grid the `built` searcher walks
(`THEOREM_VECTORS_ARCHITECTURE.md` §9.9, the option table in §14.4). The
default `0` means the preset's own cap, `6` at minimal and `3` at
mainnet, the values §14.4's table fixes: mainnet's spec runs go over
65536-long vectors, and the two 16-validator slot-40 states and the
64-validator slot-40 one are what mainnet's cap cuts. A positive value
applies at both presets. -/
register_option theorem_vectors.builtSteps : Nat := {
  defValue := 0
  descr    := "the cap on the built searcher's builder grid; 0 takes the \
    preset's default (6 at minimal, 3 at mainnet)"
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

/-- The presets write their tags, the same strings the paths and the wire
files use. -/
instance : ToJson PresetId where
  toJson p := .str p.tag

instance : FromJson PresetId where
  fromJson? j := do
    let s ← j.getStr?
    match PresetId.ofTag? s with
    | some p => pure p
    | none => throw s!"unknown preset tag '{s}'"

/-! ## Shapes and searchers -/

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

/-- Read a shape back from its wire tag. The record reader goes through
this. -/
def ShapeTag.ofTag? : String → Option ShapeTag
  | "eq"       => some .eq
  | "iffTrue"  => some .iffTrue
  | "bound"    => some .bound
  | "runOk"    => some .runOk
  | "runError" => some .runError
  | _          => none

/-- Which witness searcher proposed a candidate (`THEOREM_VECTORS_ARCHITECTURE.md` §5.4).
The searchers run in a fixed order, cheapest first, and the record names the
one that won. `.reused` marks a scalar witness carried over from an earlier
preset (§10), `.hinted` a witness rebuilt from a committed hint (§9.8). -/
inductive WitnessSearcherTag where
  | base
  | bitVec
  | built
  | random
  | manual
  /-- A scalar witness from the preset it names. -/
  | reused (preset : PresetId)
  /-- Rebuilt from a committed hint; `orig` is the searcher the hint recorded. -/
  | hinted (orig : WitnessSearcherTag)
  deriving BEq, Repr, Inhabited

/-- The wire tag of a searcher, as the records and outcome files write it
(§16.1's `witnessSearcher` field). -/
def WitnessSearcherTag.tag : WitnessSearcherTag → String
  | .base      => "base"
  | .bitVec    => "bitVec"
  | .built     => "built"
  | .random    => "random"
  | .manual    => "manual"
  | .reused p  => s!"reused-{p.tag}"
  | .hinted o  => s!"hinted-{o.tag}"

/-- The five plain searcher tags, the leaves of the compound spellings. -/
private def plainSearcherTag? : String → Option WitnessSearcherTag
  | "base"   => some .base
  | "bitVec" => some .bitVec
  | "built"  => some .built
  | "random" => some .random
  | "manual" => some .manual
  | _        => none

/-- The tag reader's recursion core, over the tag's characters. The
`hinted-` prefix recurses, so nested compound tags parse; the `reused-`
prefix reads a preset, which is a leaf. The plain tags are the last arm.
The structural recursion runs on the character list, which avoids a
size-of proof over this toolchain's `Slice`-returning `String.drop`. -/
private def ofTagChars : List Char → Option WitnessSearcherTag
  | 'h' :: 'i' :: 'n' :: 't' :: 'e' :: 'd' :: '-' :: rest =>
    (ofTagChars rest).map .hinted
  | 'r' :: 'e' :: 'u' :: 's' :: 'e' :: 'd' :: '-' :: rest =>
    (PresetId.ofTag? (String.ofList rest)).map .reused
  | cs => plainSearcherTag? (String.ofList cs)

/-- Read a searcher back from its wire tag. The record reader goes through
this. The compound tags read back in full and recursively:
`hinted-<orig>` is the `.hinted orig` a replayed hint writes (§9.8), and
`reused-<preset>` the `.reused preset` a reused witness writes (§10), so
`hinted-reused-minimal` reads back as `.hinted (.reused .minimal)`. -/
def WitnessSearcherTag.ofTag? (s : String) : Option WitnessSearcherTag :=
  ofTagChars s.toList

#guard WitnessSearcherTag.ofTag? "hinted-reused-minimal" ==
  some (.hinted (.reused .minimal))
#guard WitnessSearcherTag.ofTag? "reused-mainnet" == some (.reused .mainnet)
#guard WitnessSearcherTag.ofTag? "hinted-bitVec" == some (.hinted .bitVec)
#guard WitnessSearcherTag.ofTag? "manual" == some .manual
#guard WitnessSearcherTag.ofTag? "hinted-manual" == some (.hinted .manual)

/-- Why a disjunct produced no vector (`THEOREM_VECTORS_ARCHITECTURE.md` §5.4). `unsat` means
the solver proved the hypotheses vacuous, `notFound` that every searcher
ran out, and `outOfScope` that a block input is in play and the base
searcher failed (§1.2). A `notFound` carries the details the searchers
reported: the atoms the solver abstracted, an input type outside its
domain (§9.4). -/
inductive Failure where
  | unsat
  | notFound (tried : Array WitnessSearcherTag) (details : Array String := #[])
  | outOfScope (inputs : Array Name)
  deriving BEq, Repr, Inhabited

/-! ## Assignments -/

/-- A closed value for every input, in binder order, as SSZ bytes
(`THEOREM_VECTORS_ARCHITECTURE.md` §5.4). The byte boundary (§9.1) makes this the
only form a candidate takes between the searchers and the probe. -/
abbrev Assignment := Array ByteArray

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

/-- A byte string as the records write a root: `0x` and two lowercase hex
digits per byte. One spelling for every wire file, so a root reads back the
same way everywhere. -/
def hexOf (bytes : ByteArray) : String :=
  let digit (d : Nat) : Char :=
    "0123456789abcdef".toList[d]!
  "0x" ++ String.ofList (bytes.toList.flatMap fun b =>
    [digit (b.toNat / 16), digit (b.toNat % 16)])

/-- Read a `0x…` root back, two hex digits per byte. -/
def hexBytes? (s : String) : Option ByteArray :=
  let hexVal (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let cs := s.toList
  if cs.take 2 == ['0', 'x'] && (cs.length - 2) % 2 == 0 then
    let digits := cs.drop 2
    let rec pairs (ds : List Char) : Option (List Nat) :=
      match ds with
      | [] => some []
      | [_] => none
      | a :: b :: rest =>
        match hexVal a, hexVal b, pairs rest with
        | some va, some vb, some rest' => some ((16 * va + vb) :: rest')
        | _, _, _ => none
    (pairs digits).map
      (fun bs => ByteArray.mk (bs.toArray.map UInt8.ofNat))
  else none

/-- The JSON forms of the payload (`THEOREM_VECTORS_ARCHITECTURE.md` §12.2): an SSZ value
writes its root as `0x…`, a scalar its literal. The side file's name comes
from the value's own `name` field, so neither form repeats it. -/
instance : ToJson ValueData where
  toJson
    | .ssz root => Lean.Json.mkObj [("root", Lean.Json.str (hexOf root))]
    | .scalar lit => Lean.Json.mkObj [("scalar", Lean.Json.str lit)]

instance : FromJson ValueData where
  fromJson? j := do
    match j.getObjVal? "root" with
    | .ok r =>
      let rs ← r.getStr?
      match hexBytes? rs with
      | some b => return .ssz b
      | none => throw s!"cannot read a root from '{rs}'"
    | .error _ =>
      let lit ← j.getObjValAs? String "scalar"
      return .scalar lit

/-! ## State-builder knobs -/

/-- The knobs one state-builder step fixes (`THEOREM_VECTORS_ARCHITECTURE.md` §9.9). One
framework type, so the `built` searcher can walk a builder grid without
naming a fork. The defaults are the cheapest grid step: a small genesis
committee at slot 0 with no queue. -/
structure Knobs where
  validators : Nat := 8
  slot       : Nat := 0
  balance    : Nat := 32000000000
  queue      : Nat := 0
  deriving Repr, BEq, Hashable, Inhabited

/-- The knobs' JSON, as the built hint row writes them (§9.8). The values
are grid constants the generator picked, small enough for a JSON
integer; a solved scalar is the value that needs a decimal string. They
write as numbers the way a hint's `seed`, `size`, and `draw` do. -/
instance : ToJson Knobs where
  toJson k :=
    Json.mkObj [("validators", k.validators), ("slot", k.slot),
      ("balance", k.balance), ("queue", k.queue)]

instance : FromJson Knobs where
  fromJson? j := do
    let validators ← j.getObjValAs? Nat "validators"
    let slot ← j.getObjValAs? Nat "slot"
    let balance ← j.getObjValAs? Nat "balance"
    let queue ← j.getObjValAs? Nat "queue"
    return { validators, slot, balance, queue }

end EthCLLib.TheoremVectors
