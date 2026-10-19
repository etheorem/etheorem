import Lean
import SizzLean
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.Crypto
import EthCLLib.Proofs.Run
import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.Sampleable
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Preset

/-!
# `EthCLLib.TheoremVectors.Probe`: the compiled face of one statement at one preset

The probe (`THEOREM_VECTORS_ARCHITECTURE.md` §11) is one closed term per statement and
preset, evaluated once with `evalExpr`, whose runtime type is the `Probe`
structure of this module: every later operation is a call on the resulting
value, with SSZ bytes in and SSZ bytes out (§9.1's byte boundary).

The term builder (§11.2) substitutes the instance binders with the binding's
constants (§10, through `Preset.constOf`), decodes each input through its
`ScalarCodec`, and hands the decoded values to the prepared conjunction's
`decide` (§8.4) and to the shape's terms. Two §11.2 rules shape the term: it
contains no `match` on `Except` or `EStateM.Result`, because the probe's glue
runs interpreted and a `match` there can trip matcher realization, so the
`Except`-matching lives in the helpers above (`runProbeOk`, `runProbeError`,
and the result assemblers); and it is elaborated once per statement and
preset, with the disjunct index as a runtime argument, so the search loop
never re-elaborates.

`sample` and `shrink` draw and shrink the container inputs through the
`Sampleable` generators (§9.5, §9.6); `reads` evaluates one disjunct's
container-reading subterms at the candidate's bytes (§9.4). `build` runs
the binding's named builders (§9.9), dispatching on the catalog index and
serializing through the state input's codec, and answers empty bytes for
a statement with no state input; `defaults` holds the serialized
`default` of every input, which the base searcher (§9.4) hands to `check`
as its candidate. The §11.1 sketch's face table lists every field of the
structure above, `defaults` and the `reads` disjunct index included. The
base searcher needs `defaults`, and no other probe function supplies it.
§9.2 already gave `check` the same disjunct index, and the reads are the
disjunct's hypotheses' subterms. `IMPLEMENTATION_NOTES.md` records, stage
by stage, the fields whose sketches predated them.

Three design points this module contributed to the sketches carry their
reasons; `IMPLEMENTATION_NOTES.md` records the stage at which each was a
deviation:

- the term is built as an `Expr` tree. §11.2 states the construction: the
  direct build, `mkLambdaFVars` abstracting the value binders, and a
  substitution that replaces the instance binders, itself a mechanical
  `Expr` rewrite. Direct construction achieves the same closed term
  without a stringly-typed intermediate.
- `ProbeResult` carries the inputs' literals and splits the roots into
  `inputRoots` and `outputRoot` (§5.5's sketch lists the fields). The
  record layer (§12.2) writes a decimal literal for a scalar and a root
  for a container, and it needs to know which one each value is; a
  `Nat`-typed bound output has no SSZ root at all.
- one `ScalarCodec` class fronts the wire encoding (§11.2 names the
  class). A `Fin`-typed input (`initializePtcWindow_lt`'s window offset)
  has no `SSZRepr` instance, because a total decode from bytes cannot
  respect `Fin`'s bound; its codec is the `uintN 64` little-endian
  encoding of `Fin.val`, the same scalar family §9.4's bit-vector searcher
  puts `Fin n` in.

## Lean idioms annotated

- `Meta.evalExpr` adds the term as a definition and runs it. It is `unsafe`
  because the caller asserts the value's type; the wrapper below follows the
  `implemented_by` shape `Command.lean` uses for `evalConst`.
- `mkLambdaFVars` abstracts free variables into a `fun` chain. The builder
  works inside the reader's telescope scope (`Statement.readIn`), where the
  statement's expressions still mention the theorem's free variables; each
  `mkLambdaFVars` call binds one of them, so the finished term is closed
  once the instance variables are replaced with the binding's constants.
- A raw `Expr` built by hand is never elaborated again: `evalExpr` typechecks
  it, so a builder mistake surfaces as an evaluation error naming the term.
-/

set_option autoImplicit false

open Lean
open SizzLean (SSZRepr)

namespace EthCLLib.TheoremVectors

/-! ## The precompiled helpers (§11.2) -/

/-- The bytes nothing records. -/
def emptyBytes : ByteArray := ByteArray.mk #[]

/-- The one-byte SSZ form of a `Bool`, the `.iffTrue` run's output shape
(`THEOREM_VECTORS_ARCHITECTURE.md` §11.3): the same byte SSZ's `bool` serialize writes. -/
def boolBytes (b : Bool) : ByteArray :=
  ByteArray.mk #[b.toUInt8]

/-- The byte comparison the `.eq` shapes run on (`THEOREM_VECTORS_ARCHITECTURE.md` §11.3):
one place, so the agreement rule stays a fact of the framework half. -/
def compareBytes (a b : ByteArray) : Bool := a == b

/-- The repr comparison the `.runError` shape runs on (`THEOREM_VECTORS_ARCHITECTURE.md`
§11.3): the string form of `compareBytes`, one place, like its byte form. -/
def compareRepr (a b : String) : Bool := a == b

/-- The `.ok` side of a run's result, matched outside the term (§11.2).
The stage-7 `.runOk` run-body builder calls it. -/
def runProbeOk {ε α σ : Type} (r : Except ε (α × σ)) : Option (α × σ) :=
  match r with
  | .ok p => some p
  | .error _ => none

/-- The `.error` side of a run's result, matched outside the term (§11.2).
The stage-7 `.runError` run-body builder calls it. -/
def runProbeError {ε α σ : Type} (r : Except ε (α × σ)) : Option ε :=
  match r with
  | .error e => some e
  | .ok _ => none

/-! ## The wire codec of one input (§9.1) -/

/-- The byte codec of one input value (`THEOREM_VECTORS_ARCHITECTURE.md` §9.1). Every
input type has one, because every input crosses the byte boundary twice:
serialized into a candidate, decoded inside `check` and `run`.

`default` is the base searcher's candidate value (§9.4), `none` when the
type has no total default. `Fin n` is why the field exists: its default
`⟨0, _⟩` needs `0 < n`, which an `Inhabited` instance cannot carry (there
is no `NeZero (3 * slotsPerEpoch)` to synthesize), and the codec's own
`n` pattern match can. -/
class ScalarCodec (T : Type) where
  encode : T → ByteArray
  decode : ByteArray → Option T
  /-- The `default` the base searcher serializes, when the type has one. -/
  default : Option T := none

instance {T : Type} [r : SSZRepr T] [Inhabited T] : ScalarCodec T where
  encode := SizzLean.SSZ.serialize
  decode := fun b =>
    -- the strict read (§9.3): the shape decode reports the bytes it
    -- consumed, and a record whose side file the type does not fill
    -- exactly is corrupt
    match SizzLean.Spec.SSZType.deserialize r.shape b with
    | .ok (y, n) => if n == b.size then some (r.fromRepr y) else none
    | .error _ => none
  default := some Inhabited.default

/-- The little-endian `uintN 64` read of eight bytes, `none` when the byte
string is not exactly eight wide. A wider string would decode by its low
bytes and hide a corrupt record from the read-back check (§9.3). -/
private def uint64OfBytesLE (b : ByteArray) : Option UInt64 :=
  if b.size != 8 then none
  else
    let byte (i : Nat) : UInt64 :=
      if h : i < b.size then UInt64.ofNat (b.get i h).toNat else 0
    some <| (List.range 8).foldl (fun acc i =>
      acc ||| (byte i <<< UInt64.ofNat (8 * i))) 0

/-- The little-endian `uintN 64` write of a `UInt64`. -/
def uint64BytesLE (v : UInt64) : ByteArray :=
  ByteArray.mk <| (List.range 8).toArray.map fun i =>
    UInt8.ofNat ((v >>> UInt64.ofNat (8 * i)).toNat % 256)

/-- The decode of one input from the probe's byte array: the precompiled
face of the byte boundary (§9.1, §9.3). A missing slice or a failed decode
answers `none`, and the check reads that as `false` (§9.3). -/
def decodeInput {T : Type} [ScalarCodec T] (bytes : Array ByteArray)
    (i : Nat) : Option T :=
  match bytes[i]? with
  | some b => ScalarCodec.decode b
  | none => none

/-- `Fin n` uses the same scalar family §9.4's bit-vector searcher puts it
in: the `uintN 64` little-endian encoding of `Fin.val`. `SSZRepr (Fin n)`
cannot exist, because a total decode would have to turn every byte string
into a value below `n`; a value at or above `n` is a corrupt record, so the
decode answers `none` and the check reads that as `false` (§9.3). -/
instance {n : Nat} : ScalarCodec (Fin n) where
  encode x := uint64BytesLE (UInt64.ofNat x.val)
  decode b := do
    let v ← uint64OfBytesLE b
    match n with
    | 0 => none
    | k + 1 =>
      if h : v.toNat < k + 1 then some ⟨v.toNat, h⟩ else none
  default :=
    match n with
    | 0 => none
    | k + 1 => some ⟨0, Nat.succ_pos k⟩

/-! ## The draw and the shrink (§9.4, §9.6) -/

/-- One drawn input's wire bytes (§9.4): the `SampleableExt` draw at this
position's seed, serialized. `emptyBytes` when the draw failed or the
strict decode would refuse the value, so a failed draw is an honest
no-candidate rather than a corrupt one (§9.3). -/
def sampleOne {T : Type} [ScalarCodec T] [Plausible.SampleableExt T]
    (seed size : Nat) : ByteArray :=
  match runDrawPure seed size (Plausible.SampleableExt.interpSample T) with
  | some x => ScalarCodec.encode x
  | none => emptyBytes

/-- The shrink candidates one container input contributes (§9.6): one
`shrinkShape` step on the value's shape representation, serialized, the
other inputs' bytes unchanged. A corrupt entry decodes to nothing and
contributes no candidate (§9.3). -/
def shrinkReplace {T : Type} [ScalarCodec T] (r : SSZRepr T)
    (bytes : Array ByteArray) (i : Nat) : Array (Array ByteArray) :=
  match bytes[i]? with
  | some b =>
    match ScalarCodec.decode b with
    | none => #[]
    | some x =>
      ((shrinkShape (@SSZRepr.shape T r) (r.toRepr x)).toArray.map fun p =>
          ScalarCodec.encode (r.fromRepr p)).map fun b' =>
        if h2 : i < bytes.size then bytes.set (Fin.mk i h2) b' else bytes
  | none => #[]

/-! ## What one run produced (§5.5) -/

/-- What one probe run produced (`THEOREM_VECTORS_ARCHITECTURE.md` §5.5, extended). All
values cross the boundary as SSZ bytes; the literals and the optional roots
are the record layer's (§12.2) answer to "scalar or container" and to a
`Nat`-typed output with no SSZ root. -/
structure ProbeResult where
  /-- `f x`, or the bound's decimal literal, serialized. -/
  output   : ByteArray
  /-- `e x`, serialized; empty for `.bound`. -/
  expected : ByteArray
  /-- `f x == e x`, or the bound holds. -/
  agree    : Bool
  /-- The output's literal, when its type carries `ToString`. -/
  literal  : Option String
  /-- The inputs' literals, in binder order, where the type carries
  `ToString`. -/
  inputLiterals : Array (Option String)
  /-- `hashTreeRoot` of each input, in binder order, where the type has an
  `SSZRepr`. -/
  inputRoots : Array (Option ByteArray)
  /-- `hashTreeRoot` of the output, when its type has an `SSZRepr`. -/
  outputRoot : Option ByteArray
  /-- The error's `repr`, for the `.runError` record's `error` value
  (`THEOREM_VECTORS_ARCHITECTURE.md` §12.2). The record layer needs the
  string, and no §5.5 field could hold it, so the structure gains the
  field (`IMPLEMENTATION_NOTES.md` records the deviation). The other
  shapes keep the default `none`. -/
  errorRepr : Option String := none

/-- The `.eq` run result: the byte comparison inside compiled code, so the
term computes each side once (§11.3). -/
def eqRunResult (out expected : ByteArray) (literal : Option String)
    (outputRoot : Option ByteArray) (inputLiterals : Array (Option String))
    (inputRoots : Array (Option ByteArray)) : Except String ProbeResult :=
  .ok { output := out, expected := expected, agree := compareBytes out expected,
        literal, inputLiterals, inputRoots, outputRoot }

/-- The `.bound` run result: the bound already decided inside the term, the
literal the only record (`THEOREM_VECTORS_ARCHITECTURE.md` §11.3). -/
def boundRunResult (out : ByteArray) (agree : Bool) (literal : Option String)
    (inputLiterals : Array (Option String))
    (inputRoots : Array (Option ByteArray)) : Except String ProbeResult :=
  .ok { output := out, expected := emptyBytes, agree, literal, inputLiterals,
        inputRoots, outputRoot := none }

/-- The `.runOk` run result: the recorded side's bytes against the
expected side's bytes, and the recorded side's root. The
comparison sits inside the assembler, so the term passes each
serialization once (§11.3). The literal stays `none`: this assembler
implements the `.runOk` row's rule, which records the recorded side as
an SSZ value with its root (§11.3, §12.2). The rule lives in this
assembler; a scalar-typed recorded side would need a new rule. -/
def runOkResult (out expected : ByteArray)
    (outputRoot : Option ByteArray) (inputLiterals : Array (Option String))
    (inputRoots : Array (Option ByteArray)) : Except String ProbeResult :=
  .ok { output := out, expected, agree := compareBytes out expected,
        literal := none, inputLiterals, inputRoots, outputRoot }

/-- The `.runOk` miss result: the compiled run rejected where the kernel
proved `.ok`. `agree` stays `false` on every path; comparing
`emptyBytes` against `expected` could agree, so the comparison never
runs. The rejection's repr, when the error type has a `Repr` instance,
goes in `errorRepr`, and the executor's disagreement print names it
(`THEOREM_VECTORS_ARCHITECTURE.md` §11.3, §18). -/
def runOkMiss (expected : ByteArray) (errorRepr : Option String)
    (inputLiterals : Array (Option String))
    (inputRoots : Array (Option ByteArray)) : Except String ProbeResult :=
  .ok { output := emptyBytes, expected, agree := false, literal := none,
        inputLiterals, inputRoots, outputRoot := none, errorRepr }

/-- The `.runError` run result: no output, the expected error's repr
bytes as the expected value, the comparison of the two repr strings
inside the assembler so each repr computes once (§11.3), and the actual
error's repr string as the record's `error` value (§12.2). -/
def runErrorResult (actual expected : String)
    (inputLiterals : Array (Option String))
    (inputRoots : Array (Option ByteArray)) : Except String ProbeResult :=
  .ok { output := emptyBytes, expected := String.toUTF8 expected,
        agree := compareRepr actual expected, literal := none,
        inputLiterals, inputRoots, outputRoot := none,
        errorRepr := some actual }

/-- The `.runError` miss result: the compiled run returned cleanly where
the kernel proved `.error`. `agree` stays `false` on every path, and
there is no error to repr (`THEOREM_VECTORS_ARCHITECTURE.md` §11.3). -/
def runErrorMiss (expected : String)
    (inputLiterals : Array (Option String))
    (inputRoots : Array (Option ByteArray)) : Except String ProbeResult :=
  .ok { output := emptyBytes, expected := String.toUTF8 expected,
        agree := false, literal := none, inputLiterals, inputRoots,
        outputRoot := none }

/-! ## The probe (§11.1) and its build-time description -/

/-- The compiled face of one statement at one preset (`THEOREM_VECTORS_ARCHITECTURE.md`
§11.1). -/
structure Probe where
  /-- `decide (P x)` for one disjunct, on decoded inputs. -/
  check  : (disjunctIndex : Nat) → Array ByteArray → Bool
  /-- Draw the container inputs; scalars come back as their zero
  encodings (§9.4). -/
  sample : (seed size : Nat) → Array ByteArray
  /-- Draw one input position alone (§9.4): the same bytes the `sample`
  face's array carries at that position, computed while the other
  positions' draws stay unevaluated. A position's draw depends only on
  the seed, the size, and the position (`mixHash seed (i + 1)` inside
  `sampleOne`), so the two faces agree byte for byte at every position.
  The built searcher reads its side containers through this face, so a
  statement whose state sits beside another container input never
  samples the state's draw (§9.9). -/
  sampleAt : (seed size pos : Nat) → ByteArray
  /-- Shrink candidates for the container inputs (§9.6). -/
  shrink : Array ByteArray → Array (Array ByteArray)
  /-- The container-reading subterms of one disjunct's hypotheses,
  evaluated at the candidate's bytes and serialized, in the walk's order
  (§9.4). -/
  reads  : (disjunctIndex : Nat) → Array ByteArray → Array ByteArray
  /-- Whether every guarded read inside the disjunct's read plan stays
  inside its collection at the candidate's bytes, one answer per plan
  entry (`§9.4`, the stage-4 outcome). A candidate the face answers
  `false` for never reaches `check`, so the plan's compiled reads never
  run past a drawn or shrunken list's end and no panic prints. The face
  evaluates the indexes and the lengths alone, which cannot panic. -/
  safe   : (disjunctIndex : Nat) → Array ByteArray → Array Bool
  /-- The author's manual terms, serialized, with their input positions
  (§9.4). -/
  manuals : Array (Nat × ByteArray)
  /-- The serialized `default` of every input, in binder order: the base
  searcher's candidate (§9.4). -/
  defaults : Array ByteArray
  /-- Run the named builder (an index into the binding's catalog) and
  serialize the state it produces; empty bytes when the statement has no
  state input for a builder to fill (§9.9). -/
  build  : (builder : Nat) → Knobs → ByteArray
  /-- `f x`, `e x`, the comparison, the roots. -/
  run    : Array ByteArray → Except String ProbeResult

/-- What the probe knows at build time and the record layer needs on disk
(§12.2): the binder names and the type of each input and of the output,
rendered with the preset's constants substituted, which is the form §12.2's
`type` field writes. Scalar-ness comes from the run's literals (§12.2
writes a literal where the type carries `ToString`, which `ProbeResult`
already answers). -/
structure ProbeInfo where
  /-- The binder names, in binder order. -/
  inputNames  : Array Name
  /-- Each input's type, rendered (§12.2): `Fin (3 * slotsPerEpoch)`,
  `EthCLSpecs.Gloas.BeaconState`. -/
  inputTypes  : Array String
  /-- The output's type, rendered. -/
  outputType  : String
  /-- The rendered statement parts the hint fingerprint folds (§9.8):
  the hypotheses and the conclusion's sides. The rendering substitutes
  the preset's constants, whose names are the same at every preset. -/
  stmtParts   : Array String := #[]
  /-- Each input's wire-description hash, one rendered decimal per
  input, empty for a scalar (§9.8). Unlike `stmtParts`, these move with
  the preset, because a derived container's caps are the preset's, so
  the fingerprint lives on the hint entry, per preset. -/
  shapeParts  : Array String := #[]
  deriving Inhabited

/-- Probe construction for a shape no run-body builder covers. The reader
reports an `.unsupported` statement before phase B, so the arms below keep
only the match's totality. -/
private def unsupportedShapeError {α : Type} (shape : Shape) : MetaM α :=
  throwError "theorem_vectors: the probe does not run the {shape.wire} shape"

/-! ## Small term builders -/

section TermBuilders

/-- `@Option.map α β f o`. -/
private def optMap (α β : Expr) (f o : Expr) : Expr :=
  mkAppN (.const ``Option.map [levelZero, levelZero]) #[α, β, f, o]

/-- `@Option.getD α o fallback`. -/
private def optGetD (α : Expr) (o fallback : Expr) : Expr :=
  mkAppN (.const ``Option.getD [levelZero]) #[α, o, fallback]

/-- `@Option.some α a`. -/
private def optSome (α a : Expr) : Expr :=
  mkAppN (.const ``Option.some [levelZero]) #[α, a]

/-- `@Option.none α`. -/
private def optNone (α : Expr) : Expr :=
  mkAppN (.const ``Option.none [levelZero]) #[α]

/-- `@cond α b a b'`. -/
private def mkCond (α b a b' : Expr) : Expr :=
  mkAppN (.const ``cond [levelOne]) #[α, b, a, b']

/-- `@Decidable.decide p inst`. -/
private def mkDecide (p inst : Expr) : Expr :=
  mkAppN (.const ``Decidable.decide []) #[p, inst]

/-- `[e₀, …]` as an `Array α`, through `List.toArray`. -/
private def mkArrayLit (α : Expr) (elems : Array Expr) : Expr :=
  let list := elems.foldr (fun e acc => mkAppN (.const ``List.cons [levelZero]) #[α, e, acc])
    (mkAppN (.const ``List.nil [levelZero]) #[α])
  mkAppN (.const ``List.toArray [levelZero]) #[α, list]

/-- `@ScalarCodec.encode T inst x`. -/
private def encodeCall (T inst x : Expr) : Expr :=
  mkAppN (.const ``ScalarCodec.encode []) #[T, inst, x]

/-- `@decodeInput T inst bytes i`: the precompiled decode of one input's
slice of the byte array, so the term carries no `Array`-access instance
terms (§11.2). -/
private def decodeCall (T inst bytes : Expr) (i : Expr) : Expr :=
  mkAppN (.const ``decodeInput []) #[T, inst, bytes, i]

/-- `@ToString.toString T inst x`. -/
private def toStringCall (T inst x : Expr) : Expr :=
  mkAppN (.const ``ToString.toString [levelZero]) #[T, inst, x]

/-- `String.toUTF8 s`. -/
private def toUtf8 (s : Expr) : Expr := mkApp (.const ``String.toUTF8 []) s

/-- The `i`-th projection of a right-associated `Prod` chain. -/
private partial def tupProj (xs : Expr) (i : Nat) : Expr :=
  if i == 0 then .proj `Prod 0 xs else tupProj (.proj `Prod 1 xs) (i - 1)

/-- The right-associated `Prod` type over `ts`, `PUnit` for none. -/
private def tupType (ts : Array Expr) : Expr :=
  ts.foldr (fun t acc => mkApp2 (.const ``Prod [levelZero, levelZero]) t acc) (.const ``PUnit [levelOne])

/-- The zero value of `tupType ts`, holding the `fᵢ` themselves. -/
private def tupVal (ts fs : Array Expr) : Expr :=
  let rec goTy (i : Nat) : Expr :=
    if i >= ts.size then .const ``PUnit [levelOne]
    else mkApp2 (.const ``Prod [levelZero, levelZero]) ts[i]! (goTy (i + 1))
  let rec goVal (i : Nat) : Expr :=
    if i >= fs.size then .const ``PUnit.unit [levelOne]
    else mkAppN (.const ``Prod.mk [levelZero, levelZero]) #[ts[i]!, goTy (i + 1), fs[i]!, goVal (i + 1)]
  goVal 0

/-- A two-argument constant function, the shape the `build` field keeps
when the statement has no state input for a builder to fill. -/
private def stub2 (aTy bTy res : Expr) : Expr :=
  .lam `_ aTy (.lam `_ bTy res .default) .default

/-- The instance fvar → binding-constant substitution over a finished term
(§11.2). The telescope's instance variables are the only fvars left in the
term once every value binder is abstracted. -/
private def substInstances (ctx : StatementCtx) (consts : Array Name)
    (term : Expr) : Expr :=
  term.replace fun e => match e with
    | .fvar id =>
      match ctx.instFvars.findIdx? (fun g => g.fvarId! == id) with
      | some i => if i < consts.size then some (mkConst consts[i]!) else none
      | none => none
    | _ => none

/-- Apply a fork constant to `args` across its leading instance binders
(§9.9): every instance-implicit binder whose type names one of the four
seams the binding fixes takes the binding's constant for this preset, and
the explicit `args` fill the explicit binders in order. `none` when the
constant does not resolve, a binder names an unknown seam, or the binders
outrun the arguments. This is how the framework half reaches the
catalog's builders (`Builders.Gloas.advanced`), constants that carry the
`[Preset] [Config]` binders the fork body runs under, plus
`[HasherTag]` or `[CryptoBackend]` where the constant's own body uses
them (the catalog's builders pin the hasher locally, so the binder
appears only where a body names it). The fork's `Const.slotsPerEpoch`,
which the grid's epoch boundary reads, is a zero-argument constant the
built searcher applies by hand, outside this walk. -/
-- `partial` because the walk instantiates each binder's body before it
-- descends (`instantiate1`), which hides the subterm the structural
-- recursion would need.
partial def applyAcrossInstances (binding : ForkBinding)
    (presetId : PresetId) (constName : Name) (args : Array Expr) :
    MetaM (Option Expr) := do
  let some ci := (← getEnv).find? constName | return none
  go constName ci.type #[] args.toList
where
  /-- The seam table: the binding constant one instance binder's type
  fixes, `none` for a binder the binding cannot fill. -/
  instConstOf (d : Expr) : Option Name :=
    match d.getAppFn with
    | .const c _ =>
      -- the per-fork classes carry the fork's namespace; the two framework
      -- seams are shared constants
      if c == binding.fork ++ `Preset then
        (Preset.constOf binding presetId .preset).toOption
      else if c == binding.fork ++ `Config then
        (Preset.constOf binding presetId .config).toOption
      else if c == ``EthCLLib.Spec.HasherTag then some binding.hasherTag
      else if c == ``EthCLLib.Spec.CryptoBackend then some binding.crypto
      else none
    | _ => none

  /-- The walk: fill each instance binder from the seam table, fill each
  explicit binder from `rest`, and apply what accumulated once the
  telescope ends. -/
  go (constName : Name) (t : Expr) (applied : Array Expr)
      (rest : List Expr) : MetaM (Option Expr) := do
    match t with
    | .forallE _ d b bi =>
      if bi.isInstImplicit then
        let some n := instConstOf d | return none
        -- the next binder's type may name this one; instantiate before
        -- the walk descends, so no loose bvar reaches the checks
        go constName (b.instantiate1 (mkConst n []))
          (applied.push (mkConst n [])) rest
      else if bi.isExplicit then
        match rest with
        | [] => return none
        | a :: more =>
          -- the argument must fit the binder, so a catalog constant
          -- with an argument type other than the caller's answers none
          -- and the caller's own error names it (§9.9)
          unless ← Meta.isDefEq d (← Meta.inferType a) do
            return none
          go constName (b.instantiate1 a) (applied.push a) more
      else
        -- an implicit-implicit binder is not a seam and not an
        -- application argument; the catalog's builders have none
        return none
    | _ =>
      if rest.isEmpty then pure (some (mkAppN (mkConst constName []) applied))
      else pure none

end TermBuilders

/-- The rendered form of a type expression, with the telescope's instance
variables replaced by the preset's constants (§10): the client-facing
spelling the record's `type` fields write (§12.2). -/
private def renderedType (ctx : StatementCtx) (consts : Array Name)
    (t : Expr) : MetaM String := do
  toString <$> Meta.ppExpr (substInstances ctx consts t)

/-- The unsafe evaluation of the probe term (`THEOREM_VECTORS_ARCHITECTURE.md` §11.2),
behind the same `implemented_by` shape `Command.lean` uses for the
binding. -/
private unsafe def evalProbeImpl (value : Expr) : MetaM Probe :=
  Lean.Meta.evalExpr Probe (.const ``EthCLLib.TheoremVectors.Probe []) value

/-- The opaque face of the probe evaluation. -/
@[implemented_by evalProbeImpl]
private opaque evalProbeCore (value : Expr) : MetaM Probe

/-- The `.eq` run body under the `xs` binder: serialize both sides at the
output's type, or, when the type has no `SSZRepr`, fall back to the UTF-8
bytes of the literal (`Nat`-typed outputs). Each side computes once, as
`eqRunResult`'s arguments (§11.3). `none` when the output type records no
way; the caller reports a skipped run, because the shape ran but the
record layer has no form for the answer. -/
private def eqRunBody (lhs rhs : Expr)
    (underXs : Expr → Expr) (outTy : Expr)
    (outRepr? : Option Expr) (outHash : Option (Expr × Expr))
    (outToString? : Option Expr)
    (inputLits inputRoots : Array Expr) : MetaM (Option Expr) := do
  let render (e : Expr) : MetaM (Option Expr) :=
    match outRepr? with
    | some inst =>
      pure (some (mkAppN (.const ``SizzLean.SSZ.serialize [])
        #[outTy, inst, underXs e]))
    | none =>
      match outToString? with
      | some inst => pure (some (toUtf8 (toStringCall outTy inst (underXs e))))
      | none => pure none
  let some outT ← render lhs | return none
  let some expT ← render rhs | return none
  let litT := match outToString? with
    | some inst =>
      optSome (.const ``String []) (toStringCall outTy inst (underXs lhs))
    | none => optNone (.const ``String [])
  let rootT :=
    match outRepr?, outHash with
    | some inst, some (h, hasher) =>
      optSome (.const ``ByteArray [])
        (mkAppN (.const ``SizzLean.SSZ.hashTreeRoot [])
          #[outTy, h, hasher, inst, underXs lhs])
    | _, _ => optNone (.const ``ByteArray [])
  pure (some (mkAppN (.const ``eqRunResult [])
    #[outT, expT, litT, rootT,
      mkArrayLit (mkApp (.const ``Option [levelZero]) (.const ``String []))
        inputLits,
      mkArrayLit (mkApp (.const ``Option [levelZero])
        (.const ``ByteArray [])) inputRoots]))

/-- The `.bound` run body under the `xs` binder: decide the comparison with
the instance built for it, and record the literal
(`THEOREM_VECTORS_ARCHITECTURE.md` §11.3). `none` when the literal has no
`ToString`, which the caller reports as a skipped run. The comparison and
its `Decidable` instance arrive prebuilt (`cmpDec`, `cmpExpr`); the bound
and its relation live inside them. -/
private def boundRunBody (lhs : Expr) (cmpDec cmpExpr : Expr)
    (underXs : Expr → Expr) (outTy : Expr)
    (outToString? : Option Expr)
    (inputLits inputRoots : Array Expr) : Option Expr :=
  match outToString? with
  | none => none
  | some outToString =>
    let cmpExpr := underXs cmpExpr
    let agree := mkDecide cmpExpr (underXs cmpDec)
    let lit := toStringCall outTy outToString (underXs lhs)
    some (mkAppN (.const ``boundRunResult [])
      #[toUtf8 lit, agree, optSome (.const ``String []) lit,
        mkArrayLit (mkApp (.const ``Option [levelZero]) (.const ``String []))
          inputLits,
        mkArrayLit (mkApp (.const ``Option [levelZero])
          (.const ``ByteArray [])) inputRoots])

/-- The `.iffTrue` run body under the `xs` binder (§11.3): `lhs` is the
function's `Bool` result, so the output byte is `lhs` itself; the expected
byte is `decide q`, carried by the `Decidable` instance the builder
synthesized (§8.4). -/
private def iffTrueRunBody (lhs q qDec : Expr)
    (underXs : Expr → Expr) (outToString : Expr)
    (outRepr? : Option Expr) (outHash : Option (Expr × Expr))
    (inputLits inputRoots : Array Expr) : Expr :=
  let boolTy := .const ``Bool []
  let outVal := underXs lhs
  let decideQ := mkDecide (underXs q) (underXs qDec)
  let lit := optSome (.const ``String []) (toStringCall boolTy outToString outVal)
  let root :=
    match outRepr?, outHash with
    | some inst, some (h, hasher) =>
      optSome (.const ``ByteArray [])
        (mkAppN (.const ``SizzLean.SSZ.hashTreeRoot [])
          #[boolTy, h, hasher, inst, outVal])
    | _, _ => optNone (.const ``ByteArray [])
  mkAppN (.const ``eqRunResult [])
    #[mkApp (.const ``boolBytes []) outVal,
      mkApp (.const ``boolBytes []) decideQ,
      lit, root,
      mkArrayLit (mkApp (.const ``Option [levelZero]) (.const ``String []))
        inputLits,
      mkArrayLit (mkApp (.const ``Option [levelZero])
        (.const ``ByteArray [])) inputRoots]
/-- The error and return types of one run action's `StateT σ (Except ε) α`
type, the reading both run bodies share (§11.3). `withReducible` unfolds a
reducible monad abbrev (`GloasRun`) and stops at the `StateT` spine, which
a full `whnf` would unfold away. A non-`StateT` type is a machinery error:
the reader's run matches fired on a `StateT.run` application. -/
private def runSpineOf (act : Expr) (wire : String) : MetaM (Expr × Expr) := do
  let .app (.app (.app (.const ``StateT _) _) m) retTy :=
    ← Meta.withReducible (Meta.whnf (← Meta.inferType act))
    | throwError "theorem_vectors: the {wire} action's type is not a \
        `StateT` (§11.3)"
  let .app (.const ``Except _) errTy := ← Meta.whnf m
    | throwError "theorem_vectors: the {wire} action's monad is not an \
        `Except` (§11.3)"
  pure (errTy, retTy)

/-- The `Except String ProbeResult` type the run bodies and the run-body
assembly answer (`THEOREM_VECTORS_ARCHITECTURE.md` §11.3). One helper,
so the three build sites cannot drift. -/
private def probeResultExTy : Expr :=
  mkAppN (.const ``Except [levelZero, levelZero]) #[.const ``String [],
    .const ``EthCLLib.TheoremVectors.ProbeResult []]

/-- The recorded side of a `.runOk` run's result pair when the run's
return value is the state (`THEOREM_VECTORS_ARCHITECTURE.md` §11.3): `ty`
and `repr` are the type and the `SSZRepr` instance the value's bytes
record at, and `viewH?` is the box's hasher type and instance, the pair
the `.view` read takes when the value is a boxed state. -/
private structure RunOkValueSide where
  /-- The type the bytes record at: the container under the box. -/
  ty     : Expr
  /-- The `SSZRepr` instance for `ty`. -/
  repr   : Expr
  /-- The box's hasher type and its `SizzLean.Hasher` instance, present
  when the value is a boxed state. -/
  viewH? : Option (Expr × Expr)

/-- The value pick of a `.runOk` record (`THEOREM_VECTORS_ARCHITECTURE.md`
§11.3): `some` when the run's return type names the binding's state
container, `none` when the record keeps the store. The value-style
mutators are the `some` shape. `increaseBalance` takes the state it
writes as an argument and returns the mutated one. The `preState`
bystander its theorem threads records nothing the theorem asserts. A
`Unit`-return step's mutation lives on the store, so the store pick
carries that mutation.

The test whnfs the return type first, because the box wrapping hides the
container: the fork's `State` is a reducible abbrev over
`SSZ.Box HasherTag.H BeaconState`, so the `SSZ.Box` application must
surface before `isStateType` reads the bare container constant. A boxed
value records the container's bytes. The box carries no `SSZRepr`
instance of its own, so the recorded side reads the value through the
box's `.view`. The bytes record at the container's type and instance,
the type a client replaying the function holds. The test strips one
`SSZ.Box` layer, and a doubly boxed return, or a state container behind
a non-reducible alias, answers `none` and falls back to the store pick. -/
private def runOkValueSide? (binding : ForkBinding) (retTy : Expr) :
    MetaM (Option RunOkValueSide) := do
  let w ← Meta.withReducible (Meta.whnf retTy)
  -- the box strip: one `SSZ.Box` layer off, whose first argument is the
  -- box's hasher type and whose second is the container under it
  let (bare, boxH?) :=
    match w.getAppFn, w.getAppArgs with
    | .const c _, args =>
      if c == ``SizzLean.Cache.SSZ.Box && args.size ≥ 2 then
        (args[1]!, some args[0]!)
      else (w, none)
    | _, _ => (w, none)
  unless isStateType binding bare do return none
  let reprRes? ←
    (try some <$> Meta.synthInstance (mkApp (.const ``SizzLean.SSZRepr []) bare)
      catch _ => pure none)
  let some repr := reprRes?
    | throwError "theorem_vectors: the run's return value names the state \
        container, but its type carries no `SSZRepr` instance, so the \
        value pick has nothing to record (§11.3)"
  match boxH? with
  | none => pure (some { ty := bare, repr, viewH? := none })
  | some hTy =>
    let hasherRes? ←
      (try some <$> Meta.synthInstance (mkApp (.const ``SizzLean.Hasher []) hTy)
        catch _ => pure none)
    let some hasher := hasherRes?
      | throwError "theorem_vectors: the boxed state value's hasher \
          instance did not resolve, so the box's `.view` read has no \
          `Hasher` instance (§11.3)"
    pure (some { ty := bare, repr, viewH? := some (hTy, hasher) })

/-- The `.runOk` run body under the `xs` binder (`THEOREM_VECTORS_ARCHITECTURE.md`
§11.3): `runPure` (`EthCLLib.Proofs.runPure`) evaluates the run on the
plain pre-state, the precompiled `runProbeOk` extracts the pair outside
the term (§11.2), and the recorded side's bytes go against the expected
side's bytes, with the recorded side's root under the binding's hasher
(§11.4). When `valSide?` is `some`, the recorded side is the run's return
value, the pair's `.1` read through the box when the value is the fork's
boxed `State`. The expected side is the conclusion's `ret` term: the
value-style mutators' theorems state the mutated state as the value and
leave the threaded store a bystander. When `valSide?` is `none`, the
recorded side is the pair's `.2`, the store, and the expected side is the
conclusion's `post` term, both at the pre-state's type. Each
serialization sits at one argument position, and `runOkResult` computes
the comparison from its own arguments, so the recorded side serializes
once per run (§11.3). A rejected run, which the kernel excluded for the
witness, takes `runOkMiss`: it keeps `agree := false` and carries the
rejection's repr in `errorRepr` when the error type has a `Repr`
instance, and the executor's disagreement check prints that repr beside
the two byte values (§11.3, §18). Without a `Repr` instance,
`errorRepr` stays `none`.

`preTy` and `preRepr` are the pre-state's type and its `SSZRepr`
instance, the ones the caller synthesized for the shape's `pre`
expression. `tag` is the binding's hasher-tag constant, the `HasherTag`
instance `runPure` takes. -/
private def runOkRunBody (act pre ret post : Expr) (underXs : Expr → Expr)
    (tag preTy preRepr : Expr) (valSide? : Option RunOkValueSide)
    (hashPair? : Option (Expr × Expr))
    (inputLits inputRoots : Array Expr) : MetaM Expr := do
  let (errTy, retTy) ← runSpineOf (underXs act) ".runOk"
  -- `runPure`'s spine: `{T ε α} [SSZRepr T] [HasherTag] act v`. The
  -- `SSZRepr` instance is the pre-state's, which exists because the
  -- pre-state crossed the byte boundary (§9.1)
  let runPureApp := mkAppN (.const ``EthCLLib.Proofs.runPure [])
    #[preTy, errTy, retTy, preRepr, tag, underXs act, underXs pre]
  let exTy := probeResultExTy
  let arrLits := mkArrayLit (mkApp (.const ``Option [levelZero])
    (.const ``String [])) inputLits
  let arrRoots := mkArrayLit (mkApp (.const ``Option [levelZero])
    (.const ``ByteArray [])) inputRoots
  -- the sides the run compares (§11.3): the value pick records and
  -- expects at the value's type, reading each side through the box; the
  -- store pick keeps the pre-state's type
  let (recTy, recRepr, recOf, expectedTerm) :=
    match valSide? with
    | some v =>
      -- the box's `.view` read turns a boxed value into the plain
      -- container; on an unboxed one it is the identity
      let viewOf e :=
        match v.viewH? with
        | none => e
        | some (hTy, hasher) =>
          mkAppN (.const ``SizzLean.Cache.SSZ.Box.view [])
            #[hTy, v.ty, hasher, v.repr, e]
      (v.ty, v.repr, viewOf, ret)
    | none => (preTy, preRepr, fun e => e, post)
  let expSer := mkAppN (.const ``SizzLean.SSZ.serialize [])
    #[recTy, recRepr, recOf (underXs expectedTerm)]
  let pairTy := mkApp2 (.const ``Prod [levelZero, levelZero]) retTy preTy
  -- the miss branch carries the rejection's repr when the error type
  -- has a `Repr` instance; without one it answers `none`
  let errRepr? ←
    (try some <$> Meta.synthInstance (mkApp (.const ``Repr [levelZero]) errTy)
      catch _ => pure none)
  Meta.withLocalDeclD `runPair pairTy fun p => do
    -- the recorded side: the value pick reads the pair's `.1`, the run's
    -- return value; the store pick reads the pair's `.2`, the store
    let recorded := recOf
      (match valSide? with
        | some _ => .proj `Prod 0 p
        | none => .proj `Prod 1 p)
    let ser := mkAppN (.const ``SizzLean.SSZ.serialize [])
      #[recTy, recRepr, recorded]
    let root :=
      match hashPair? with
      | some (h, hasher) =>
        optSome (.const ``ByteArray [])
          (mkAppN (.const ``SizzLean.SSZ.hashTreeRoot [])
            #[recTy, h, hasher, recRepr, recorded])
      | none => optNone (.const ``ByteArray [])
    let okRes := mkAppN (.const ``runOkResult [])
      #[ser, expSer, root, arrLits, arrRoots]
    let missBase := mkAppN (.const ``runOkMiss [])
      #[expSer, optNone (.const ``String []), arrLits, arrRoots]
    let missRes ←
      match errRepr? with
      | none => pure missBase
      | some errRepr =>
        Meta.withLocalDeclD `runErr errTy fun e => do
          let missErr := mkAppN (.const ``runOkMiss [])
            #[expSer,
              optSome (.const ``String [])
                (mkAppN (.const ``reprStr [levelZero]) #[errTy, errRepr, e]),
              arrLits, arrRoots]
          -- the fallback re-applies `runPureApp`, so a rejected run
          -- evaluates the transition twice; the executor turns a miss
          -- into the build error, so the extra run never lands in a
          -- passing record (§11.3, §18)
          pure (optGetD exTy
            (optMap errTy exTy
              (← Meta.mkLambdaFVars #[e] missErr)
              (mkAppN (.const ``runProbeError []) #[errTy, retTy, preTy,
                runPureApp]))
            missBase)
    pure (optGetD exTy
      (optMap pairTy exTy
        (← Meta.mkLambdaFVars #[p] okRes)
        (mkAppN (.const ``runProbeOk []) #[errTy, retTy, preTy, runPureApp]))
      missRes)

/-- The `.runError` run body under the `xs` binder (§11.3): the same
`runPure` evaluation, with `runProbeError` extracting the error outside
the term (§11.2). The actual error's `reprStr` and the expected error's
`reprStr` each compute once, `runErrorResult` compares them and records
the actual one, and the expected repr's UTF-8 bytes are the expected
value (§12.2). A run that returned cleanly instead, which the kernel
excluded, takes `runErrorMiss`: `agree := false`, with no error to repr.
Answers a skip reason when the error type has no `Repr` instance. -/
private def runErrorRunBody (act pre err : Expr) (underXs : Expr → Expr)
    (tag preTy preRepr : Expr)
    (inputLits inputRoots : Array Expr) : MetaM (Except String Expr) := do
  let (errTy, retTy) ← runSpineOf (underXs act) ".runError"
  let reprRes? ←
    (try some <$> Meta.synthInstance (mkApp (.const ``Repr [levelZero]) errTy)
      catch _ => pure none)
  let some errRepr := reprRes?
    | return .error "the `.runError` conclusion's error type has no `Repr` \
        instance, so there is nothing to record"
  let runPureApp := mkAppN (.const ``EthCLLib.Proofs.runPure [])
    #[preTy, errTy, retTy, preRepr, tag, underXs act, underXs pre]
  let exTy := probeResultExTy
  let arrLits := mkArrayLit (mkApp (.const ``Option [levelZero])
    (.const ``String [])) inputLits
  let arrRoots := mkArrayLit (mkApp (.const ``Option [levelZero])
    (.const ``ByteArray [])) inputRoots
  Meta.withLocalDeclD `runErr errTy fun e => do
    -- each repr string computes once; `runErrorResult` compares its own
    -- arguments, records the actual one as the `error` value, and writes
    -- the expected one's UTF-8 bytes as the expected value (§11.3, §12.2)
    let actualRepr := mkAppN (.const ``reprStr [levelZero]) #[errTy, errRepr, e]
    let expectedRepr :=
      mkAppN (.const ``reprStr [levelZero]) #[errTy, errRepr, underXs err]
    let okRes := mkAppN (.const ``runErrorResult [])
      #[actualRepr, expectedRepr, arrLits, arrRoots]
    let missRes := mkAppN (.const ``runErrorMiss [])
      #[expectedRepr, arrLits, arrRoots]
    pure (.ok (optGetD exTy
      (optMap errTy exTy
        (← Meta.mkLambdaFVars #[e] okRes)
        (mkAppN (.const ``runProbeError []) #[errTy, retTy, preTy, runPureApp]))
      missRes))

/-! ## The container reads (§9.4) -/


/-- The pre-order read walk over one hypothesis (§9.4). A node that
mentions a container input stops the descent when its type carries a
scalar literal form: it joins the plan, and its compiled value takes its
place in the residual formula. A node that mentions no container input
stays in the residual formula for the solver. The walk never enters a
lambda or a `let` body, because a term under a binder has no runtime
value to evaluate at. Both the probe's `reads` face and the random
searcher's substitution walk this same function, which is what keeps the
serialized reads aligned with the subterms they replace. -/
private partial def collectReads (containerIds : Array FVarId) (e : Expr)
    (acc : Array Expr) : MetaM (Array Expr) := do
  if !(collectFVarIds e #[]).any containerIds.contains then
    return acc
  match ← scalarKind (← Meta.inferType e) with
  | some _ => return acc.push e
  | none =>
    match e with
    | .app f a =>
      collectReads containerIds a (← collectReads containerIds f acc)
    | .mdata _ b => collectReads containerIds b acc
    | .proj _ _ b => collectReads containerIds b acc
    | _ => return acc

/-- The reads of one disjunct's hypotheses, in walk order (§9.4). -/
def containerReads (containerIds : Array FVarId) (hyps : Array Expr) :
    MetaM (Array Expr) :=
  hyps.foldlM (fun acc h => collectReads containerIds (Prepare.zeta h) acc) #[]

/-- The wire bytes one read's value takes, at the read's scalar type
(§9.4). `none` when the type carries no scalar literal form, which the
walk never produces. A `Nat` read travels through `UInt64.ofNat`, so a
value at or above `2 ^ 64` truncates; the check evaluates the real
value, and a misgrounded point's candidate fails it (§9.3). -/
private def readEncodeTerm (ty : Expr) (v : Expr) : MetaM (Option Expr) := do
  match ← scalarKind ty with
  | some .bool => pure (some (mkApp (.const ``boolBytes []) v))
  | some .nat => pure (some (mkApp (.const ``uint64BytesLE [])
      (mkApp (.const ``UInt64.ofNat []) v)))
  | some (.uint 64) => pure (some (mkApp (.const ``uint64BytesLE []) v))
  | some (.uint 32) => pure (some (mkAppN (.const ``leBytes [])
      #[mkRawNatLit 4, mkApp (.const ``UInt32.toNat []) v]))
  | some (.uint 16) => pure (some (mkAppN (.const ``leBytes [])
      #[mkRawNatLit 2, mkApp (.const ``UInt16.toNat []) v]))
  | some (.uint 8) => pure (some (mkAppN (.const ``leBytes [])
      #[mkRawNatLit 1, mkApp (.const ``UInt8.toNat []) v]))
  | some (.fin n) => pure (some (mkAppN (.const ``leBytes [])
      #[mkRawNatLit 8, mkAppN (.const ``Fin.val []) #[n, v]]))
  | _ => pure none

/-- The wire description's hash, for the hint fingerprint (§9.8): a new
field in a container changes its `SSZType` description, which changes
this hash, and that is what marks a fork's random hints stale after a
spec change. -/
def shapeHash (T : Type) [SizzLean.SSZRepr T] : UInt64 :=
  hash (SizzLean.SSZRepr.shape (T := T))

/-- Compiled evaluation of one input's shape hash, for the fingerprint. -/
private unsafe def evalShapeHashImpl (e : Expr) : MetaM UInt64 :=
  Lean.Meta.evalExpr UInt64 (.const ``UInt64 []) e

@[implemented_by evalShapeHashImpl]
private opaque evalShapeHashOp (e : Expr) : MetaM UInt64

/-! ## The read bounds (§9.4, the stage-4 outcome) -/

/-- The compiled term for a collection's element count, `none` when the
type carries none. The corpus's collections are `SSZList` / `Bitlist`
subtypes over `Array`, plus the plain `Array` and `List` themselves; the
`Subtype` arm reads `Array.size` through `Subtype.val`. -/
private def lengthTermOf (coll : Expr) : MetaM (Option Expr) := do
  let ty ← Meta.withReducible (Meta.whnf (← Meta.inferType coll))
  match ty with
  | .app (.const ``Array _) elem =>
    pure (some (mkAppN (.const ``Array.size [levelZero]) #[elem, coll]))
  | .app (.const ``List _) elem =>
    pure (some (mkAppN (.const ``List.length [levelZero]) #[elem, coll]))
  | .app (.app (.const ``Subtype _) A) _ =>
    match ← Meta.withReducible (Meta.whnf A) with
    | .app (.const ``Array _) elem =>
      -- the buffer projection of the subtype, read structurally: a raw
      -- `Subtype.val` application is sensitive to the projection's
      -- binder order, and `.proj` is not
      let val : Expr := .proj `Subtype 0 coll
      pure (some (mkAppN (.const ``Array.size [levelZero]) #[elem, val]))
    | _ => pure none
  | _ => pure none

/-- The guarded reads one plan entry makes: every read whose value comes
out of an indexed collection, paired with its collection and index
(`§9.4`'s `!`-reads, the reads whose compiled evaluation can run past a
drawn list's end). Only the panic-capable reads gate: a `!`-read's
compiled form is `GetElem?.getElem!`, whose `none` branch panics; a
`?`-read answers `none` and a proof-carrying `xs[i]'h` read cannot run
past the end, so neither gates. An
index must be a `Nat`-typed term, which is what the `Nat.lt` bound
compiles against; an index of another type leaves that read ungated.

The walk collects in post-order, innermost first, so the safe term can
nest the inner reads' checks inside the outer ones: an outer read whose
index contains an inner read only evaluates its index when the inner
read's check passed. -/
private partial def detectReadBounds (r : Expr)
    (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
  let acc ←
    match r with
    | .app f a => detectReadBounds a (← detectReadBounds f acc)
    | .mdata _ b => detectReadBounds b acc
    | .proj _ _ b => detectReadBounds b acc
    | _ => pure acc
  let guarded :=
    match r.getAppFn with
    | .const c _ => c == ``GetElem?.getElem!
    | _ => false
  if guarded then
    let args := r.getAppArgs
    if args.size ≥ 2 then
      let coll := args[args.size - 2]!
      let idx := args.back!
      let idxTy ← Meta.withReducible (Meta.whnf (← Meta.inferType idx))
      if idxTy == .const ``Nat [] then
        if (← lengthTermOf coll).isSome then
          return acc.push (coll, idx)
  return acc

/-- The read bound of one plan entry, one `Bool` term over the checks of
all its guarded reads (`THEOREM_VECTORS_ARCHITECTURE.md` §9.4, the stage-4 outcome).
The checks fold innermost first, and each fold step selects the next
check through a lambda and applies it at once, so the accumulator is
always a `Bool` and the compiled term evaluates an outer read's index
only when the inner reads' checks passed. That matters because the
compiler evaluates arguments strictly: an outer index that contains an
inner read must not run before the inner read's check answered, or the
panic the gate was built to prevent would move inside the face. -/
private def entrySafeTerm (checks : Array Expr) : Expr :=
  let unitTy := .const ``Unit []
  -- a raw, non-dependent arrow: the bound name is never referenced
  let funTy := .forallE `_u unitTy (.const ``Bool []) .default
  let step (c acc : Expr) : Expr :=
    -- `cond` picks one of the two lambdas, and applying the picked one
    -- evaluates only that side's body
    mkApp (mkCond funTy c
      (.lam `_t unitTy acc .default)
      (.lam `_f unitTy (mkConst ``Bool.false) .default)) (mkConst ``Unit.unit)
  checks.foldr step (mkConst ``Bool.true)

/-- The conclusion's sides, the terms a changed conclusion changes
(§9.8's fingerprint names the statement). -/
def shapeTermsOf : Shape → Array Expr
  | .eq a b => #[a, b]
  | .iffTrue a b => #[a, b]
  | .bound a _ b => #[a, b]
  | .runOk a p r p2 => #[a, p, r, p2]
  | .runError a p e => #[a, p, e]
  | .unsupported _ => #[]

/-- Build and evaluate the probe for one statement at one preset (§11.2).
Runs inside the reader's telescope scope: the statement's expressions and
`ctx`'s free variables are telescope-local. `manualTerms` pairs each
author-written manual term with its input position, the terms still
holding the telescope's instance variables.

Returns the build-time description the record layer reads, plus the
evaluated probe. An `.error` answer is a skip reason, a fact about the
theorem or the shape (`ScalarCodec`, `ToString`, or the render form
missing); a thrown error is machinery (`§18`: the probe's own failures are
never facts about the theorem). -/
def Probe.ofStatement (binding : ForkBinding) (presetId : PresetId)
    (ctx : StatementCtx) (disjuncts : Array Disjunct)
    (manualTerms : Array (Nat × Expr)) :
    MetaM (Except String (ProbeInfo × Probe)) := do
  let stmt := ctx.stmt
  let shape := stmt.shape
  unless shape matches .eq .. || shape matches .bound .. ||
      shape matches .iffTrue .. || shape matches .runOk .. ||
      shape matches .runError .. do
    return .error s!"the probe does not run the {shape.wire} shape"
  unless stmt.typeBinders.isEmpty do
    return .error s!"the command cannot fix the type parameters \
      {stmt.typeBinders} yet"
  -- §10: the instance constants this preset fixes, substituted for the
  -- telescope's instance variables at the end
  let instConsts ← ctx.stmt.instances.mapM fun (_, kind) =>
    match Preset.constOf binding presetId kind with
    | .ok c => pure c
    | .error e => throwError e
  -- synthesize what the term needs while the telescope's variables are in
  -- context; every result still mentions them and is substituted at the end
  let inputTys ← ctx.inputFvars.mapM (Meta.inferType ·)
  let codecInsts? ← inputTys.mapM fun t =>
    (try some <$> Meta.synthInstance (mkApp (.const ``ScalarCodec []) t)
      catch _ => pure none)
  let toStringInsts? ← inputTys.mapM fun t =>
    (try some <$> Meta.synthInstance (mkApp (.const ``ToString [levelZero]) t)
      catch _ => pure none)
  let rootInsts? ← inputTys.mapM fun t =>
    (try some <$> Meta.synthInstance (mkApp (.const ``SizzLean.SSZRepr []) t)
      catch _ => pure none)
  -- an input without a codec cannot cross the byte boundary, which is a
  -- scope miss (§1.2), reported as a skip
  let some codecInsts ← pure (codecInsts?.mapM id)
    | do
      let i? := codecInsts?.findIdx? Option.isNone
      let name : Name :=
        match i? with
        | some i => match stmt.inputs[i]? with
          | some inp => inp.name
          | none => Name.anonymous
        | none => Name.anonymous
      return .error s!"input {name} has no wire codec; the theorem is \
        out of scope (§1.2)"
  -- §11.4: the roots come from the binding's hasher, whether or not the
  -- theorem binds a `[HasherTag]`. The binding's tag is a runtime name, so
  -- the environment check below turns a misspelling into a machinery
  -- error; the elaborator checks the double-backtick framework names.
  unless (← getEnv).contains binding.hasherTag do
    throwError "theorem_vectors: the binding's hasher \
      `{binding.hasherTag}` does not resolve (§11.4)"
  let tag : Expr := .const binding.hasherTag []
  let h : Expr := mkApp (.const ``EthCLLib.Spec.HasherTag.H []) tag
  let hasher? : Option Expr ←
    (try some <$> Meta.synthInstance (mkApp (.const ``SizzLean.Hasher []) h)
      catch _ => pure none)
  let hashPair? : Option (Expr × Expr) := hasher?.map fun i => (h, i)
  -- the shape's sides and the output type. The run shapes' sides are the
  -- run's parts, and the default "output type" is the pre-state's:
  -- `.runOk` records the post-state at that type unless the run's return
  -- value is the state. A state-typed return value records at the
  -- value's own type. `.runError` records no output at all (§12.1), so
  -- the field goes unused there
  let outTerm ← match shape with
    | .eq lhs _ => pure lhs
    | .bound lhs _ _ => pure lhs
    | .iffTrue lhs _ => pure lhs
    | .runOk _ pre _ _ => pure pre
    | .runError _ pre _ => pure pre
    | _ => unsupportedShapeError shape
  -- the `.iffTrue` right side needs `Decidable` for its decision (§11.3).
  -- The side's `let`s zeta away first: a `Decidable` cannot be synthesized
  -- for a proposition hidden behind a scratch `let`
  -- (`canBuilderCoverBid_iff`'s right side carries three). The left side is
  -- the function's own `Bool` and needs none.
  let iffDecs? : Option (Expr × Expr × Expr) ← match shape with
    | .iffTrue lhs0 q0 => do
      let lhs := Prepare.zeta lhs0
      let q := Prepare.zeta q0
      let qDec? ← (try some <$> Meta.synthInstance (mkApp (.const ``Decidable []) q)
        catch _ => pure none)
      match qDec? with
      | some qDec => pure (some (lhs, q, qDec))
      | none =>
        return .error "the `.iffTrue` conclusion has no `Decidable` \
          instance for its right side"
    | _ => pure none
  let outTy ←
    if shape matches .iffTrue .. then
      pure (.const ``Bool [])
    else
      Meta.inferType outTerm
  let outToString? ←
    (try some <$> Meta.synthInstance (mkApp (.const ``ToString [levelZero]) outTy)
      catch _ => pure none)
  let outRepr? ←
    (try some <$> Meta.synthInstance (mkApp (.const ``SizzLean.SSZRepr []) outTy)
      catch _ => pure none)
  -- the `.bound` comparison needs its own `Decidable`, over the statement's
  -- own relation (§11.3: `lhs rel b` holds), with the type's `LT` / `LE`
  -- instance synthesized, not `Nat`'s
  let cmp? : Option (Expr × Expr) ← match shape with
    | .bound lhs rel b => do
      let relCls := match rel with
        | .lt => .const ``LT [levelZero]
        | .le => .const ``LE [levelZero]
      let relInst? ← (try some <$> Meta.synthInstance (mkApp relCls outTy)
        catch _ => pure none)
      let some relInst := relInst? | pure none
      let cmp := match rel with
        | .lt => mkAppN (.const ``LT.lt [levelZero]) #[outTy, relInst, lhs, b]
        | .le => mkAppN (.const ``LE.le [levelZero]) #[outTy, relInst, lhs, b]
      match ← (try some <$> Meta.synthInstance (mkApp (.const ``Decidable []) cmp)
          catch _ => pure none) with
      | some dec => pure (some (cmp, dec))
      | none => pure none
    | _ => pure none
  -- a dependent input type would break the flat `Prod` decode; the corpus
  -- has none, and the skip says so plainly
  let inputIds := ctx.inputFvars.map (fun f => f.fvarId!)
  for j in [0:inputTys.size] do
    if (inputIds.take j).any (fun id => inputTys[j]!.containsFVar id) then
      return .error s!"input {j} has a type that depends on an earlier \
        input, which the flat decode cannot express"

  Meta.withLocalDeclD `bytes (mkApp (.const ``Array [levelZero]) (.const ``ByteArray [])) fun bytes => do
    -- the decode chain: `fun bytes => bind (codec bytes 0) fun x₀ => … some tuple`
    let tupTy := tupType inputTys
    let mut cur := optSome tupTy (tupVal inputTys ctx.inputFvars)
    for i in [0:ctx.inputFvars.size] do
      let j := ctx.inputFvars.size - 1 - i
      let lam ← Meta.mkLambdaFVars #[ctx.inputFvars[j]!] cur
      let di := decodeCall inputTys[j]! codecInsts[j]! bytes (mkRawNatLit j)
      cur := mkAppN (.const ``Option.bind [levelZero, levelZero]) #[inputTys[j]!, tupTy, di, lam]
    let decoder ← Meta.mkLambdaFVars #[bytes] cur
    let decoderApp := mkApp decoder bytes

    Meta.withLocalDeclD `xs tupTy fun xs => do
      let projOfIdx (i : Nat) : Expr := tupProj xs i
      let underXs (e : Expr) : Expr :=
        e.replace fun s => match s with
          | .fvar id =>
            ctx.inputFvars.findIdx? (fun g => g.fvarId! == id)
              |>.map (fun i => projOfIdx i)
          | _ => none
      -- the disjunct lambdas: `fun x₀ … xₙ => decide conj`
      let disjunctLams ← disjuncts.mapM fun d =>
        Meta.mkLambdaFVars ctx.inputFvars (mkDecide d.conj d.decidable)
      Meta.withLocalDeclD `disjunctIndex (.const ``Nat []) fun ci => do
        -- the disjunct dispatch: `cond (disjunctIndex == j)
        -- (disjunctⱼ …) …`, `false`
        -- at the leaf, so an index past the disjuncts answers false (§9.3)
        let projTerms := Array.range ctx.inputFvars.size |>.map projOfIdx
        let mut dispatch := mkConst ``Bool.false
        for j in [0:disjunctLams.size] do
          let applied := mkAppN disjunctLams[j]! projTerms
          dispatch := mkCond (.const ``Bool [])
            (mkAppN (.const ``Nat.beq []) #[ci, mkRawNatLit j]) applied dispatch
        let checkBody := optGetD (.const ``Bool [])
          (optMap tupTy (.const ``Bool [])
            (← Meta.mkLambdaFVars #[xs] dispatch) decoderApp)
          (mkConst ``Bool.false)
        let checkFn ← Meta.mkLambdaFVars #[ci, bytes] checkBody

        -- the run body under `xs` (§11.3)
        let exTy := probeResultExTy
        let resultTy := Expr.const ``EthCLLib.TheoremVectors.ProbeResult []
        -- `Except.error` carries `{ε α : Type}` as implicits
        let decodeFailed := mkAppN (.const ``Except.error [levelZero, levelZero])
          #[.const ``String [], resultTy,
            mkStrLit "theorem_vectors: a record input failed to decode"]
        -- per-input literal and root terms, computed inside the run body
        let inputLits := (Array.zip (Array.zip inputTys toStringInsts?)
          (Array.range ctx.inputFvars.size)).map fun ((t, inst?), j) =>
          match inst? with
          | some inst =>
            optSome (.const ``String []) (toStringCall t inst (projOfIdx j))
          | none => optNone (.const ``String [])
        let inputRoots := (Array.zip (Array.zip inputTys rootInsts?)
          (Array.range ctx.inputFvars.size)).map fun ((t, inst?), j) =>
          match inst?, hashPair? with
          | some inst, some (h, hasher) =>
            optSome (.const ``ByteArray [])
              (mkAppN (.const ``SizzLean.SSZ.hashTreeRoot [])
                #[t, h, hasher, inst, projOfIdx j])
          | _, _ => optNone (.const ``ByteArray [])
        let bodyOpt ← match shape with
          | .eq lhs rhs => do
            let b? ← eqRunBody lhs rhs underXs outTy outRepr? hashPair?
              outToString? inputLits inputRoots
            pure (b?.map fun b => (b, none))
          | .bound lhs _ _ =>
            let some (cmp, cmpDec) := cmp?
              | return .error "the bound has no `Decidable` instance"
            let b? := boundRunBody lhs cmpDec cmp underXs outTy
              outToString? inputLits inputRoots
            pure (b?.map fun b => (b, none))
          | .iffTrue _ _ =>
            let some (lhs, q, qDec) := iffDecs?
              | return .error "the `.iffTrue` conclusion has no `Decidable` \
                  instance for its right side"
            let some outToString := outToString?
              | return .error "the output type has no `ToString` instance"
            pure (some (iffTrueRunBody lhs q qDec underXs outToString
              outRepr? hashPair? inputLits inputRoots, none))
          | .runOk act pre ret post =>
            -- `outRepr?` is the pre-state's `SSZRepr` here, the instance
            -- `runPure` and the store pick's serialization take; it
            -- exists because the pre-state crossed the byte boundary
            -- (§9.1)
            let some preRepr := outRepr?
              | return .error "the pre-state has no `SSZRepr` instance, so \
                  the run's post-state has nothing to record"
            -- §11.3's output rule: the record picks the run's return
            -- value when its type names the binding's state container,
            -- the value-style mutators' shape; the store pick stays for
            -- the `Unit`-return steps, whose mutation lives on the store
            let (_, retTy) ← runSpineOf act ".runOk"
            let valSide? ← runOkValueSide? binding retTy
            let body ← runOkRunBody act pre ret post underXs tag outTy
              preRepr valSide? hashPair? inputLits inputRoots
            -- the recorded type replaces the pre-state's in the record's
            -- output value, so the type string names the bytes
            pure (some (body, valSide?.map (fun v => v.ty)))
          | .runError act pre err =>
            let some preRepr := outRepr?
              | return .error "the pre-state has no `SSZRepr` instance, so \
                  the run has nothing to record"
            match ← runErrorRunBody act pre err underXs tag outTy preRepr
                inputLits inputRoots with
            | .ok b => pure (some (b, none))
            | .error e => return .error e
          | _ => unsupportedShapeError shape
        let some (body, valOutTy?) := bodyOpt
          | return .error "the output type has neither an `SSZRepr` nor a \
              `ToString` instance, so there is nothing to record"
        let runBody := optGetD exTy
          (optMap tupTy exTy (← Meta.mkLambdaFVars #[xs] body) decoderApp)
          decodeFailed
        let runFn ← Meta.mkLambdaFVars #[bytes] runBody

        -- §9.4: the container reads. Per disjunct, the plan the walk
        -- produces; the probe evaluates it at the candidate's bytes, so
        -- the random searcher's substitution and the compiled values stay aligned.
        -- the statement's own kind table, the reader computed once (§9.4)
        let containerFlags : Array (Option FVarId) :=
          (Array.range ctx.inputFvars.size).map fun i =>
            if stmt.scalarKinds[i]?.join.isNone then
              some ctx.inputFvars[i]!.fvarId!
            else none
        let containerIds : Array FVarId := containerFlags.filterMap id
        let arrTy := mkApp (.const ``Array [levelZero]) (.const ``ByteArray [])
        let boolArrTy := mkApp (.const ``Array [levelZero]) (.const ``Bool [])
        let mut readsDispatch :=
          mkAppN (.const ``Array.empty [levelZero]) #[.const ``ByteArray []]
        let mut safeDispatch :=
          mkAppN (.const ``Array.empty [levelZero]) #[.const ``Bool []]
        -- one plan per disjunct: the reads' wire values and the read
        -- bounds walk the same subterms, so both dispatches build from it
        for j in [0:disjuncts.size] do
          let plan ← containerReads containerIds disjuncts[j]!.hyps
          let encodes : Array Expr ← plan.mapM fun r => do
            let v := underXs r
            let some enc ← readEncodeTerm (← Meta.inferType r) v
              | throwError "theorem_vectors: a container read has no \
                  scalar wire form (§9.4)"
            pure enc
          let readsDisjunct := optGetD arrTy
            (optMap tupTy arrTy (← Meta.mkLambdaFVars #[xs]
              (mkArrayLit (.const ``ByteArray []) encodes)) decoderApp)
            (mkAppN (.const ``Array.empty [levelZero]) #[.const ``ByteArray []])
          readsDispatch := mkCond arrTy
            (mkAppN (.const ``Nat.beq []) #[ci, mkRawNatLit j]) readsDisjunct
            readsDispatch
          -- §9.4, from the stage-4 outcome: the read bounds. Per read,
          -- whether the read's `!`-index stays inside its collection at
          -- the candidate's bytes. A point or candidate the face answers
          -- `false` for never reaches the compiled `reads` or `check`, so
          -- no panic reaches compiled code. The face is pure over the
          -- decoded inputs, so the searchers can gate on it before they
          -- evaluate anything else.
          let checks : Array Expr ← plan.mapM fun r => do
            entrySafeTerm <$> (← detectReadBounds r #[]).mapM fun (coll, idx) => do
              let some lenT ← lengthTermOf (underXs coll)
                | pure (mkConst ``Bool.true)
              let idxT := underXs idx
              pure (mkDecide (mkAppN (.const ``LT.lt [levelZero])
                #[.const ``Nat [], .const ``instLTNat [], idxT, lenT])
                (mkAppN (.const ``Nat.decLt []) #[idxT, lenT]))
          let safeDisjunct := optGetD boolArrTy
            (optMap tupTy boolArrTy (← Meta.mkLambdaFVars #[xs]
              (mkArrayLit (.const ``Bool []) checks)) decoderApp)
            (mkAppN (.const ``Array.empty [levelZero]) #[.const ``Bool []])
          safeDispatch := mkCond boolArrTy
            (mkAppN (.const ``Nat.beq []) #[ci, mkRawNatLit j]) safeDisjunct
            safeDispatch
        let readsFn ← Meta.mkLambdaFVars #[ci, bytes] readsDispatch
        let safeFn ← Meta.mkLambdaFVars #[ci, bytes] safeDispatch

        -- the manual terms, serialized in compiled code (§9.4). Each
        -- manual term already carries the telescope's instances (§14.6:
        -- elaborated in the telescope), which `substInstances` fixes
        -- per preset.
        let manualsLit : Array Expr ← manualTerms.mapM fun (pos, sterm) => do
          let t ← Meta.inferType sterm
          let inst ← Meta.synthInstance (mkApp (.const ``ScalarCodec []) t)
          pure (mkAppN (.const ``Prod.mk [levelZero, levelZero])
            #[.const ``Nat [], .const ``ByteArray [],
              mkRawNatLit pos, encodeCall t inst sterm])
        -- the defaults: the base searcher's candidate (§9.4). A type with no
        -- total default (`Fin 0`) encodes the empty byte string, which the
        -- check rejects, so the base searcher fails that disjunct honestly.
        let defaultsLit := mkArrayLit (.const ``ByteArray [])
          ((Array.zip inputTys codecInsts).map fun (t, codec) =>
            optGetD (.const ``ByteArray [])
              (mkAppN (.const ``Option.map [levelZero, levelZero])
                #[t, .const ``ByteArray [],
                  mkAppN (.const ``ScalarCodec.encode []) #[t, codec],
                  mkAppN (.const ``ScalarCodec.default []) #[t, codec]])
              (mkConst ``emptyBytes []))
        -- §9.4: the draw and the shrink. A scalar position answers its
        -- default encoding, the zero entry the solver replaces; a
        -- container position draws through its `SampleableExt` instance
        -- (§9.5), each at `mixHash seed (i + 1)` so no two positions and
        -- no two draws share a generator state, and contributes one
        -- `shrinkReplace` step (§9.6). Both sample faces walk the same
        -- per-position terms, so `sample` at a position and `sampleAt`
        -- for it agree byte for byte, which is what lets the memo and
        -- the per-position draws share entries (§9.4).
        let sampleFns : Except String (Expr × Expr) ←
          Meta.withLocalDeclD `seed (.const ``Nat []) fun seedV =>
            Meta.withLocalDeclD `size (.const ``Nat []) fun sizeV => do
              let mut entries : Array Expr := #[]
              for i in [0:inputTys.size] do
                let t := inputTys[i]!
                let codec := codecInsts[i]!
                if (stmt.scalarKinds[i]?.join).isSome then
                  entries := entries.push
                    (optGetD (.const ``ByteArray [])
                      (mkAppN (.const ``Option.map [levelZero, levelZero])
                        #[t, .const ``ByteArray [],
                          mkAppN (.const ``ScalarCodec.encode []) #[t, codec],
                          mkAppN (.const ``ScalarCodec.default []) #[t, codec]])
                      (mkConst ``emptyBytes []))
                else
                  let sampRes ← Meta.trySynthInstance
                    (mkApp (.const ``Plausible.SampleableExt [levelOne, levelZero]) t)
                  let some samp := sampRes.toOption
                    | return .error s!"input {stmt.inputs[i]!.name} has no \
                        draw (§9.5); the theorem is out of scope (§1.2)"
                  entries := entries.push
                    (mkAppN (.const ``EthCLLib.TheoremVectors.sampleOne [])
                      #[t, codec, samp,
                        -- `mixHash` spreads the seed and the position
                        -- apart: `seed + d + i` and `seed + d + i' + 1`
                        -- would share a generator state across draws
                        mkApp (.const ``UInt64.toNat [])
                          (mkAppN (.const ``mixHash [])
                            #[mkApp (.const ``UInt64.ofNat []) seedV,
                              mkApp (.const ``UInt64.ofNat [])
                                (mkRawNatLit (i + 1))]),
                        sizeV])
              let sampleFn ← Meta.mkLambdaFVars #[seedV, sizeV]
                (mkArrayLit (.const ``ByteArray []) entries)
              -- the per-position face (§9.9): the dispatch answers entry
              -- `pos`'s own term, `emptyBytes` past the inputs. `cond` is
              -- `@[macro_inline]`, so the compiled term is a match and the
              -- untaken arms' draws never run.
              Meta.withLocalDeclD `pos (.const ``Nat []) fun posV => do
                let mut dispatch := mkConst ``emptyBytes []
                for j in [0:entries.size] do
                  dispatch := mkCond (.const ``ByteArray [])
                    (mkAppN (.const ``Nat.beq []) #[posV, mkRawNatLit j])
                    entries[j]! dispatch
                let sampleAtFn ← Meta.mkLambdaFVars #[seedV, sizeV, posV] dispatch
                return .ok (sampleFn, sampleAtFn)
        let (sampleFn, sampleAtFn) ←
          match sampleFns with
          | .ok f => pure f
          | .error e => return .error e
        let shrinkFnE : Except String Expr ←
          Meta.withLocalDeclD `shrinkIn arrTy fun bV => do
            let mut acc := mkAppN (.const ``Array.empty [levelZero]) #[arrTy]
            for i in [0:inputTys.size] do
              let t := inputTys[i]!
              unless stmt.scalarKinds[i]?.join.isNone do continue
              let codec := codecInsts[i]!
              -- the codec's generic instance carries `[SSZRepr T]
              -- [Inhabited T]`, so a container with a codec has the
              -- `SSZRepr` the shrink's `shrinkShape` walks
              let rRes ← Meta.trySynthInstance
                (mkApp (.const ``SizzLean.SSZRepr []) t)
              let some r := rRes.toOption
                | return .error s!"input {stmt.inputs[i]!.name} has no \
                    shape description to shrink (§9.6)"
              acc := mkAppN (.const ``Array.append [levelZero])
                #[arrTy, acc,
                  mkAppN (.const ``EthCLLib.TheoremVectors.shrinkReplace [])
                    #[t, codec, r, bV, mkRawNatLit i]]
            return .ok (← Meta.mkLambdaFVars #[bV] acc)
        let shrinkFn ←
          match shrinkFnE with
          | .ok f => pure f
          | .error e => return .error e
        -- §9.9: the builder face. The dispatch over the binding's catalog
        -- runs the named builder with the preset's instances bound and
        -- serializes the state it produces through the state input's codec.
        -- A statement with no state input keeps the empty stub: the built
        -- searcher applies to exactly one state input, so the face is never
        -- called on it.
        let statePos? := (Array.range inputTys.size).find? fun i =>
          match inputTys[i]!.getAppFn with
          | .const c _ => c == binding.stateType
          | _ => false
        let buildFn ← match statePos? with
          | none =>
            pure (stub2 (.const ``Nat []) (.const ``Knobs [])
              (mkConst ``emptyBytes []))
          | some statePos => do
            -- the state position's codec, and its type, carry the
            -- telescope's instance variables; the builder applications
            -- name the binding's constants, so both go through the same
            -- substitution the finished term gets, here, where the
            -- encode's type argument must match the applied builder's
            -- result type (§11.2's substitution)
            let stateTy := substInstances ctx instConsts inputTys[statePos]!
            let stateCodec := substInstances ctx instConsts codecInsts[statePos]!
            Meta.withLocalDeclD `builderIx (.const ``Nat []) fun bIx =>
              Meta.withLocalDeclD `knobsV (.const ``Knobs []) fun knobsV => do
                let mut dispatch : Expr := mkConst ``emptyBytes []
                for i in [0:binding.builders.size] do
                  let (_, bConst) := binding.builders[i]!
                  unless (← getEnv).contains bConst do
                    throwError "theorem_vectors: the `{binding.tag}` binding's \
                      builder `{bConst}` does not resolve; is the fork's \
                      Builders module imported? (§9.9)"
                  let some app ← applyAcrossInstances binding presetId bConst
                      #[knobsV] |
                    throwError "theorem_vectors: the `{binding.tag}` binding's \
                      builder `{bConst}` does not take the fork's instances and \
                      a `Knobs` argument (§9.9)"
                  let resTy ← Meta.inferType app
                  unless (match resTy.getAppFn with
                      | .const c _ => c == binding.stateType
                      | _ => false) do
                    throwError "theorem_vectors: the `{binding.tag}` binding's \
                      builder `{bConst}` produces \
                      `{← Meta.ppExpr resTy}`, not the fork's \
                      state container (§9.9)"
                  let ser := encodeCall stateTy stateCodec app
                  dispatch := mkCond (.const ``ByteArray [])
                    (mkAppN (.const ``Nat.beq []) #[bIx, mkRawNatLit i]) ser
                    dispatch
                Meta.mkLambdaFVars #[bIx, knobsV] dispatch
        let term := mkAppN (.const ``Probe.mk [])
          #[checkFn, sampleFn, sampleAtFn, shrinkFn, readsFn, safeFn,
            mkArrayLit (mkApp2 (.const ``Prod [levelZero, levelZero]) (.const ``Nat [])
              (.const ``ByteArray [])) manualsLit,
            defaultsLit,
            buildFn,
            runFn]
        let face ← evalProbeCore (substInstances ctx instConsts term)
        let inputTypes ← inputTys.mapM (renderedType ctx instConsts)
        -- §9.8: the fingerprint's statement parts. The hypotheses and the
        -- conclusion's sides render with the preset's constants
        -- substituted, and every input with a wire description
        -- contributes its shape hash, so a new container field changes
        -- the fingerprint and the fork's random hints go stale at once
        let hypParts : Array String ← stmt.hyps.mapM (renderedType ctx instConsts)
        let concParts : Array String ←
          (shapeTermsOf shape).mapM (renderedType ctx instConsts)
        let shapeHashes : Array (Option String) ←
          (Array.zip inputTys rootInsts?).mapM fun (t, r?) => do
            match r? with
            | none => pure none
            | some r =>
              -- the telescope's instance variables leave first: the
              -- shape hash evaluates in compiled code, which needs a
              -- closed term (§11.2's substitution)
              let t' := substInstances ctx instConsts t
              let r' := substInstances ctx instConsts r
              pure (some (toString (← evalShapeHashOp
                (mkAppN (.const ``shapeHash []) #[t', r']))))
        let shapeParts : Array String := shapeHashes.map (fun o? => o?.getD "")
        let info : ProbeInfo :=
          { inputNames := stmt.inputs.map (·.name)
            inputTypes
            outputType := ← renderedType ctx instConsts (valOutTy?.getD outTy)
            stmtParts := hypParts ++ concParts
            shapeParts }
        return .ok (info, face)

end EthCLLib.TheoremVectors
