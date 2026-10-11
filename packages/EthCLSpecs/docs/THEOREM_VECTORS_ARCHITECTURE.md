# Theorem vectors: architecture

This document describes the finished theorem-vector generator. It is the
design of record for the code, the way `FRAMEWORK_ARCHITECTURE.md` is for the
framework. It lives beside the other design documents for `EthCLLib` and
`EthCLSpecs`; `THEOREM_VECTORS_PLAN.md` sequences the stages that build it.

Read `SPEC_AUTHORING_MODEL.md` §11 and `FRAMEWORK_ARCHITECTURE.md` §13 first.
The generator repeats the inversion those sections set for the pyspec runner: a
fork-agnostic half in `EthCLLib`, a fork-aware half in `EthCLSpecs`, and a
typeclass-shaped seam between them.

Contents:

1. Purpose and scope
2. Placement in the monorepo
3. The pipeline
4. Module map
5. The core data model
6. The fork binding seam
7. The statement reader
8. The prepare pass
9. The witness search
10. Preset binding and witness reuse
11. The probe and the executor
12. Records
13. Formats
14. Selecting theorems and the generator commands
15. The command-line harness
16. The report
17. Build integration
18. Failure policy
19. Extension points
20. Glossary

---

## 1. Purpose and scope

### 1.1 What a theorem vector is

A proved theorem of the form `∀ x, P x → f x = e x` carries three facts a test
vector needs. `P` says which inputs are in scope. `f x` names the function
under test and its argument. `e x` says what the output must be. The kernel has
checked that claim for every `x` that satisfies `P`.

A **theorem vector** is one concrete `x` with `P x`, plus the recorded `f x`.
The generator turns one theorem into one or more vectors. A client that
implements `f` replays the vector. A client that fails learns which proved
property it broke, because the vector names the theorem.

A found `x` also shows that `P` is satisfiable. A theorem with an unsatisfiable
`P` produces no vector and a report line that says so.

### 1.2 Scope

The generator reads the public theorems under `EthCLSpecs.Proofs`. A theorem is
in scope when every explicit or implicit value binder has a type the generator
can produce and serialize, and when its conclusion has one of the shapes in
§5.3.

Out of scope, with the reason the reader reports:

| Input or form | Reason |
| --- | --- |
| A block type: `BeaconBlock`, `SignedBeaconBlock`, `BeaconBlockBody`, `ExecutionPayload`, `SignedExecutionPayloadEnvelope` | A block the theorem accepts needs a proposer index, a parent root, a state root, and signatures. Neither random draws nor the bit-vector solver meets them. |
| The fork-choice `Store` | It holds blocks and payloads by root, and its map backend is a type parameter. |
| A function-typed input, such as `f : Gwei → Gwei` | No SSZ form exists for a function. |
| A conclusion outside the shape set | The reader cannot name the output. |

The scope rule has one exception that costs nothing. The base source (§9.4)
still runs on a theorem with a block input. If `default` satisfies `P`, the
vector is written. If it does not, the theorem is reported out of scope and no
other source runs.

The block types are a per-fork fact. The fork binding (§6) names them, so the
framework half never names a fork type.

### 1.3 Trust boundary

The kernel checks the theorem for every `x` with `P x`, at every preset, and for
every hasher and crypto backend the theorem binds as an instance.

The vector records what the **compiled** Lean implementation computes at one
`x`, under the FFI SHA-256 hasher and the verify-off crypto backend. The
executor also computes `e x` compiled and compares. The kernel has proved the
two equal, so a disagreement is a compiler, FFI, or serialization bug. The
check is free and the failure is loud. It does not re-check the kernel.

The `decide P` check that every witness passes is compiled too. The same trust
applies.

A vector tests one point of a property the proof covers everywhere. Its value
is against other clients. For the Lean implementation, the proof already
covers it.

---

## 2. Placement in the monorepo

### 2.1 Two halves and a seam

```
                       SizzLean, LeanHazmat*
                               │
                               ▼
┌──────────────────────── EthCLLib (package) ─────────────────────────────┐
│                                                                          │
│  EthCLLib            the framework, the Spec DSL, PySpecTests.Driver     │
│                               │                                          │
│                               ▼                                          │
│  EthCLLib.TheoremVectors      lean_lib EthCLLibTheoremVectors            │
│    reader, prepare, witness sources, probe, executor, records,           │
│    formats, report, the generator commands, the ForkBinding seam         │
│    + require plausible                                                   │
└──────────────────────────────┬───────────────────────────────────────────┘
                               │ import
                               ▼
┌──────────────────────── EthCLSpecs (package) ───────────────────────────┐
│                                                                          │
│  EthCLSpecs           Fulu, Gloas, Heze bodies and EthCLSpecs.Proofs     │
│                               │                                          │
│                               ▼                                          │
│  EthCLSpecs.TheoremVectors    lean_lib EthCLSpecsTheoremVectors          │
│    Bindings/   one ForkBinding value per fork                            │
│    Builders/   the state-builder catalog per fork                        │
│    Seeds/      author-written input terms                                │
│    Generators/ one file per fork: discovery clauses and named lines      │
│    Hints/      the committed hints, one JSON file per theorem            │
│    Main.lean   lean_exe theorem_vectors: render, check, report           │
└──────────────────────────────────────────────────────────────────────────┘
```

The framework half names no fork, no container, and no theorem. It works on
`Expr`, `Name`, and `ByteArray`. The spec half supplies every fork fact as a
value of one framework type, `ForkBinding` (§6), and lists the theorems in
generator files.

### 2.2 Why the split

`EthCLLib` cannot import `EthCLSpecs`. The proofs live in `EthCLSpecs`, so any
code that names a theorem or a fork type lives there too. The same constraint
shaped the pyspec runner: `PySpecTests.Driver` is generic in `EthCLLib`, and
`pyspec_server` in `EthCLSpecs` instantiates it at a fork through
`ForkInterface`. The generator follows that pattern, with `ForkBinding` in the
role of `ForkInterface`.

The split also keeps the dependency on `Plausible` out of the shipped
libraries. `EthCLLib` and `EthCLSpecs` import nothing under
`EthCLLib.TheoremVectors`, so the link line of `pyspec_server` does not change.

### 2.3 Lake targets

`packages/EthCLLib/lakefile.toml` gains one require and one library:

```toml
[[require]]
name = "plausible"
git = "https://github.com/leanprover-community/plausible"
rev = "v4.29.0"

# The theorem-vector generator's framework half. Excluded from the shipped
# EthCLLib library, which globs only its own root, the way EthCLLibTests is.
[[lean_lib]]
name = "EthCLLibTheoremVectors"
roots = ["EthCLLib.TheoremVectors"]
```

`packages/EthCLSpecs/lakefile.toml` gains one library and one executable:

```toml
# The generator's spec half: fork bindings, state builders, seeds, and the
# generator files whose elaboration writes the records. The output directory
# is fixed here so the command never depends on the working directory Lake
# gives it. The `weak.` prefix defers the setting until the module that
# registers the option is imported; `lean` rejects a `-D` for an option it
# has not seen yet.
[[lean_lib]]
name = "EthCLSpecsTheoremVectors"
roots = ["EthCLSpecs.TheoremVectors"]
leanOptions = [{ name = "weak.theorem_vectors.outDir", value = "packages/EthCLSpecs/theorem_vectors" }]

# The command-line harness over the records: render, check, report.
[[lean_exe]]
name = "theorem_vectors"
root = "EthCLSpecs.TheoremVectors.Main"
```

The exe root sits in `EthCLSpecsTheoremVectors`, a library that is not
precompiled, so it needs no `supportInterpreter` shim. It links the FFI the
same way `pyspec_server` does, through the package-level `moreLinkArgs`.

### 2.4 Dependencies

| Dependency | Used for | Where |
| --- | --- | --- |
| `Plausible` v4.29.0 | `SampleableExt`, `Shrinkable`, `Gen` | `EthCLLib.TheoremVectors.Sampleable`, `Witness.Random`, `Witness.Shrink` |
| `Std.Tactic.BVDecide` (core) | `bvDecide'` and its `CounterExample` | `Witness.BitVec` |
| `cadical` (ships with the toolchain) | the SAT backend of `bvDecide'` | build environment |
| `SizzLean` | `SSZRepr`, serialize, `hashTreeRoot` | the probe, records |
| `Lean.Json` (core) | `ToJson`, `FromJson`, the printer and parser | records, outcomes, hints |
| `EthCLLib.PySpecTests` | `ForkInterface`, `runCase` | the pyspec format's check |

The `Plausible` tag sits one patch behind the `v4.29.1` toolchain. A toolchain
bump moves the tag with it. That is one line in the bump checklist.

### 2.5 Why generation runs at elaboration time

A runtime executable that generates vectors would run over `importModules`
and pay for it: `loadExts`, initializer execution, the `evalExpr`
import-env path, and the `maxHeartbeats` budget. None of that is needed
here. A `command` elaborator runs
during `lake build` of a generator file. It sees the full environment,
`evalExpr` works, `MetaM` tactics work, and the output directory is a build
artifact.

The cost is one generator file per fork. That file is also the review
surface: a reader sees which theorems produce vectors, which do not, and
why.

The render, check, and report passes need no theorem and no `evalExpr`.
They read records from disk. They run in the exe, which keeps them out of
the build of the generator files, so a change to a format never reruns a
search.

### 2.6 What one vector is worth

One vector per theorem tests one input. The proof already covers every
input for the Lean `f`. The vector earns its place against other clients,
where the sample position matters. This generator supplies the oracle and
the property name. Choosing positions across the input space is a separate
concern, and this design leaves it to a later tool. Three pieces sit in the
framework half so such a tool can import them: the `bvDecide'`
counterexample reader, the generic SSZ `SampleableExt` instance, and the
probe's byte boundary.

---

## 3. The pipeline

Three phases. Phase A runs once per theorem, inside the `theorem_vectors`
command. Phase B runs once per preset in the line's preset list, inside the
same command. Phase C runs over the records of every run, in the exe.

```
generator file  (theorem_vectors_fork header, discovery clauses, named lines)
        │
 A0 Select    read the whole file; resolve discovery, survey, overrides, skips   §14.3
        │
════════╪═══ Phase A: per theorem, at elaboration time ═══════════════════════
        ▼
 A1 Read      theorem type → Statement: inputs, hyps, target, shape     §7
        ▼
 A2 Scope     block input? → only the base source may run              §7.4
        ▼
 A3 Prepare   unfold spec predicates, split P into DNF cases,
              add the Q / ¬Q side for .iffTrue → Array Case             §8
        │
════════╪═══ Phase B: per preset ═════════════════════════════════════════════
        ▼
 B1 Bind      fix [Preset] [Config] [HasherTag] [CryptoBackend];
              build and evaluate the Probe for this preset              §10, §11
        ▼
 B2 Reuse     a scalar witness from an earlier preset passes check? → B5 §10
        ▼
 B3 Search    witness sources in order, the committed hint first,
              each candidate through check                              §9
        ▼
 B4 Shrink    smaller inputs while check still holds                    §9.6
        ▼
 B5 Execute   probe.run: f x, e x, compare, serialize, roots            §11
        ▼
 B6 Record    one VectorRecord directory per case, and its hint         §12, §9.8
        ▼
 B7 Verify    read the record back, decode, run f again, compare        §12.5
        ▼
 B8 Outcome   append one outcome line for the report                    §16
        │
════════╪═══ Phase C: over all records, in the exe ═══════════════════════════
        ▼
 C1 Render    every record → every format that accepts it               §13
        ▼
 C2 Check     each format's consumer replays its vectors                §13.5
        ▼
 C3 Report    outcomes + records → theorem_vectors/report.md            §16
```

A theorem that reaches B8 with no record written logs a warning with the
reason. The `theorem_vectors!` form and the `@[theorem_vectors]` tag turn that
warning into an error.

---

## 4. Module map

### 4.1 The framework half: `EthCLLib/TheoremVectors/`

| Module | Responsibility | Depends on |
| --- | --- | --- |
| `Types.lean` | `PresetId`, `ShapeTag`, `WitnessSourceTag`, `Failure`, `ValueData`, `BoundRel`, `Knobs` | Lean core |
| `ForkBinding.lean` | the `ForkBinding` structure and `PresetInstances` | `Types`, `PySpecTests.Interface` |
| `Statement.lean` | `Statement`, `Shape`, the reader over a theorem type | `Types`, `Internal.Capture` |
| `Scope.lean` | the block-input walk over input types | `Statement`, `ForkBinding` |
| `Prepare.lean` | unfold, normalize, DNF split, side cases → `Array Case` | `Statement` |
| `Sampleable.lean` | `SampleableExt` and `Shrinkable` for scalars and SSZ containers | `Plausible`, `SizzLean` |
| `Probe.lean` | the `Probe` structure and the term builder that produces it | `Statement`, `Prepare`, `ForkBinding`, `Sampleable` |
| `Witness/Source.lean` | `WitnessSource`, the search loop, the check | `Probe` |
| `Witness/Base.lean` | the `default` source | `Witness.Source` |
| `Witness/BitVec.lean` | the `bvDecide'` source and the counterexample reader | `Witness.Source` |
| `Witness/Built.lean` | the state-builder source, the knob grid, the built-state cache | `Witness.Source`, `Witness.BitVec` |
| `Witness/Random.lean` | the random-state-plus-solve source | `Witness.Source`, `Witness.BitVec` |
| `Witness/Seed.lean` | the author-seed source | `Witness.Source` |
| `Witness/Shrink.lean` | the shrink loop | `Witness.Source` |
| `Witness/Hint.lean` | the hint schema, reader, writer, fingerprint, and the hint source | `Witness.Source`, `Lean.Json` |
| `Preset.lean` | bind one preset, the reuse check | `Probe`, `ForkBinding` |
| `Execute.lean` | per-shape outcome from probe runs, the agreement check | `Probe` |
| `Record.lean` | `VectorValue`, `VectorRecord`, writer, reader | `Types`, `Lean.Json` |
| `Yaml.lean` | the YAML writer for the client-facing files (§12.3) | Lean core |
| `Format.lean` | the `VectorFormat` structure and `RenderEnv` | `Record`, `ForkBinding` |
| `Formats/Function.lean` | the function format | `Format`, `Yaml` |
| `Formats/Pyspec.lean` | the pyspec format and its `runCase` check | `Format`, `Yaml`, `PySpecTests.Driver` |
| `Outcome.lean` | the per-theorem outcome lines | `Types`, `Lean.Json` |
| `Report.lean` | `report.md` from outcomes and records | `Outcome`, `Record` |
| `Command.lean` | `theorem_vectors_fork`, `theorem_vectors` with its discovery, named, and `skip` forms | everything above except `Formats`, `Report`; `Internal.ProofLedger` for the two tags |
| `TheoremVectors.lean` | the library root, re-exports | all |

Each module does one thing. `Statement` reads. `Prepare` rewrites. `Probe`
compiles. `Witness/*` searches. `Execute` runs. `Record` persists. `Format`
renders. `Command` sequences.

One piece sits outside the library. The `@[theorem_vectors]` attribute and
its extension, `theoremVectorsExt`, live in `EthCLLib.Internal.ProofLedger`
beside `@[characterizes]`. A proof module imports that module already, and
it pulls in nothing from the generator (§14.1).

### 4.2 The spec half: `EthCLSpecs/TheoremVectors/`

| Module | Responsibility |
| --- | --- |
| `Bindings/Fulu.lean`, `Bindings/Gloas.lean`, `Bindings/Heze.lean` | one `ForkBinding` value per fork |
| `Bindings.lean` | the table the exe uses: fork tag → `ForkBinding` |
| `Seeds/Gloas.lean` (and siblings as needed) | author-written input terms, `[Preset]`-generic |
| `Builders/Fulu.lean`, `Builders/Gloas.lean`, `Builders/Heze.lean` | the state-builder catalog per fork (§9.9) |
| `Generators/Fulu.lean`, `Generators/Gloas.lean`, `Generators/Heze.lean` | the generator lists |
| `Hints/<fork>/<thm>.json` | the committed hints, one file per theorem (§9.8) |
| `Main.lean` | the exe: `render`, `check`, `report` |
| `TheoremVectors.lean` | the library root, imports the bindings, builders, seeds, and generators |

A generator file imports `EthCLSpecs.Proofs.<Fork>`, its fork's binding, and
its fork's seeds. The binding imports its fork's builders, because it names
them. A generator file imports nothing from another fork.

### 4.3 Module dependency graph

```
                 Types ──────────────┐
                   │                 │
         ┌─────────┼──────────┐      │
         ▼         ▼          ▼      ▼
    ForkBinding  Statement  Record  Outcome        Yaml (writer only)
         │         │  │       │      │               │
         │         │  └──► Scope     │               │
         │         ▼          │      │               │
         │      Prepare       │      │               │
         │         │          │      │               │
         │   Sampleable       │      │               │
         │         │          ▼      │               │
         └────►  Probe ◄── Format ───┼──► Report     │
                   │          │      │               │
          ┌────────┼───────┐  ├─ Formats/Function ◄──┤
          ▼        ▼       ▼  └─ Formats/Pyspec ◄────┘
    Witness/*   Preset   Execute
          │        │       │
          └────────┴───────┴──────► Command

    Spec half:  Bindings ──► Generators ──► (elaboration writes records)
                Bindings ──► Main (exe) ──► Formats, Report
```

`Command` is the only module that imports the whole pipeline. The exe imports
`Format`, `Formats/*`, `Report`, and the bindings. Neither imports the other.

---

## 5. The core data model

Every type below lives in the framework half. None names a fork.

### 5.1 Presets

```lean
/-- The presets a run can fix. The generator, the records, and the paths all
take the preset from this inductive; the fork binding maps each one to the
fork's own `Preset` and `Config` instances. -/
inductive PresetId where
  | minimal
  | mainnet
  deriving DecidableEq, Repr, Inhabited

def PresetId.tag : PresetId → String
  | .minimal => "minimal"
  | .mainnet => "mainnet"
```

### 5.2 The statement

```lean
/-- One value binder of the theorem, explicit or implicit. -/
structure Input where
  name     : Name
  type     : Expr      -- with the instance binders still free
  explicit : Bool

/-- One instance binder and the seam it belongs to. -/
inductive InstanceKind where
  | preset | config | hasherTag | cryptoBackend
  | other (className : Name)

structure Statement where
  thm       : Name
  instances : Array (Name × InstanceKind)   -- binder name, seam
  inputs    : Array Input                   -- value binders, in order
  hyps      : Array Expr                    -- Prop binders, in order
  target    : Name                          -- the spec function under test
  shape     : Shape
  blockInputs : Array Name                  -- inputs out of scope by §1.2
```

### 5.3 Shapes

```lean
inductive BoundRel where
  | lt | le

/-- The conclusion forms the reader accepts. Each carries the terms the
executor evaluates, with the binders still free. -/
inductive Shape where
  /-- `lhs = rhs`. One vector; `rhs` pins the output. -/
  | eq (lhs rhs : Expr)
  /-- `lhs = true ↔ q`. Two vectors, one per side of `q`. -/
  | iffTrue (lhs q : Expr)
  /-- `lhs < b` or `lhs ≤ b`. One vector; the bound is checked. -/
  | bound (lhs : Expr) (rel : BoundRel) (b : Expr)
  /-- `act.run (pureState pre) = .ok (ret, pureState post)`, or the `runPure`
  reading `runPure act pre = .ok (ret, post)`. One vector; the post-state is
  the output. -/
  | runOk (act pre ret post : Expr)
  /-- `act.run (pureState pre) = .error err`. One vector with no post-state. -/
  | runError (act pre err : Expr)
  /-- Anything else, with the reason. -/
  | unsupported (reason : String)

inductive ShapeTag where
  | eq | iffTrue | bound | runOk | runError
  deriving DecidableEq, Repr
```

### 5.4 Cases, assignments, sources, failures

```lean
/-- One search problem: a conjunction of hypotheses over the inputs. The
prepare pass produces one per DNF disjunct, times two for `.iffTrue`. -/
structure Case where
  index : Nat
  side  : Option Bool          -- `.iffTrue` only
  hyps  : Array Expr           -- conjuncts, binders still free

/-- A closed value for every input, in binder order, as SSZ bytes. -/
abbrev Assignment := Array ByteArray

inductive WitnessSourceTag where
  | base | bitVec | built | random | seed
  | reused (from : PresetId)
  /-- Rebuilt from a committed hint; `orig` is the source the hint recorded. -/
  | hinted (orig : WitnessSourceTag)
  deriving Repr

inductive Failure where
  /-- The solver proved `¬P` with no state input in play. The theorem is vacuous. -/
  | unsat
  /-- Every source ran out. The author should add a seed. -/
  | notFound (tried : Array WitnessSourceTag)
  /-- A block input and the base source failed (§1.2). -/
  | outOfScope (inputs : Array Name)
```

### 5.5 Outcomes of execution

```lean
/-- What one probe run produced. All values cross the boundary as SSZ bytes. -/
structure ProbeResult where
  output        : ByteArray                -- `f x`, or the post-state, serialized
  expected      : ByteArray                -- `e x`, serialized; empty for `.bound`
  agree         : Bool                     -- `f x == e x`, or the bound holds
  literal       : Option String            -- the output's literal, when it has `ToString`
  inputLiterals : Array (Option String)    -- one per input, in binder order
  inputRoots    : Array (Option ByteArray) -- hashTreeRoot per input, where the type is SSZ
  outputRoot    : Option ByteArray         -- hashTreeRoot of the output, when its type is SSZ
```

The literals and the optional roots answer the record layer's question of
scalar or container (§12.2). A `Nat`-typed bound output has a literal and
no root, and its `output.ssz` holds the literal's UTF-8 bytes.

### 5.6 Records

```lean
inductive ValueData where
  /-- An SSZ value: its bytes live in `<name>.ssz`, the root goes in the record. -/
  | ssz (root : ByteArray)
  /-- A scalar: its decimal literal for the reader. Its SSZ bytes live in
  `<name>.ssz` like every other input, so the read-back needs no type width. -/
  | scalar (literal : String)

structure VectorValue where
  name  : Name          -- the binder name, or `output`
  type  : Name          -- the spec type's constant, such as `EthCLSpecs.Gloas.BeaconState`
  value : ValueData

structure VectorRecord where
  thm       : Name
  fork      : String               -- the binding's tag, such as "gloas"
  preset    : PresetId
  target    : Name
  shape     : ShapeTag
  caseIndex : Nat
  side      : Option Bool
  inputs    : Array VectorValue
  output    : Option VectorValue   -- `none` for `.runError`
  error     : Option String        -- `.runError` only: the error's `repr`
  source    : WitnessSourceTag
```

---

## 6. The fork binding seam

`ForkBinding` is the one type through which the framework half sees a fork.
It plays the role `ForkInterface` plays for the pyspec runner. A fork supplies
one value. The generator consumes it.

```lean
/-- The instance constants one preset fixes. The command builds `Expr.const`
from each name, so a binding names constants and never holds an `Expr`. -/
structure PresetInstances where
  preset : Name     -- `EthCLSpecs.Gloas.minimal
  config : Name     -- `EthCLSpecs.Gloas.minimalConfig

structure ForkBinding where
  /-- The fork namespace, `EthCLSpecs.Gloas`. The reader checks a theorem's
  target against the fork's captured spec functions through this name. -/
  fork        : Name
  /-- The path segment and the pyspec fork name, `"gloas"`. -/
  tag         : String
  /-- One entry per preset the fork supports. -/
  presets     : Array (PresetId × PresetInstances)
  /-- The hasher the probe binds: `EthCLLib.Spec.fastHasherTag`. -/
  hasherTag   : Name
  /-- The crypto backend the probe binds: `EthCLLib.Spec.CryptoBackend.verifyOff`. -/
  crypto      : Name
  /-- The state container, so the pyspec format can tell a state input apart. -/
  stateType   : Name
  /-- The types that put a theorem out of scope (§1.2). -/
  blockTypes  : Array Name
  /-- The namespaces the probe's term is elaborated under. -/
  opens       : Array Name
  /-- The state-builder catalog (§9.9): a display name and a constant of type
  `[Preset] → [Config] → Knobs → BeaconState`, cheapest first. -/
  builders    : Array (String × Name)
  /-- Which `(runner, handler)` pair a spec function answers to in the pyspec
  layout; `none` for a function no vector format drives. -/
  handlerOf   : Name → Option (String × String)
  /-- The fork's `ForkInterface` at a preset, for the pyspec format's check. -/
  interface   : PresetId → Option ForkInterface
```

The Gloas binding, in `EthCLSpecs/TheoremVectors/Bindings/Gloas.lean`:

```lean
def gloas : ForkBinding where
  fork       := ``EthCLSpecs.Gloas
  tag        := "gloas"
  presets    := #[(.minimal, ⟨``Gloas.minimal, ``Gloas.minimalConfig⟩),
                  (.mainnet, ⟨``Gloas.mainnet, ``Gloas.mainnetConfig⟩)]
  hasherTag  := ``EthCLLib.Spec.fastHasherTag
  crypto     := ``EthCLLib.Spec.CryptoBackend.verifyOff
  stateType  := ``Gloas.BeaconState
  blockTypes := #[``Gloas.BeaconBlock, ``Gloas.SignedBeaconBlock, ``Gloas.BeaconBlockBody,
                  ``Gloas.ExecutionPayload, ``Gloas.SignedExecutionPayloadEnvelope, ``Gloas.Store]
  opens      := #[``EthCLLib.Spec, ``EthCLSpecs.Gloas, ``EthCLSpecs.Proofs.Gloas]
  handlerOf  := fun
    | ``Gloas.processBuilderPendingPayments => some ("epoch_processing", "builder_pending_payments")
    | ...
    | _ => none
  interface  := fun
    | .minimal => some Gloas.Interface.gloasInterface
    | .mainnet => some Gloas.Interface.gloasInterfaceMainnet
```

The binding is a plain `def`. A generator file names it in its header
(§14.2), and the command reads it with `evalConst ForkBinding`. The exe reads
the whole table from `Bindings.lean`.

Two consequences follow. A new fork needs one new binding file and one new
generator file, and no edit in the framework half. The framework half's tests
can run against a test binding over a toy fork, the same way `EthCLLib.Tests`
tests the DSL over toy forks.

---

## 7. The statement reader

Input: a theorem `Name` and the binding. Output: a `Statement`, or an error
when the name is not a theorem.

### 7.1 Binder classification

The reader runs `forallTelescope` on the theorem's type. Each binder falls in
one of three groups:

| Binder | Test | Group |
| --- | --- | --- |
| `[Preset]`, `[Config]`, `[HasherTag]`, `[CryptoBackend]` | instance-implicit, class name known | `instances`, with its `InstanceKind` |
| any other instance-implicit | instance-implicit | `instances`, `.other`, reported |
| a `Prop` | `isProp` on the binder type | `hyps` |
| anything else, explicit or implicit | | `inputs` |

Implicit value binders count as inputs. `getPtcElseOffset_lt_next_slot` binds
`{slot curSlot : Slot}` and the vector needs both.

The reader keeps every instance binder free. Phase B fixes them (§10).

### 7.2 Target discovery

The target is the spec function under test. The reader walks the conclusion's
left side and takes the first application whose head is a captured spec
function of the binding's fork, through `EthCLLib.Internal.Capture.isSpecFunction`
and `specFunctionOwner?`. The head of the left side itself is often not the
target: in `(initializePtcWindow (pureState state))[i] = …` the head is
`GetElem.getElem` and the target is `initializePtcWindow`.

A conclusion with no spec function on its left side has no target. The
theorem still runs when its shape matches, and a format that needs a
target rejects its records (§13.3). `getPtcElseOffset_lt_same_slot` is one:
a `.bound` over a helper the proof file defines.

### 7.3 Shape matching

After the telescope, the body is matched in this order:

1. `Iff (Eq lhs true) q` → `.iffTrue lhs q`
2. `Eq (StateT.run act (pureState pre)) (Except.ok (ret, pureState post))` → `.runOk`
3. `Eq (runPure act pre) (Except.ok (ret, post))` → `.runOk`
4. `Eq (StateT.run act (pureState pre)) (Except.error err)` → `.runError`
5. `Eq lhs rhs` → `.eq lhs rhs`
6. `LT.lt lhs b` → `.bound lhs .lt b`; `LE.le lhs b` → `.bound lhs .le b`
7. anything else → `.unsupported` with the head constant in the reason

Rule 7 names one family: a conclusion whose head is a framework predicate
under `EthCLLib.Proofs` (`KeepsUncached`, `KeepsUncachedFrom`,
`ReturnsUncached`) is a box lemma. It states a fact about the box
discipline of a spec function, and no input and output pair expresses it.
The reason reads `box lemma: <head>`, and the report counts these apart
from the other `.unsupported` reasons (§16.2), because they are not a gap
in the shape set.

The `.runOk` match requires `pre` to be one of the inputs and `post` to be a
closed term over the inputs. A theorem whose post-state is an existential
(`∃ s', …`) is `.unsupported`, because the executor cannot evaluate `e x`.
The repository's contract theorems state the whole post-state as a value
(`SPECS_ARCHITECTURE.md` §11.1.1), so this covers them.

### 7.4 The scope walk

For each input, the reader walks the type's constant applications. It stops
with a hit at any constant in `binding.blockTypes`. It descends into the
fields of a structure type and into the element type of `Vector`, `Array`,
`List`, and the SSZ list and vector wrappers. Every hit goes in
`blockInputs`. A function type is a separate hit and makes the statement
`.unsupported`.

### 7.5 What the reader reports

| Finding | Reported as |
| --- | --- |
| `.unsupported` shape | a skip with the reason, in the outcome line |
| a box lemma (§7.3) | a skip with the reason `box lemma: <head>`, counted apart |
| non-empty `blockInputs` | scope restriction: only the base source runs |
| an `.other` instance binder | a skip: the command cannot bind an unknown seam |
| a function-typed input | a skip |

---

## 8. The prepare pass

Input: a `Statement`. Output: `Array Case`.

### 8.1 Unfold

A hypothesis stated through a spec predicate, such as
`¬ isSlashableAttestationData a b`, is one opaque atom to a bit-vector solver
and to a random filter alike. The pass runs `simp only` with three lemma sets:

- the equation lemmas of every spec predicate the hypothesis names, found
  through the capture extension, when the predicate's body is small
  (under 100 expression nodes). A body that folds over a state container
  unfolds into a term the simp walk cannot finish, so the pass leaves it
  as one atom, and the bit-vector source grounds the closed call in
  compiled code instead (§9.4);
- the `UInt64`-to-`Nat` bridge lemmas the proofs already use
  (`UInt64.lt_iff_toNat_lt`, `UInt64.le_iff_toNat_le`, and their siblings),
  oriented back toward `UInt64` form;
- `Bool` normalization (`decide_eq_true_eq`, `Bool.and_eq_true`, and the rest).

Crypto predicates stay as they are. Under the verify-off backend the probe
evaluates them, so the solver never needs to see inside one. A case that
negates a crypto gate is unsatisfiable under that backend. The solver
never sees inside the gate, so the case reports `notFound`, never
`unsat`.

### 8.2 Split

The unfolded conjunction is put in disjunctive normal form. Each disjunct
becomes one `Case`. A hypothesis that unfolds to three branches yields three
cases, and the case index goes into the record's path. Boundary points fall
out of the split: `a < b ∨ a = b` gives the solver two goals, and the equality
case is the boundary.

The pass has a disjunct cap (option `theorem_vectors.maxCases`, default 16).
A theorem over the cap reports the count and falls back to one case with the
unsplit hypothesis.

### 8.3 Sides

For `.iffTrue lhs q`, every case is doubled: one copy adds `q` to its
hypotheses with `side := some true`, the other adds `¬q` with
`side := some false`. The witness for the `¬q` side is a witness of the
negation, which the sources handle the same way.

### 8.4 Decidability

Every case must be decidable, because every source ends with `decide` on the
candidate. The pass synthesizes `Decidable` for the case's conjunction once,
and a case that fails synthesis is reported and dropped.

---

## 9. The witness search

Input: the probe for one preset and one `Case`. Output: an `Assignment` or a
`Failure`.

### 9.1 The byte boundary

Every value that crosses between the elaborator and compiled code is SSZ
bytes. A witness is `Array ByteArray`, one entry per input in binder order.
The probe (§11) decodes inside compiled code. This is the same wire boundary
`ForkInterface` uses, for the same reason: the framework half cannot name a
fork type, and a `ByteArray` names none.

### 9.2 The source interface

```lean
/-- What one source answered. -/
inductive SearchStep where
  | candidate (a : Assignment)   -- goes through the probe's check before it counts
  | nothing                      -- this source has no candidate; try the next
  | unsat                        -- the source proved `¬P`; stop the loop

structure WitnessSource where
  tag     : WitnessSourceTag
  /-- Can this source try this case at all? -/
  applies : Statement → Case → Bool
  /-- Produce one answer. -/
  search  : SearchCtx → Statement → Case → SearchM SearchStep
```

`SearchCtx` carries the probe, the binding, the preset, the seed options, and
the author seeds for this line. `SearchM` is `MetaM` with a budget counter.

The full order is hint (§9.8), seed, base, bit-vector, built (§9.9),
random, and the command assembles the list per line. A line with seeds
runs seed then bit-vector, with no base source: the author chose those
inputs, and a `default` witness would ignore that choice, for the cases
the seed wins and for the cases it fails alike. A line without seeds runs
base then bit-vector. A theorem with a block input runs base alone (§1.2).
The hint source comes first on every list, and the built and random
sources follow the bit-vector source. The rest is cheapest first.

`Witness/Source.lean` holds the loop:

```
for source in sources:
  if source.applies stmt case:
    match ← source.search ctx stmt case with
    | .candidate a => if probe.check case.index a then return .ok a
                      -- the check is compiled `decide P`; a failed check falls
                      -- through to the next source
    | .nothing     => continue
    | .unsat       => return .error .unsat      -- no later source can help
return .error (.notFound tried)
```

A source that cannot produce a candidate the check accepts has produced
nothing. The check is the single arbiter. `notFound` names every source
that ran on the case, whether or not it proposed a candidate.

### 9.3 The check

`probe.check : Nat → Array ByteArray → Bool` takes the case index and the
assignment, decodes the assignment, and evaluates `decide (P x)` for that
case's conjunction, compiled. It never throws: a decode failure is
`false`. The decode is strict, so a corrupt record fails: a byte string
of a width other than the type's, and a `Fin n` value at or above `n`,
decode to `none`.

### 9.4 The core sources

**Base.** Serialize `default` for every input and check. This is the one
source that runs on a theorem with a block input.
`getPtcElseOffset_lt_same_slot` passes here: `slot = 0` has no hypothesis
to fail.

The `default` state is never a candidate. Neither the base source nor the
seed fill proposes `default` for an input of the binding's `stateType`.
The spec is not defined on the empty, all-inactive validator set:
`computePtcFromFulu`'s balance-weighted selection runs to its fuel bound
on it, minutes per committee, and no result follows. A state input comes
from a seed, a hint (§9.8), or the built source (§9.9). A theorem with an
unseeded state input gets `nothing` from both sources.

**Bit-vector.** Applies when every unseeded input has a type in `{UInt8,
UInt16, UInt32, UInt64, Bool}` or an SSZ alias of one (`Slot`, `Epoch`,
`Gwei`, `ValidatorIndex`, …), and every hypothesis is a bit-vector formula
after the prepare pass. A `Fin n` input enters as a `UInt64` with the
bound `x < n`, the probe's own codec (§11.2), once stage 4's bridge lands;
until then the source reports the input and answers `nothing`. The
source poses `¬P` and calls `bvDecide'` from
`Lean.Elab.Tactic.BVDecide.Frontend`, whose result type is
`MetaM (Except CounterExample Result)`. A `CounterExample` carries
`equations : Array (Expr × BVExpr.PackedBitVec)`. Each equation pairs an
input with a value, and the source serializes each value to its SSZ width.
A `Result` means `¬P` is a theorem, so the source returns `Failure.unsat`
and the loop stops: no later source can find what does not exist.

Before the call, the source grounds every maximal closed scalar subterm
of the hypotheses in compiled code and substitutes the literal: a read of
a seeded input (`coverBidState.builders[0]!.balance`), a preset constant
(`UInt64.ofNat slotsPerEpoch`), a crypto gate under the verify-off
backend. The solver abstracts an unreduced constant as an opaque atom and
returns a model around it, which the check rejects; the grounding keeps
the formula over the free scalars alone. It runs before and after the
unfold, so the unfold's products ground too.

With seeds, the source takes the handoff of the seed source. The seeds fix
the containers. A scalar that sits inside a computation over a seeded
input is *coupled* (the builder index of `canBuilderCoverBid_iff`, a read
index), and the source walks it over a grid of its 64 smallest values,
128 grid points per case at most. At each point the seeded reads are
closed, the grounding turns them into literals, and the solver takes the
remaining free scalars. A `¬P` proof at one grid point is a fact about
that point, so the source moves to the next and answers `nothing` when
every point fails. Only the seedless solve, where the formula carries the
whole case, answers `unsat`. A coupled scalar the grid misses falls to a
later source.

**Random plus solve.** Applies when at least one input is a container and the
remaining inputs are scalars. The probe draws the container inputs with their
`SampleableExt` instances (`probe.sample seed size`), serialized. The source
then collects every maximal subterm of the hypotheses that mentions only
container inputs, evaluates each one through `probe.reads`, and substitutes
the literal. What remains is a bit-vector formula over the scalar inputs, and
the bit-vector source solves it. The loop redraws up to
`theorem_vectors.randomDraws` (default 64) times when the solver reports
`¬P` for that draw. `canBuilderCoverBid_iff` is the target: a draw fixes the
builder's balance and pending total, and the solver picks a `bidAmount` on
each side of the bound.

**Seed.** Applies when the line names seeds (§14.3). A seed fixes some inputs
to author-written terms, serialized through the probe (`probe.seeds`).
When the seeds cover every input, the candidate is the seeds themselves,
checked like any other. When they cover a strict subset, the source
answers `nothing` and the bit-vector source takes the partial assignment
for the rest. The seed is one assignment and the prepare pass may split
the theorem into several cases (§8.2), so the author's claim is per
theorem: a fully covering seed that wins no case is a build error, and a
case the seed fails falls through to the next source like any other
candidate. A partial seed carries no claim of that strength; when no
source finds a witness around it, the case reports `notFound`.

### 9.5 Generation

`Sampleable.lean` supplies the instances the probe needs:

- hand-written `SampleableExt` and `Shrinkable` for `UInt8` through `UInt64`,
  `Bool`, `Fin n`, and fixed-width `ByteArray`;
- one generic instance for every type with `SSZRepr`, driven by SizzLean's
  type description: each field by its own instance, each list bounded by its
  SSZ limit and by `Gen`'s size parameter, each fixed-length vector at its
  length, and the value rebuilt through the same structure the `SSZRepr`
  instance walks.

The generic instance is what makes a `BeaconState` an input the search
produces on its own. A mainnet state has fixed-length vectors a minimal state
does not (`EPOCHS_PER_HISTORICAL_VECTOR` is 65536 against 64), and shrinking
cannot cut a fixed length. The size parameter bounds the lists, and the
report records the time per record so mainnet cost stays visible.

### 9.6 Shrink

After a witness from the random source passes, `Witness/Shrink.lean` asks
`probe.shrink a` for smaller candidates, in `Shrinkable` order, and keeps the
first one that passes the check. It repeats until no candidate passes or the
budget (`theorem_vectors.shrinkSteps`, default 200) runs out. Scalars found
by the solver are not shrunk, because a solver value is a boundary point and
shrinking would move it. A state from the built source is shrunk by its
knobs and never by its fields (§9.9).

### 9.7 Further sources

One more source fits beside the built source once it exists. **Corpus
pre-states.** The pyspec vectors hold thousands of `pre.ssz` states under
`~/.cache/sizzlean/<tag>-<preset>/`. A source reads the states for the fork
and preset, filters them with the check, and passes survivors to the solver
the way the built source passes a built state. They come from disk and need
no spec run, and some carry valid signatures and matching hashes, which
helps with sparse hypotheses.

It is one more `WitnessSource` value in the list. Nothing else changes.

### 9.8 Hints: the first source

A search can be slow, and its result can change when the search changes. A
**hint** records how a witness was found, with enough data to rebuild the
candidate without searching. It is a hint and nothing more: the check still
decides, and a hint the check rejects sends the case through the full
search.

**The hint source.** `Witness/Hint.lean` supplies a `WitnessSource` that runs
first. It applies when a hint exists for the theorem, preset, and case, and
the mode is not `ignore`. Its `search` rebuilds the candidate through the
probe, and the loop's check validates it like any other candidate. On
success the record's source is `.hinted orig`. On failure the loop continues
with the next source, and the outcome line says the hint failed.

**What a hint holds.** Only what the search decided, never the witness
bytes. A mainnet state is megabytes, and a hint must stay small enough to
commit.

| Source | Hint data |
| --- | --- |
| base | nothing beyond the source tag |
| bit-vector | the scalar literals the solver chose |
| built | the builder name, the knobs, the solved scalars |
| random plus solve | the generator seed, the size, the draw index, the solved scalars |
| seed | nothing beyond the source tag |
| corpus state, when it exists | the vector path and the state root |

The random draw replays from the seed, size, and index, because `Gen` is a
pure function of those. Shrink replays from the same draw. The hint skips
the redraw loop and the solver, which is where the cost is.

**Where hints live.** In the spec half, committed:

```
EthCLSpecs/TheoremVectors/Hints/<fork>/<thm>.json
```

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "fingerprint": "0x…",
  "entries": [
    { "preset": "minimal", "case": 0, "side": true,
      "source": "random", "seed": 7, "size": 8, "draw": 3,
      "scalars": { "builderIndex": "3", "bidAmount": "32000000000" } },
    { "preset": "minimal", "case": 0, "side": false,
      "source": "random", "seed": 7, "size": 8, "draw": 3,
      "scalars": { "builderIndex": "3", "bidAmount": "40000000001" } } ] }
```

The fingerprint is a hash of the statement and the input type names. Scalars
are decimal strings, because a `UInt64` can exceed the integer range a JSON
reader is sure to keep. The file is JSON (§12.3): the generator is its only
reader, and `Lean.Json` gives both directions from the hint structure's
derived instances.

An ordinary build never writes into the source tree, the same rule the
proof-coverage baseline follows. New and replaced hints go to
`<outDir>/hints/<fork>/<thm>.json`, and `just theorem-vectors-hints-update`
copies them over the committed ones. The diff reaches review, so a changed
witness is visible as a changed hint.

**The mode.** One option, `theorem_vectors.hints`:

| Value | Meaning |
| --- | --- |
| `use` (default) | read hints; search when one is missing or fails; write new hints to the output tree |
| `ignore` | search everything; write new hints |
| `require` | a hint that is missing or fails is an error |

**Staleness.** Each hint file carries a fingerprint, a hash of the theorem's
statement and of the input type names. A mismatch does not reject the hint,
because the check decides. The outcome line records `hint: stale-replayed`
or `hint: stale-failed`, so the report shows which hints a spec change
touched. A new field in `BeaconState` changes every random draw of that
fork, and every random hint for the fork goes stale at once. That is the
expected behavior, and one run of the update recipe refreshes them.

**Why hints and the fixed seed both exist.** `theorem_vectors.seed` makes a
build deterministic. A hint adds two things. Cost: a build replays instead
of searching, which matters once mainnet runs. Stability: a new source in
the list, a different draw budget, or a new `Plausible` version would
otherwise change every random witness, and a client that holds the old
vectors would see churn. With hints, a witness changes only when the check
rejects it or when someone runs the update recipe on purpose.

A reused scalar witness (§10) writes a hint for the second preset too, so
its replay does not depend on the first preset having run.

### 9.9 State builders: the `built` source

The state is the hard half of a witness. A random draw produces a state
field by field, and that state breaks invariants the spec maintains: a
validator with an exit epoch before its activation, a slot behind its
checkpoints, a balance list longer than the validator list. A hypothesis
that depends on those invariants is sparse under random draws, and a client
replaying such a vector can reject the state for a reason that has nothing
to do with the theorem.

A **state builder** runs the spec itself to produce a reachable state from a
few knobs. Each fork has a small catalog, and the search tries the catalog
before it draws at random.

**The catalog.** One builder per row, in `EthCLSpecs/TheoremVectors/Builders/<Fork>.lean`:

| Builder | Builds | Knobs used |
| --- | --- | --- |
| `genesis` | the fork's genesis state from generated deposits, every validator active, the way the pyspec's `create_genesis_state` does | `validators`, `balance` |
| `advanced` | `genesis`, then `processSlots` to the target slot, so epoch transitions run and the state carries real justification, committees, and RANDAO mixes | `validators`, `slot` |
| `upgraded` | the parent fork's `advanced` state through the fork's own upgrade, so the fork-specific fields hold the values the upgrade gives them | `validators`, `slot` |
| `withQueue` | `advanced` plus pending deposits, withdrawals, or builder payments appended through the spec's own operations | `validators`, `slot`, `queue` |

Deposits need pubkeys and withdrawal credentials. Under the verify-off
backend any 48-byte value verifies, so a builder derives them from the
validator index, as the pyspec's `pubkeys` list does. A builder that needs a
real signature is outside this catalog. The catalog is per fork: Fulu has no
parent in the repository, so its catalog has no `upgraded` row.

**The interface.** The knobs are one framework type, so the framework half
can enumerate a grid without naming a fork:

```lean
structure Knobs where
  validators : Nat := 8
  slot       : Nat := 0
  balance    : Nat := 32000000000
  queue      : Nat := 0
  deriving Repr, BEq, Hashable
```

A builder is a fork constant of type `[Preset] → [Config] → Knobs → BeaconState`.
The binding lists its builders by name, as it lists the preset constants:

```lean
  builders := #[("genesis",   ``Builders.Gloas.genesis),
                ("advanced",  ``Builders.Gloas.advanced),
                ("upgraded",  ``Builders.Gloas.upgraded),
                ("withQueue", ``Builders.Gloas.withQueue)]
```

The probe gains one function, `build : (builder : Nat) → Knobs → ByteArray`,
which runs the named builder with the preset's instances bound and
serializes the state. A builder is a seed with knobs that every theorem of
the fork gets for free, and it takes the seed's path through the probe.

**The source.** `Witness/Built.lean` supplies the `built` source, between the
bit-vector and random sources. It applies when exactly one input has the
binding's state type. Any other container input is drawn the way the random
source draws it, and the scalars are solved. It walks the knob grid,
cheapest first:

| Step | Builder | Knobs |
| --- | --- | --- |
| 1 | `genesis` | 8 validators |
| 2 | `advanced` | 8 validators, the first epoch boundary |
| 3 | `upgraded` | 8 validators, the first epoch boundary |
| 4 | `advanced` | 16 validators, slot 40 |
| 5 | `withQueue` | 16 validators, slot 40, queue 4 |
| 6 | `advanced` | 64 validators, slot 40 |

For each built state the source evaluates the container-only reads, solves
the scalars with the bit-vector source, and checks, the same loop the random
source runs over a draw. The random source runs only when the grid fails.
The order is right because a built state is reachable and a random one is
not, so a built witness is worth more to a client. The option
`theorem_vectors.builtSteps` caps the grid, and the cap is lower at mainnet
by default, where `advanced` runs the spec over 65536-long vectors.

**Shrinking.** A built state is never shrunk field by field, because that
would break what the builder guaranteed. The source shrinks the knobs
instead: fewer validators, a lower slot, a shorter queue. The grid order is
the shrink order.

**The cache.** A built state is a pure function of the fork, the preset, the
builder, and the knobs, so its bytes are cached in the output tree:

```
<outDir>/built/<fork>/<preset>/<builder>/<validators>-<slot>-<balance>-<queue>.ssz
<outDir>/built/<fork>/<preset>/<builder>/<validators>-<slot>-<balance>-<queue>.stamp
```

Every theorem of the fork shares the entry, so a builder runs once per
build for each grid step it reaches, however many theorems use it. The
cache also outlives the build on a developer machine. The `.stamp` file
holds the Lake trace of the fork's `Builders` module, read from the `.trace`
file beside its `.olean`. Lake folds the traces of every import into that
file, so it changes when the module or anything it imports changes, which
includes the fork body. A spec change therefore invalidates every entry of
that fork, and the next build rebuilds them. `just theorem-vectors-clean` removes the cache with the rest of the
tree. The cache is never committed, because a mainnet entry is megabytes
and CI rebuilds it once per job.

**Hints.** A built witness has the smallest hint of any source: the builder
name, the knobs, and the solved scalars. It stays valid across `Plausible`
versions, because no generator is involved.

---

## 10. Preset binding and witness reuse

The preset is a run parameter. Every theorem in the corpus binds `[Preset]`,
so it holds at every preset. Phase B fixes the instance binders from the
binding, once per preset in the line's list:

| Binder | Bound to |
| --- | --- |
| `[Preset]` | `binding.presets[p].preset` |
| `[Config]` | `binding.presets[p].config` |
| `[HasherTag]` | `binding.hasherTag` |
| `[CryptoBackend]` | `binding.crypto` |

The search runs per preset. Preset constants enter the hypotheses
(`slotsPerEpoch` bounds `initializePtcWindow_lt`), and the preset sets the
length of each vector in the state. A minimal `BeaconState` is not a valid
mainnet state, so a container witness never moves between presets.

Scalar witnesses can move. When every input type is free of the preset
(`Preset.lean` checks that the type's constants do not depend on the fork's
`Preset` class), the witness from an earlier preset goes through the new
preset's `probe.check`. A witness that passes is reused, and the record's
`source` says `.reused minimal`. A witness that fails sends the case to a
fresh search.

---

## 11. The probe and the executor

### 11.1 Why a probe

The search draws container values at run time, inside compiled code. Those
values are not `Expr`s, and turning a mainnet state into an `Expr` literal
would be slow and large. The generator therefore compiles one closed term per
statement and preset, whose type is fixed in the framework half, and
evaluates it once with `evalExpr`. Every later operation is a call on the
resulting value with bytes in and bytes out.

```lean
/-- The compiled face of one statement at one preset. -/
structure Probe where
  /-- `decide (P x)` for one case, on decoded inputs. -/
  check  : (caseIndex : Nat) → Array ByteArray → Bool
  /-- Draw the container inputs; scalars come back as zero bytes. -/
  sample : (seed size : Nat) → Array ByteArray
  /-- Shrink candidates for the container inputs. -/
  shrink : Array ByteArray → Array (Array ByteArray)
  /-- The container-only subterms of the hypotheses, evaluated and serialized. -/
  reads  : Array ByteArray → Array ByteArray
  /-- The author seeds, serialized, with their input positions. -/
  seeds  : Array (Nat × ByteArray)
  /-- The serialized `default` of every input, in binder order: the base
  source's candidate (§9.4). Empty bytes for a type with no default. -/
  defaults : Array ByteArray
  /-- Run the named builder (an index into the binding's catalog) and
  serialize the state it produces. -/
  build  : (builder : Nat) → Knobs → ByteArray
  /-- `f x`, `e x`, the comparison, the roots. -/
  run    : Array ByteArray → Except String ProbeResult
```

### 11.2 Term construction

`Probe.lean` builds the term as an `Expr` tree inside the reader's
telescope scope. `mkLambdaFVars` abstracts the value binders, and a
substitution replaces the instance binders with the binding's constants for
the preset (§10). The decode of each input goes through `ScalarCodec` at
the input's type, which is known as an `Expr` from the statement. The class
fronts `SSZRepr` for every SSZ type and adds `Fin n` as the `uintN 64`
encoding of `Fin.val`, which no `SSZRepr` can carry because a decode must
respect the bound. The output is serialized the same way, or as the UTF-8
bytes of its literal when its type has `ToString` and no `SSZRepr`.

Two rules apply to the evaluated term. It contains no
`match` on `Except` or `EStateM.Result`; it calls precompiled helpers in the
framework half (`runProbeOk`, `runProbeError`, `compareBytes`) that do the
matching. And the term is elaborated once per statement and preset, with the
case index as a runtime argument, so the search loop never re-elaborates.

The spec's functions are in a `precompileModules` library, so `f` runs
native. The probe's own glue is interpreted, and it does little.

### 11.3 Execution per shape

| Shape | `output` | `expected` | `agree` |
| --- | --- | --- | --- |
| `.eq lhs rhs` | `lhs` | `rhs` | bytes equal |
| `.iffTrue lhs q` | `lhs` (one `Bool` byte) | `decide q` | bytes equal |
| `.bound lhs rel b` | `lhs` | empty | `lhs rel b` holds |
| `.runOk act pre ret post` | the post-state from `runPure act pre` | `post` evaluated | `.ok` and bytes equal |
| `.runError act pre err` | empty | `repr err` | `.error` and the error's `repr` equal |

`agree = false` is a build error with both values printed. The kernel proved
them equal, so the difference is a compiler, FFI, or serialization defect.

### 11.4 Roots

`run` returns `hashTreeRoot` for every SSZ input and for the output, under the
bound hasher: the binding's `hasherTag` constant, whether or not the theorem
binds a `[HasherTag]`. The records carry the roots so a format can refer to a
value without decoding it. An SSZ value with no root is a build error, never
an empty root.

---

## 12. Records

A record is the general vector. It holds every fact that any format needs and
nothing that belongs to one format. Formats read records and nothing else.

### 12.1 On disk

```
<outDir>/records/<fork>/<preset>/<thm>/<case>[_t|_f]/
  record.json
  <input>.ssz          one per input, scalars included, named by the binder
  output.ssz           absent for .runError
```

`<thm>` is the theorem's name with the `EthCLSpecs.Proofs.<Fork>.` prefix
removed. `<case>` is the zero-padded case index. `_t` and `_f` mark the
`.iffTrue` side.

### 12.2 `record.json`

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "fork": "gloas",
  "preset": "minimal",
  "target": "EthCLSpecs.Gloas.canBuilderCoverBid",
  "shape": "iffTrue",
  "case": 0,
  "side": true,
  "source": "random",
  "inputs": [
    { "name": "state", "type": "EthCLSpecs.Gloas.BeaconState",
      "value": { "root": "0x…" } },
    { "name": "builderIndex", "type": "EthCLSpecs.Gloas.BuilderIndex",
      "value": { "scalar": "3" } },
    { "name": "bidAmount", "type": "EthCLSpecs.Gloas.Gwei",
      "value": { "scalar": "32000000000" } } ],
  "output": { "name": "output", "type": "Bool", "value": { "scalar": "true" } },
  "error": null }
```

Every value has an `ssz` side file named by the binder. The payload nests
under `value`, one of two forms: a container's `root`, or a scalar's
`scalar` as a string, so a `UInt64` never meets a JSON reader's integer
range. A `.runError` record has `error` in place of `output`.

### 12.3 File formats: JSON inside, YAML outside

Two kinds of file leave the generator, and the reader of each decides its
format.

**The generator's own files** are records, outcomes (§16.1), and hints
(§9.8). The generator and the exe write them and read them back, and no
client sees them. They are JSON through `Lean.Json`, which ships with Lean:
each structure derives `ToJson` and `FromJson`, the printer writes the file,
and the parser reads it. No format code is written for them.

**The client-facing files** are the ones a consumer reads: `meta.yaml` in
the pyspec layout (§13.4) and the function format (§13.3). Other clients'
runners read `meta.yaml` with their YAML parsers, so the generator writes
the form the upstream dumper writes, byte for byte. That dumper writes a
map of scalars as one flow line, `{bls_setting: 1}`, and a map with a
nested collection in block style. It writes a hex value single-quoted,
`root: '0x…'`, so a parser never reads a root as an integer. `meta.yaml`
is a map of scalars and goes out as one flow line. The function format has
no upstream form and goes out in block style, with the value-and-root pair
of an SSZ input inline. `Yaml.lean` is a writer for those two shapes and
nothing else: scalars, decimal literals, single-quoted hex, quoted strings,
nested maps, and lists of scalars or maps. It has no reader, because the
generator never reads a YAML file. A later format that needs `steps.yaml`
or `roots.yaml` adds one shape to the writer.

No YAML library enters the dependency set. The two that exist for Lean 4
are either a self-declared subset with seven commits or a verified parser
three toolchain versions ahead with its own heavy dependencies, and the
generator needs neither a parser nor a full emitter.

### 12.4 Writer and reader

`Record.write : FilePath → VectorRecord → Array ByteArray → IO Unit` writes
the directory. `Record.read : FilePath → IO (VectorRecord × Array ByteArray)`
reads it back. Both are in the framework half, with no fork knowledge, because
they move bytes and names.

### 12.5 The read-back check

After a record is written, the command reads the directory back, hands the
decoded bytes to `probe.run` again, and compares the fresh `ProbeResult` with
the recorded output. This checks the SSZ round trip of every value and the
record writer itself. A mismatch is a build error.

---

## 13. Formats

### 13.1 The format value

```lean
structure RenderEnv where
  outDir   : FilePath
  bindings : String → Option ForkBinding   -- by fork tag

/-- One consumer layout. A first-class value, so the exe can hold the
registry as a list and iterate it. -/
structure VectorFormat where
  name    : String
  accepts : VectorRecord → Bool
  render  : RenderEnv → VectorRecord → Array ByteArray → IO (Array FilePath)
  check   : RenderEnv → VectorRecord → Array FilePath → IO CheckResult

inductive CheckResult where
  | passed
  | failed (detail : String)
  | noConsumer          -- the format has no Lean-side consumer to replay with
```

`VectorFormat` is a structure and not a typeclass, because the exe iterates
a registry, and a list of values iterates where a set of instances does not.
The registry is `Formats.all : Array VectorFormat` in `Format.lean`, and a
new format appends one value.

### 13.2 The render pass

```
for record in records/**:
  for format in Formats.all:
    if format.accepts record:
      paths ← format.render env record bytes
      results[format, record] := format.check env record paths
```

A record no format accepts stays in `records/` and the report lists it.

`render` and `check` are two invocations of the exe (§15), so `render`
writes the rendered paths per record and format to
`<outDir>/formats/manifest.json`, and `check` reads them back: check
receives what render returned.

### 13.3 The function format

Accepts every record with a target: the `function` field names the function
a client exposes, and a record without a target has none to name. Writes
one self-contained file per vector:

```
<outDir>/formats/function/<fork>/<preset>/<target>/<thm>_<case>[_t|_f].yaml
```

```yaml
theorem: EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff
function: EthCLSpecs.Gloas.canBuilderCoverBid
fork: gloas
preset: minimal
shape: iffTrue
inputs:
  state: {ssz: '0x…', root: '0x…'}
  builderIndex: 3
  bidAmount: 32000000000
output: true
source: random
```

SSZ values go in as single-quoted hex with their root, scalars as
literals. The YAML writer renders the file in block style (§12.3). Its
`check` returns
`noConsumer`. The format serves a client that chooses to expose the
function. The theorem name in the file is the point.

### 13.4 The pyspec format

Accepts a `.runOk` or `.runError` record whose target has a handler in
`binding.handlerOf` and whose only input is the state (`binding.stateType`).
Handlers that take a block or an operation are out of scope by §1.2.

```
<outDir>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<thm>_<case>/
  pre.ssz
  post.ssz          absent for .runError, which marks an invalid case
  meta.yaml         {bls_setting: 2, theorem: <name>}
```

The layout is the upstream one with raw `.ssz` in place of `.ssz_snappy`. The
Python harness decompresses before it hands paths to the server, so a
one-line switch in `harness.py` accepts either suffix and snappy stays out of
Lean. The YAML writer renders `meta.yaml` as one flow line, the form the
upstream dumper writes for a map of scalars and the one every client's
runner already reads (§12.3).

### 13.5 The pyspec check

`check` builds a `CaseRequest` from the rendered files, with `post = none`
for an invalid case, and calls `EthCLLib.PySpecTests.runCase` with the
`ForkInterface` from `binding.interface preset`. A `CaseResult` with
`passed = false` is `CheckResult.failed` with the driver's detail line. This
replays the vector through the same path the upstream vectors take.

---

## 14. Selecting theorems and the generator commands

A theorem reaches the generator in one of three ways. The generator file
lists it by name, or discovers it through one of two tags. The file is the
one place that decides, so a reader of the file sees the whole set.

### 14.1 The two tags

**`@[characterizes f]`** already exists (`EthCLLib.Internal.ProofLedger`). It
marks the one theorem that states a function's contract, chosen by a person.
That set is the natural source of vectors: one contract per function, with no
duplicates from the `_toNat` restatements and the supporting lemmas around
it.

**`@[theorem_vectors]`** is new and lives beside it in
`EthCLLib.Internal.ProofLedger`, as a marker in a persistent environment
extension, `theoremVectorsExt`. It carries no code. The `Proofs/` modules
import nothing from `EthCLLib.TheoremVectors`, so `Plausible` and the probe
stay out of the shipped libraries. The tag says: this theorem, whether or
not it is a contract, must produce vectors. The attribute rejects a
declaration that is not a theorem and a theorem outside a registered fork's
proof namespace, the same checks `characterizes` runs.

A tag is a claim. A tagged theorem that produces no vector fails the build,
the way a `theorem_vectors!` line does. A characterized theorem that
produces no vector is a warning, because the tag was written for the proof
ledger and says nothing about witnesses.

### 14.2 `theorem_vectors_fork`

```lean
theorem_vectors_fork EthCLSpecs.TheoremVectors.Bindings.gloas
```

Stores the binding constant's name in a module-local environment extension.
Every later line in the file reads it. A line in a file with no header is an
error. The header is explicit so a reader of the generator file sees which
fork it drives on the first line.

### 14.3 `theorem_vectors`

```lean
theorem_vectors_fork Bindings.gloas

-- named lines: overrides and additions
theorem_vectors canBuilderCoverBid_iff with (state := Seeds.Gloas.coverBidState)
theorem_vectors! processBuilderPendingPayments_run presets minimal mainnet
theorem_vectors initializePtcWindow_lt_default

-- exclusions: theorems the clauses must not select
theorem_vectors skip processOperations_run_ok_iff "block input, needs a body builder"

-- discovery: every theorem of the fork that carries the tag
theorem_vectors characterized
theorem_vectors tagged

-- the survey: every other public theorem of the fork, read and listed
theorem_vectors survey
```

Grammar:

```
theorem_vectors characterized [presets <presetId>+]
theorem_vectors tagged        [presets <presetId>+]
theorem_vectors survey
theorem_vectors[!] <ident> [with (<input> := <term>)+] [presets <presetId>+]
theorem_vectors skip <ident> <string>
```

- `characterized` selects every `@[characterizes]` theorem whose target the
  binding's fork owns (`Capture.specFunctionOwner?`). `tagged` selects every
  `@[theorem_vectors]` theorem under the fork's proof namespace. Each runs
  with the default budget, the default seeds (none), and the clause's preset
  list.
- `survey` takes every public theorem under the fork's proof namespace that
  no other clause or line selects, runs phase A alone (§3), and writes an
  outcome line with status `unselected`. It never searches a witness and
  never writes a record. It exists so the report shows the whole corpus: a
  reader sees which theorems the lines leave out and what the reader made
  of them. It takes no `presets` clause, because nothing runs per preset.
- `<ident>` resolves to a theorem in the environment, under the fork's proof
  namespace or fully qualified.
- `with` names seeds: one term per input, `[Preset]`-generic, elaborated at
  each preset. A seed for an input the theorem does not have is an error.
- `presets` lists the presets to run. The default is `minimal`.
- `!` turns every skip into an error. A tagged theorem is strict without it.
- `skip` excludes a theorem from discovery and records the reason in the
  outcome file. A `skip` validates against the potential selection, the
  tags of §14.1 and the fork's proof namespace, so a stale exclusion is
  still visible and the line can sit above the clauses it excludes from.

**Precedence.** Each line elaborates as its own command, in file order. A
named line wins over discovery for the same theorem, and one theorem runs
once, so an override never produces a second record set. Two named lines
for one theorem are an error, and so are a named line and a skip line for
one theorem: the skip would overwrite the named run's outcome. The
outcome line records the origin:
`named`, `tagged`, `characterized`, `skipped`, or `survey`.

**Order.** The named lines and the `skip` lines come before the discovery
clauses in the file. Named lines run in file order, then the discovered
set in name order, with the skips and named lines removed. A named line
or a `skip` line after a discovery clause that already ran its theorem is
an error, and the message says to move the line up: a discovery run of
that theorem would run it without the seeds, warn, and then run it again,
or run it and lose the exclusion. A line a precedence rule rejects leaves
no state: the elaborator records it only after its pass succeeded, so a
later line meets only the lines above it that passed.

Each per-preset run of phases B1 through B8 (§3) carries its own
heartbeat budget (`theorem_vectors.maxHeartbeats`, §14.4), which the
command sets around it. The run writes records, then one outcome line
(§16). Per record the command logs one info message with the path. Per
skipped preset it logs one warning with the reason, or an error for a
strict theorem.

**What this buys.** A new `@[characterizes]` proof gets a vector attempt on
the next build, and the report lists it with its outcome. An author who wants
a lemma's vectors adds one tag at the proof. The generator file still shows
every seed, every strict line, and every exclusion with a reason. Cost stays
bounded, because the discovered set runs with the default budget and a
theorem that needs more gets a named line.

### 14.4 Options

| Option | Default | Meaning |
| --- | --- | --- |
| `theorem_vectors.outDir` | `theorem_vectors` | the output root; the lakefile fixes it |
| `theorem_vectors.maxCases` | 16 | the DNF cap (§8.2) |
| `theorem_vectors.maxHeartbeats` | 1000000 | the heartbeat budget per run, in the units `set_option maxHeartbeats` takes; the command multiplies by 1000 for the reader field |
| `theorem_vectors.randomDraws` | 64 | redraws for the random source |
| `theorem_vectors.randomSize` | 8 | `Gen`'s size parameter |
| `theorem_vectors.shrinkSteps` | 200 | the shrink budget |
| `theorem_vectors.seed` | 0 | the random seed, so a build is reproducible |
| `theorem_vectors.hints` | `use` | `use`, `ignore`, or `require` (§9.8) |
| `theorem_vectors.builtSteps` | 6 at minimal, 3 at mainnet | how far down the builder grid the `built` source walks (§9.9) |

### 14.5 Concurrency

Lake elaborates modules in parallel. Each generator file writes under its own
`records/<fork>/`, `outcomes/<fork>/`, `hints/<fork>/`, and `built/<fork>/`
subtrees, so two files never write the same path. Theorems inside one file
run in order.

---

## 15. The command-line harness

`lake exe theorem_vectors` lives in `EthCLSpecs/TheoremVectors/Main.lean`. It
needs the fork bindings for the pyspec check, so it lives in the spec half,
as `pyspec_server` does. It never elaborates a theorem; the records are its
input.

```
theorem_vectors render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]
theorem_vectors check  [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]
theorem_vectors report [--out <dir>]
theorem_vectors list   [--out <dir>]
```

| Subcommand | Does | Exit code |
| --- | --- | --- |
| `render` | phase C1 over the selected records | 0, or 1 when a render throws |
| `check` | phase C2 over the rendered vectors | 0, or 1 when any check fails |
| `report` | phase C3; writes `report.md` | 0 |
| `list` | prints one line per record, for scripts | 0 |

`--out` defaults to `packages/EthCLSpecs/theorem_vectors`, the same path the
lakefile fixes for the commands. The exe imports `Bindings.lean` and
`Formats.all`, and builds the `RenderEnv` from them.

---

## 16. The report

### 16.1 Outcome lines

The command writes one file per theorem:

```
<outDir>/outcomes/<fork>/<thm>.json
```

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "target": "EthCLSpecs.Gloas.canBuilderCoverBid",
  "shape": "iffTrue",
  "origin": "named",
  "blockInputs": [],
  "cases": 2,
  "runs": [
    { "preset": "minimal", "status": "written", "records": 2,
      "source": "random", "hint": "replayed", "seconds": 4.1 },
    { "preset": "mainnet", "status": "skipped",
      "reason": "notFound after base, bitVec, built, random" } ] }
```

`origin` is one of `named`, `tagged`, `characterized`, `skipped`, `survey`.
`status` is one of `written`, `skipped`, `outOfScope`, `unsat`,
`unsupported`, `unselected`. A `survey` line has one run with status
`unselected`, or `unsupported` with the reader's reason, and no preset
field. `hint` is
one of `replayed`, `stale-replayed`, `failed`, `stale-failed`, `missing`,
`ignored`. The file is JSON (§12.3).

### 16.2 `report.md`

`report` folds the outcome files and the records into one Markdown file with
one table per fork:

| Theorem | Origin | Shape | Preset | Status | Source | Hint | Records | Formats | Seconds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |

followed by a list of records no format accepted and a list of theorems with
block inputs. The summary line above the tables counts the theorems with
outcomes, the box lemmas (§7.3), and the theorems with block inputs, so
the other `.unsupported` rows read as the shape gaps they are. The report
is the review surface: a reader sees which theorems produce vectors, which
do not, and why.

---

## 17. Build integration

### 17.1 Output tree

```
packages/EthCLSpecs/theorem_vectors/        gitignored
  records/<fork>/<preset>/<thm>/<case>/
  outcomes/<fork>/<thm>.json
  hints/<fork>/<thm>.json                  new and replaced hints, for the update recipe
  built/<fork>/<preset>/<builder>/         the built-state cache, bytes and stamps
  formats/function/<fork>/<preset>/<target>/
  formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/
  report.md
```

`.gitignore` gains `packages/EthCLSpecs/theorem_vectors/`. The committed
hints live in the source tree under `EthCLSpecs/TheoremVectors/Hints/`.

### 17.2 Justfile

```
# Generate the records (runs the generator files), render, check, report
theorem-vectors:
    lake build EthCLSpecsTheoremVectors
    lake exe theorem_vectors render
    lake exe theorem_vectors check
    lake exe theorem_vectors report

# Remove the output tree and the generator modules' build outputs, so the
# next build regenerates. Lake tracks the modules, not the files they write.
theorem-vectors-clean:
    rm -rf packages/EthCLSpecs/theorem_vectors
    rm -rf packages/EthCLSpecs/.lake/build/lib/lean/EthCLSpecs/TheoremVectors/Generators

# Copy the hints the last build wrote over the committed ones. Commit the diff.
theorem-vectors-hints-update:
    cp -r packages/EthCLSpecs/theorem_vectors/hints/. packages/EthCLSpecs/EthCLSpecs/TheoremVectors/Hints/

# Search everything again, with the committed hints ignored, then update them.
theorem-vectors-hints-rebuild:
    just theorem-vectors-clean
    THEOREM_VECTORS_HINTS=ignore lake build EthCLSpecsTheoremVectors
    just theorem-vectors-hints-update
```

The clean recipe exists because a deleted output directory stays empty until
the generator modules rebuild. Removing their build outputs forces that. The
rebuild recipe sets the hint mode through the environment variable
`THEOREM_VECTORS_HINTS`, which the command reads ahead of the
`theorem_vectors.hints` option. A declarative `lakefile.toml` cannot pass a
command-line key to an option, and the variable keeps the lakefile
declarative.

### 17.3 CI

One job, `theorem-vectors`, after the `ethcl` build:

1. `just theorem-vectors`, with hints in `use` mode. A `theorem_vectors!`
   skip, a tagged theorem's skip, a failed agreement check, a failed
   read-back, or a failed pyspec check fails the job. A stale or failed hint
   does not, and the report lists it. A job that wants to catch unreviewed
   witness churn runs with `require` instead.
2. Upload `theorem_vectors/` as an artifact, so the vectors and the report
   are available per commit.

### 17.4 The pyspec harness switch

`harness.py` accepts `.ssz` where it finds no `.ssz_snappy`. With that, the
pyspec format's output tree can be pointed at the harness directly
(`--vectors <outDir>/formats/pyspec`) and runs through the same `pytest`
path as the upstream corpus.

---

## 18. Failure policy

| Event | Phase | Effect |
| --- | --- | --- |
| theorem name does not resolve | A1 | error |
| two named lines for one theorem | A0 | error |
| `skip` for a theorem no discovery clause could select | A0 | error |
| named or skip line below the clause that ran its theorem | A0 | error |
| a named line and a skip line for one theorem | A0 | error |
| `.unsupported` shape | A1 | skip (error under `!` or `@[theorem_vectors]`) |
| block input, base source fails | B3 | `outOfScope` skip (error under `!` or the tag) |
| solver proves `¬P` | B3 | `unsat` skip, always reported |
| sources exhausted | B3 | `notFound` skip (error under `!` or the tag) |
| fully covering seed wins no case | B3 | error |
| partial seed, no source finds a witness | B3 | `notFound` skip |
| hint fails the check, mode `use` | B3 | full search, `hint: failed` in the outcome |
| hint missing or fails, mode `require` | B3 | error |
| `agree = false` | B5 | error, both values printed |
| read-back mismatch | B7 | error |
| no format accepts a record | C1 | listed in the report |
| pyspec check fails | C2 | `check` exits 1 |
| DNF cap hit | A3 | warning, unsplit fallback |

The rule behind the table: a claim the author made (`!`, the tag, a seed)
fails hard.
A fact about the theorem (`unsat`, `notFound`, `unsupported`) is reported. A
disagreement between the kernel and the compiled code always fails hard.

---

## 19. Extension points

Each row adds code and edits none of the existing pipeline.

| To add | Write | Touch |
| --- | --- | --- |
| a fork | `Bindings/<Fork>.lean`, `Generators/<Fork>.lean` | the bindings table |
| a preset | one `PresetId` constructor, one entry per binding | `Types.lean`, the bindings |
| a witness source | one `WitnessSource` value | the source list |
| a format | one `VectorFormat` value | `Formats.all` |
| a shape | one `Shape` constructor, one reader arm, one executor row | `Statement`, `Execute` |
| a seed | one `def` in `Seeds/<Fork>.lean` | the generator line |
| a state builder | one `def` in `Builders/<Fork>.lean` | the binding's `builders` list |
| a theorem | `@[characterizes]` or `@[theorem_vectors]` on the proof, or one named line | nothing else |
| an exclusion | one `theorem_vectors skip` line with a reason | nothing else |

A shape is the one addition that touches two modules. The reader must
recognize it and the executor must know its output. Both arms are exhaustive
matches, so a missing arm is a build error.

---

## 20. Glossary

- **Theorem vector.** One input that satisfies a theorem's hypotheses, plus
  the recorded output of the function under test.
- **Statement.** The parsed theorem type: inputs, hypotheses, target, shape.
- **Shape.** The form of the conclusion. One of `eq`, `iffTrue`, `bound`,
  `runOk`, `runError`.
- **Case.** One conjunction of hypotheses the search solves, from the DNF
  split, with a side for `iffTrue`.
- **Witness.** An assignment of SSZ bytes to every input that passes the
  check.
- **Witness source.** One strategy that proposes witnesses. The sources run
  in a fixed order, cheapest first.
- **Check.** Compiled `decide P` on a candidate. The single arbiter.
- **Hint.** A committed note of how a witness was found, enough to rebuild
  the candidate without a search. The check still decides.
- **State builder.** A fork function that runs the spec to produce a
  reachable state from a few knobs. The `built` source walks a catalog of
  them, and the output tree caches their bytes.
- **Probe.** The compiled face of one statement at one preset: check, sample,
  shrink, reads, seeds, build, run.
- **Survey.** The generator clause that reads every public theorem the
  other lines leave out and lists it with status `unselected`. It never
  searches a witness.
- **Box lemma.** A theorem whose conclusion is a framework predicate about
  the box discipline (`KeepsUncached`, `ReturnsUncached`). No vector
  expresses it, and the report counts it apart.
- **Binding.** The `ForkBinding` value through which the framework half sees
  a fork.
- **Record.** The general vector on disk: `record.json` plus SSZ files.
- **Format.** A renderer from records to one consumer's layout, with a check.
- **Generator file.** A module in the spec half that selects a fork's
  theorems: discovery clauses, named lines, and exclusions.
- **Discovery.** Selecting theorems through a tag, `@[characterizes]` or
  `@[theorem_vectors]`, in place of a named line.
- **Outcome.** The per-theorem, per-preset result line the report folds.
- **Byte boundary.** The rule that every value between the elaborator and
  compiled code is SSZ bytes.
