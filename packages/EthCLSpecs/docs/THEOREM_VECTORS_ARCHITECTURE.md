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

The scope rule has one exception that costs nothing. The base searcher (§9.4)
still runs on a theorem with a block input. If `default` satisfies `P`, the
vector is written. If it does not, the theorem is reported out of scope and no
other searcher runs.

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
│    reader, prepare, witness searchers, probe, executor, records,         │
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
# The generator's spec half: fork bindings, state builders, and
# the generator files whose elaboration writes the records. The
# output directory is fixed here so the command never depends on the
# working directory Lake
# gives it. The `weak.` prefix defers the setting until the module that
# registers the option is imported; `lean` rejects a `-D` for an option it
# has not seen yet.
[[lean_lib]]
name = "EthCLSpecsTheoremVectors"
roots = ["EthCLSpecs.TheoremVectors"]
leanOptions = [
  { name = "weak.theorem_vectors.outDir", value = "packages/EthCLSpecs/theorem_vectors" },
  # The committed hints the hint searcher reads (§9.8); the update recipe
  # copies the output tree's hints over this directory.
  { name = "weak.theorem_vectors.hintsDir", value = "packages/EthCLSpecs/EthCLSpecs/TheoremVectors/Hints" },
]

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
 A2 Scope     block input? → only the base searcher may run            §7.4
        ▼
 A3 Prepare   unfold spec predicates, split P into DNF disjuncts,
              add the Q / ¬Q side for .iffTrue → Array Disjunct         §8
        │
════════╪═══ Phase B: per preset ═════════════════════════════════════════════
        ▼
 B1 Bind      fix [Preset] [Config] [HasherTag] [CryptoBackend];
              build and evaluate the Probe for this preset              §10, §11
        ▼
 B2 Reuse     a scalar witness from an earlier preset passes check? → B5 §10
        ▼
 B3 Search    witness searchers in order, the committed hint first,
              each candidate through check                              §9
        ▼
 B4 Shrink    smaller inputs while check still holds                    §9.6
        ▼
 B5 Execute   probe.run: f x, e x, compare, serialize, roots            §11
        ▼
 B6 Record    one VectorRecord directory per disjunct, and its hint     §12, §9.8
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
| `Types.lean` | `PresetId`, `ShapeTag`, `WitnessSearcherTag`, `Failure`, `ValueData`, `BoundRel`, `Knobs` | Lean core |
| `Scalar.lean` | the scalar kinds, their wire widths, and their literal forms | Lean core |
| `ForkBinding.lean` | the `ForkBinding` structure and `PresetInstances` | `Types`, `PySpecTests.Interface` |
| `Statement.lean` | `Statement`, `Shape`, the reader over a theorem type | `Types`, `Internal.Capture` |
| `Scope.lean` | the block-input walk over input types | `Statement`, `ForkBinding` |
| `Prepare.lean` | unfold, normalize, DNF split, sides → `Array Disjunct` | `Statement` |
| `Sampleable.lean` | `SampleableExt` and `Shrinkable` for scalars and SSZ containers | `Plausible`, `SizzLean` |
| `Probe.lean` | the `Probe` structure and the term builder that produces it | `Statement`, `Prepare`, `ForkBinding`, `Sampleable` |
| `Witness/Searcher.lean` | `WitnessSearcher`, the search loop, the check | `Probe` |
| `Witness/Base.lean` | the `default` searcher | `Witness.Searcher` |
| `Witness/BitVec.lean` | the `bvDecide'` searcher and the counterexample reader | `Witness.Searcher` |
| `Witness/Built.lean` | the state-builder searcher, the knob grid, the built-state cache | `Witness.Searcher`, `Witness.BitVec` |
| `Witness/Random.lean` | the random-state-plus-solve searcher | `Witness.Searcher`, `Witness.BitVec` |
| `Witness/Manual.lean` | the manual searcher (the author's manual terms) | `Witness.Searcher` |
| `Witness/Shrink.lean` | the shrink loop | `Probe`, `Prepare` |
| `Witness/Hint.lean` | the hint schema, reader, writer, fingerprint, and the hint searcher | `Witness.Searcher`, `Lean.Json` |
| `Preset.lean` | bind one preset, the reuse check | `Probe`, `ForkBinding` |
| `Execute.lean` | per-shape outcome from probe runs, the agreement check | `Probe` |
| `Record.lean` | `VectorValue`, `VectorRecord`, writer, reader | `Types`, `Lean.Json` |
| `Yaml.lean` | the YAML writer for the client-facing files (§12.3) | Lean core |
| `Snappy.lean` | the snappy block-format writer, all-literals form | Lean core |
| `Format.lean` | the `VectorFormat` structure and `RenderEnv` | `Record`, `ForkBinding` |
| `Formats/Function.lean` | the function format | `Format`, `Yaml` |
| `Formats/Pyspec.lean` | the pyspec format and its `runCase` check | `Format`, `Yaml`, `PySpecTests.Driver` |
| `Formats/Operations.lean` | the operations format and its `runCase` check | `Format`, `Formats/Pyspec`, `PySpecTests.Interface`, `PySpecTests.Driver` |
| `Outcome.lean` | the per-theorem outcome lines | `Types`, `Lean.Json` |
| `Report.lean` | `report.md` from outcomes and records | `Outcome`, `Record` |
| `Command.lean` | `theorem_vectors_fork`, `theorem_vectors` with its discovery, named, and `skip` forms | everything above except `Formats`, `Report`; `Internal.ProofLedger` for the two tags |
| `TheoremVectors.lean` | the library root, re-exports | all |

Each module does one thing. `Statement` reads. `Prepare` rewrites. `Probe`
compiles. `Witness/*` searches. `Execute` runs. `Record` persists. `Format`
renders. `Command` sequences.

Three pieces sit outside the library, under `EthCLLib/Internal/`. The
`@[theorem_vectors]` attribute and its extension, `theoremVectorsExt`, live
in `EthCLLib.Internal.ProofLedger` beside `@[characterizes]`.
`EthCLLib.Internal.Binders` holds the shared binder sort (`BinderRole`,
`binderRole`); the statement reader and the manual-terms command both sort
through it, so the two cannot disagree about what an input is.
`EthCLLib.Internal.ManualTerms` holds the `theorem_vectors_manual` command
and its ledger (`manualTermsExt`, `manualTermsOf`, §14.6). A proof module
imports `ProofLedger` already, and none of the three pulls in anything from
the generator (§14.1).

### 4.2 The spec half: `EthCLSpecs/TheoremVectors/`

| Module | Responsibility |
| --- | --- |
| `Bindings/Fulu.lean`, `Bindings/Gloas.lean`, `Bindings/Heze.lean` | one `ForkBinding` value per fork |
| `Bindings.lean` | the table the exe uses: fork tag → `ForkBinding` |
| `Builders/Fulu.lean`, `Builders/Gloas.lean`, `Builders/Heze.lean` | the state-builder catalog per fork (§9.9) |
| `Generators/Fulu.lean`, `Generators/Gloas.lean`, `Generators/Heze.lean` | the generator lists |
| `Hints/<fork>/<thm>.json` | the committed hints, one file per theorem (§9.8) |
| `Main.lean` | the exe: `render`, `check`, `report` |
| `TheoremVectors.lean` | the library root, imports the bindings, builders, and generators |

A generator file imports `EthCLSpecs.Proofs.<Fork>` and its fork's binding.
The registration under a theorem sits in the theorem's own module (§14.6),
so the proof file carries the witness terms and no generator file names a
term. The binding imports its fork's builders, because it names
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
          │        │       │  ├─ Formats/Pyspec ◄────┘
          ▼        ▼       ▼  └─ Formats/Operations
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
  reading `runPure act pre = .ok (ret, post)`. One vector; the output is
  `ret` when its type names the state container (a value-style mutator),
  the post-state otherwise. Stage 10 records the rule's reason. -/
  | runOk (act pre ret post : Expr)
  /-- `act.run (pureState pre) = .error err`, or the `runPure` reading
  `runPure act pre = .error err`. One vector with no post-state. -/
  | runError (act pre err : Expr)
  /-- Anything else, with the reason. -/
  | unsupported (reason : String)

inductive ShapeTag where
  | eq | iffTrue | bound | runOk | runError
  deriving DecidableEq, Repr
```

### 5.4 Disjuncts, assignments, searchers, failures

```lean
/-- One search problem: a conjunction of hypotheses over the inputs. The
prepare pass produces one per DNF disjunct, times two for `.iffTrue`. -/
structure Disjunct where
  index : Nat
  side  : Option Bool          -- `.iffTrue` only
  hyps  : Array Expr           -- conjuncts, binders still free

/-- A closed value for every input, in binder order, as SSZ bytes. -/
abbrev Assignment := Array ByteArray

inductive WitnessSearcherTag where
  | base | bitVec | built | random | manual
  | reused (from : PresetId)
  /-- Rebuilt from a committed hint; `orig` is the searcher the hint recorded. -/
  | hinted (orig : WitnessSearcherTag)
  deriving Repr

inductive Failure where
  /-- The solver proved `¬P` with no state input in play. The theorem is vacuous. -/
  | unsat
  /-- Every searcher ran out. The author registers manual terms under the
  theorem (§14.6). -/
  | notFound (tried : Array WitnessSearcherTag)
  /-- A block input and the base searcher failed (§1.2). -/
  | outOfScope (inputs : Array Name)
```

### 5.5 Outcomes of execution

```lean
/-- What one probe run produced. All values cross the boundary as SSZ bytes. -/
structure ProbeResult where
  output        : ByteArray                -- `f x`, or a `.runOk`'s picked side, serialized
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
  thm             : Name
  fork            : String               -- the binding's tag, such as "gloas"
  preset          : PresetId
  target          : Name
  shape           : ShapeTag
  disjunctIndex   : Nat
  side            : Option Bool
  inputs          : Array VectorValue
  output          : Option VectorValue   -- `none` for `.runError`
  error           : Option String        -- `.runError` only: the error's `repr`
  witnessSearcher : WitnessSearcherTag
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
  /-- The pyspec spelling of the fork's spec functions: the full Lean name
  to the snake-case name clients consume. One row per function the fork
  declares with a pyspec spelling; the inherited replays carry none.
  Validated once, at the generator header. -/
  pyspecNames : Array (Name × String)
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

The reader also reads the target's pyspec name: the fork binding's
`pyspecNames` table maps the target's full Lean name to the snake-case
spelling clients consume (§6), and §13.3's `function` field carries it.
A target with no row has no pyspec name, and the record's field is null.

### 7.3 Shape matching

After the telescope, the body is matched in this order:

1. `Iff (Eq lhs true) q` → `.iffTrue lhs q`
2. `Eq (StateT.run act (pureState pre)) (Except.ok (ret, pureState post))` → `.runOk`
3. `Eq (runPure act pre) (Except.ok (ret, post))` → `.runOk`
4. `Eq (StateT.run act (pureState pre)) (Except.error err)` → `.runError`
5. `Eq (runPure act pre) (Except.error err)` → `.runError`
6. `Eq lhs rhs` → `.eq lhs rhs`
7. `LT.lt lhs b` → `.bound lhs .lt b`; `LE.le lhs b` → `.bound lhs .le b`
8. anything else → `.unsupported` with the head constant in the reason

Rule 8 names one family: a conclusion whose head is a framework predicate
under `EthCLLib.Proofs` (`KeepsUncached`, `KeepsUncachedFrom`,
`ReturnsUncached`) is a box lemma. It states a fact about the box
discipline of a spec function, and no input and output pair expresses it.
The reason reads `box lemma: <head>`, and the report counts these apart
from the other `.unsupported` reasons (§16.2), because they are not a gap
in the shape set.

The run matches, forms 2 through 5, require the run's state to be one of
the statement's state-typed value inputs. A state-typed value binder is a
binder whose type names the binding's `stateType`. The `.runOk` post-state
must be a closed term over the inputs. A theorem whose post-state is an
existential (`∃ s', …`) is `.unsupported`, because the executor cannot
evaluate `e x`. The repository's contract theorems state the whole
post-state as a value (`SPECS_ARCHITECTURE.md` §11.1.1), so this covers
them. A theorem may bind several states: the Fulu balance theorems read
one and thread another, so the type identifies the run's state whatever
the binder's position.

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
| non-empty `blockInputs` | scope restriction: only the base searcher runs |
| an `.other` instance binder | a skip: the command cannot bind an unknown seam |
| a function-typed input | a skip |

---

## 8. The prepare pass

Input: a `Statement`. Output: `Array Disjunct`.

### 8.1 Unfold

A hypothesis stated through a spec predicate, such as
`¬ isSlashableAttestationData a b`, is one opaque atom to a bit-vector solver
and to a random filter alike. The pass runs `simp only` with three lemma sets:

- the equation lemmas of every spec predicate the hypothesis names, found
  through the capture extension, when the predicate's body is small
  (under 100 expression nodes). A body that folds over a state container
  unfolds into a term the simp walk cannot finish, so the pass leaves it
  as one atom, and the bit-vector searcher grounds the closed call in
  compiled code instead (§9.4);
- the `UInt64`-to-`Nat` bridge lemmas the proofs already use
  (`UInt64.lt_iff_toNat_lt`, `UInt64.le_iff_toNat_le`, and their siblings),
  oriented back toward `UInt64` form;
- `Bool` normalization (`decide_eq_true_eq`, `Bool.and_eq_true`, and the rest).

Crypto predicates stay as they are. Under the verify-off backend the probe
evaluates them, so the solver never needs to see inside one. A disjunct whose gate negates a crypto predicate is unsatisfiable under
that backend. The solver never sees inside the gate, so the disjunct
reports `notFound`, never `unsat`.

### 8.2 Split

The unfolded conjunction is put in disjunctive normal form. Each DNF
disjunct becomes one `Disjunct`. A hypothesis that unfolds to three
branches yields three disjuncts, and the disjunct index goes into the
record's path. Boundary points fall out of the split: `a < b ∨ a = b` gives
the solver two goals, and the equality disjunct is the boundary.

The pass has a disjunct cap (option `theorem_vectors.maxDisjuncts`, default
16). A theorem over the cap reports the count and falls back to one
disjunct with the unsplit hypothesis.

### 8.3 Sides

For `.iffTrue lhs q`, every disjunct is doubled: one copy adds `q` to its
hypotheses with `side := some true`, the other adds `¬q` with
`side := some false`. The witness for the `¬q` side is a witness of the
negation, which the searchers handle the same way.

### 8.4 Decidability

Every disjunct must be decidable, because every searcher ends with `decide`
on the candidate. The pass synthesizes `Decidable` for the disjunct's
conjunction once, and a disjunct that fails synthesis is reported and
dropped.

---

## 9. The witness search

Input: the probe for one preset and one `Disjunct`. Output: an `Assignment`
or a `Failure`. The design of record for the search lives in
[THEOREM_VECTORS_SEARCH.md](THEOREM_VECTORS_SEARCH.md), which carries §9's
subsections under their own numbers; the subsections below state each
part's rule in one line and point there.

### 9.1 The byte boundary

Every value that crosses between the elaborator and compiled code is SSZ
bytes; a witness is `Array ByteArray`, one entry per input in binder
order, and the probe (§11) decodes inside compiled code. See the search
document §1.

### 9.2 The searcher interface

`WitnessSearcher = tag + applies + search`; the loop walks hint, then
reuse (§10), then the line's tail, and the check is the single arbiter.
`notFound` names every searcher that ran. See §9.2 in the search document.

### 9.3 The check

`probe.check` is compiled `decide (P x)` per disjunct, never throws, and
decodes strictly. See §9.3 in the search document.

### 9.4 The core searchers

Base (never `default` for the state type), bit-vector (grounding, the
coupled grid, `unsat` only on a theorem with no manual terms), random plus
solve (draws, read grounding, the safe face, `randomDraws`, the mainnet
cap), manual (the terms registered under the theorem, §14.6). See §9.4 in
the search document.

### 9.5 Generation

`SampleableExt` instances, per-position and per-draw seed mixing, and the
generic SSZ-driven instance. See §9.5 in the search document.

### 9.6 Shrink

One shape step per container input, the wire-size bound, solver scalars
not shrunk, built states shrunk by knobs. See §9.6 in the search document.

### 9.7 Further searchers

Corpus pre-states as one more `WitnessSearcher`. See the search document
§7.

### 9.8 Hints: the first searcher

A hint holds how a witness was found, never the bytes: the fingerprint,
the modes, the staleness spellings, and the merge and update rules. See
the search document §8.

### 9.9 State builders: the `built` searcher

The catalog, the knob grid, the cache with its `.stamp`, shrink by knobs.
See §9.9 in the search document.

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
`witnessSearcher` says `reused-minimal`. A witness that fails sends the
disjunct to a fresh search.

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
  /-- `decide (P x)` for one disjunct, on decoded inputs. -/
  check  : (disjunctIndex : Nat) → Array ByteArray → Bool
  /-- Draw the container inputs; scalars come back as zero bytes. -/
  sample : (seed size : Nat) → Array ByteArray
  /-- One input position's draw alone. The bytes depend on the seed, the
  size, and the position, so the built searcher and a hint's replay sample
  the side containers without sampling the state (§9.4). -/
  sampleAt : (seed size pos : Nat) → ByteArray
  /-- Shrink candidates for the container inputs. -/
  shrink : Array ByteArray → Array (Array ByteArray)
  /-- One disjunct's container-reading subterms, evaluated at the
  candidate's bytes and serialized, in the walk's order (§9.4). -/
  reads  : (disjunctIndex : Nat) → Array ByteArray → Array ByteArray
  /-- Per entry of one disjunct's read plan, whether every `!`-read's
  index stays inside its collection at the candidate's bytes (§9.4). The
  face evaluates the indexes and the lengths alone, so it cannot panic. -/
  safe   : (disjunctIndex : Nat) → Array ByteArray → Array Bool
  /-- The author's manual terms, serialized, with their input positions. -/
  manuals : Array (Nat × ByteArray)
  /-- The serialized `default` of every input, in binder order: the base
  searcher's candidate (§9.4). Empty bytes for a type with no default. -/
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
disjunct index as a runtime argument, so the search loop never re-elaborates.

The spec's functions are in a `precompileModules` library, so `f` runs
native. The probe's own glue is interpreted, and it does little.

### 11.3 Execution per shape

| Shape | `output` | `expected` | `agree` |
| --- | --- | --- | --- |
| `.eq lhs rhs` | `lhs` | `rhs` | bytes equal |
| `.iffTrue lhs q` | `lhs` (one `Bool` byte) | `decide q` | bytes equal |
| `.bound lhs rel b` | `lhs` | empty | `lhs rel b` holds |
| `.runOk act pre ret post` | `ret` when its type names the state container, else the post-state | `post`, or `ret` matching the pick | `.ok` and bytes equal |
| `.runError act pre err` | empty | `repr err` | `.error` and the error's `repr` equal |

The `.eq` face has one further rule, the projected output rule. When the
output type has no `SSZRepr` and no `ToString`, and it wraps the run's
return, an `Except ε β` whose pair's first component names the state
container, each side records through that component. The pick is the
`.runOk` rule's own: the pair's first component read through the box's
`.view`, recorded at the container's type. One compiled body answers both
point kinds, because a won point can be of either kind. At an `.ok` point
the record is the picked value's bytes against the other side's, with its
root. At an `.error` point the row follows the `.runError` rule: no output
value, and the actual side's error repr in the error slot. The agreement
guard compares what the projection rendered on each side, the bytes at
`.ok` points and the two reprs at `.error` points. The recorded output
type names the picked value's container (§12.2).

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
<outDir>/records/<fork>/<preset>/<thm>/<index>[_t|_f]/
  record.json
  <input>.ssz          one per input, scalars included, named by the binder
  output.ssz           absent for a .runError record, or a projected-.eq record at an error-valued point
```

`<thm>` is the theorem's name with the `EthCLSpecs.Proofs.<Fork>.` prefix
removed. `<index>` is the zero-padded disjunct index. `_t` and `_f` mark
the `.iffTrue` side.

### 12.2 `record.json`

```json
{ "theorem": "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff",
  "fork": "gloas",
  "preset": "minimal",
  "target": "EthCLSpecs.Gloas.canBuilderCoverBid",
  "pyspecName": "can_builder_cover_bid",
  "shape": "iffTrue",
  "disjunctIndex": 0,
  "side": true,
  "witnessSearcher": "random",
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
range. A `.runError` record, or a projected-`.eq` record at an error-valued
point, has `error` in place of `output`. `pyspecName`
carries the pyspec name the fork binding's `pyspecNames` table maps the
target to (§7.2), null when there is no row; a client-conformance harness
maps on it.

### 12.3 File formats: JSON inside, YAML outside

Two kinds of file leave the generator, and the reader of each decides its
format.

**The generator's own files** are records, outcomes (§16.1), and hints
(§9.8). The generator and the exe write them and read them back, and no
client sees them. They are JSON through `Lean.Json`, which ships with Lean:
each structure derives `ToJson` and `FromJson`, the printer writes the file,
and the parser reads it. No format code is written for them.

**The client-facing files** are the ones a consumer reads: `meta.yaml` and
`manifest.yaml` in the pyspec layouts (§13.4, §13.6) and the function
format (§13.3). Other clients'
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
receives what render returned. A second cross-pass file serves the
client consumer (§13.3): the client harness writes
`<outDir>/client-results.json`, one entry per function-format file it
walked, and the function format's `check` and the report read it.

### 13.3 The function format

Accepts every record with a target: the `function` field names the function
a client exposes, and a record without a target has none to name. Writes
one self-contained file per vector, `<index>` the disjunct index, not
zero padded:

```
<outDir>/formats/function/<fork>/<preset>/<target>/<thm>_<index>[_t|_f].yaml
```

```yaml
theorem: EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff
function: can_builder_cover_bid
fork: gloas
preset: minimal
shape: iffTrue
inputs:
  state: {ssz: '0x…', root: '0x…'}
  builderIndex: 3
  bidAmount: 32000000000
output: true
witnessSearcher: random
```

SSZ values go in as single-quoted hex with their root, scalars as
literals. The YAML writer renders the file in block style (§12.3). Its
`check` answers with the client harness's results (§13.2's
`client-results.json`): an entry the harness ran carries the client's
answer, and `noConsumer` means no client ran the record, either because
the coverage table maps its target to nothing, the client build
table-skipped it, or the harness has not run. The format serves a
client that chooses to expose the function. The theorem name in the
file is the point.

The `function` key keeps its name; it names the function the way the spec
spells it: the record's `pyspecName` (§7.2, §12.2). A record whose target
has no pyspec name falls back to the Lean target name, and a harness
mapping on the field table-skips such a record.

### 13.4 The pyspec format

Upstream defines one case layout per runner (§13.7), and each layout
needs its own `VectorFormat` value with its own `accepts`, `render`, and
`check`. The value this section describes, `Formats.pyspec`, writes one
layout: the `epoch_processing` case, a pre-state and a post-state. The
name "the pyspec format" means this value throughout this document.
Another runner, such as `operations` with its operand part, gets a new
value beside it (§13.7's closing rule).

`Formats.pyspec` accepts a `.runOk` or `.runError` record whose target has
a handler in `binding.handlerOf` and whose only input is the state
(`binding.stateType`). A record with a second input, such as an
operation handler's operand, has no part to go in this layout.

```
<outDir>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<thm>_<case>/
  pre.ssz
  post.ssz          absent for .runError, which marks an invalid case
  meta.yaml         {bls_setting: 2, theorem: <name>}
  manifest.yaml     {preset, fork, runner, handler, suite, case}
```

The layout is the upstream one with raw `.ssz` in place of `.ssz_snappy`. The
Python harness decompresses before it hands paths to the server, so a
one-line switch in `harness.py` accepts either suffix and snappy stays out of
Lean. The YAML writer renders `meta.yaml` as one flow line, the form the
upstream dumper writes for a map of scalars and the one every client's
runner already reads (§12.3). Both pyspec layouts write a `manifest.yaml`
beside `meta.yaml`; §13.7 gives its keys. That section lists every upstream
pyspec format and this repository's coverage of each.

### 13.5 The pyspec check

`check` builds a `CaseRequest` from the rendered files, with `post = none`
for an invalid case, and calls `EthCLLib.PySpecTests.runCase` with the
`ForkInterface` from `binding.interface preset`. A `CaseResult` with
`passed = false` is `CheckResult.failed` with the driver's detail line. A
flagged pass fails the same way: a bug-smell reject never ships green,
whether or not the record's error column holds the same class. This
replays the vector through the same path the upstream vectors take.

### 13.6 The operations format

`Formats.operations` writes the `operations` runner's case layout. The path
layout is the pyspec format's (§13.4). The case parts differ: one operand
part sits between `pre.ssz` and `post.ssz`.

`Formats.operations` accepts a `.runOk` or `.runError` record whose target's
`handlerOf` maps to `("operations", h)` and whose input list is exactly two:
the binding's state type and one operand. The render pass finds the state
input by type, never by position.

```
<outDir>/formats/pyspec/<fork>/<preset>/<runner>/<handler>/pyspec_tests/<thm>_<case>/
  pre.ssz
  <operand>.ssz      the operand part, named by `OpKind.inputName`
  post.ssz           absent for .runError, which marks an invalid case
  meta.yaml          {bls_setting: 2, theorem: <name>}
  manifest.yaml      {preset, fork, runner, handler, suite, case}
```

The operand part's file name comes from the `OpKind.inputName` table, never
from the handler string. Two examples: `block_header` writes `block.ssz`,
and `bls_to_execution_change` writes `address_change.ssz`.

The two formats never accept the same record. A two-input record has no part
in the pyspec layout, and a single-state record has no part here.
`Formats.pyspec` keeps its single-state rule unchanged.

The check rebuilds a `CaseRequest` from the rendered files with the operand
bytes. It replays the request through `runCase` with the fork's
`ForkInterface`, the path the upstream vectors take (§17.4). A result with
`passed = false` is `CheckResult.failed` with the driver's detail. The
flagged-pass rule of §13.5 applies unchanged: a bug-smell reject never ships
green.

The Fulu `consolidation_request` handler is the live consumer today; its 18
rendered cases (15 minimal, 3 mainnet) pass the Python harness and the client
harness.

### 13.7 The upstream pyspec formats

Upstream defines one test format per runner in consensus-specs'
`tests/formats/`. The vocabulary there is: a **runner** owns a format; a
**handler** inside a runner is the sub-format layer, a specialization that
may change a case's parts; cases sit in **suites**; a case is a directory
of **parts** (the files). This document's `VectorFormat` values are per
case shape, not per runner: one value renders one part layout, whatever
runner writes it. The part suffix rule is upstream-wide: `.ssz_snappy`
preferred, a raw `.ssz` beside it accepted, which is what lets this
generator's output ride the readers below. The generator's writers still
emit raw `.ssz` parts. The exe's `prysm-corpus` subcommand writes the
`.ssz_snappy` mirror the Prysm suite's readers consume (§15), with the
all-literals encoder in `Snappy.lean`.

The table names every upstream format and this repository's coverage of
each. "Read" means `PySpecTests/harness.py` parses the format and the
server replays it (§17.4's recipes). "Written" means a `VectorFormat`
value emits it. The corpus column says whether a theorem record can ever
take the shape.

| Format (runner) | Case parts | Read | Written | Corpus |
| --- | --- | --- | --- | --- |
| `bls` | YAML only, no SSZ | no | no | never (the primitives are a dependency's) |
| `epoch_processing` | `pre.ssz`, `post.ssz`, `meta.yaml` | yes | yes — the pyspec format's one shape today | handler-bearing run theorems |
| `fast_confirmation` | the confirmation-rule fork-choice shape, minimal only | no | no | never yet, a named future-work runner |
| `finality` | `pre.ssz`, `blocks_*.ssz`, `post.ssz`, `meta.yaml` | yes | no records today | same case shape as `epoch_processing` |
| `fork_choice` | `anchor_state.ssz`, `anchor_block.ssz`, `steps.yaml`, `meta.yaml` | yes (the steps emitter chain) | no | never (Store inputs, §1.2) |
| `fork` (doc `forks.md`) | `pre.ssz`, `post.ssz`, `meta.yaml` | yes | no records today | upgrade-boundary theorems, none yet |
| `genesis` | in scope per the harness's runner list; the pinned minimal archives carry no genesis runner for these forks | yes | no | none yet |
| `light_client` | SSZ + YAML | no | no | never (out of scope, the comment in `harness.py` names it) |
| `merkle_proof` | SSZ + YAML | no | no | never (out of scope) |
| `networking` | SSZ + YAML | no | no | never (out of scope) |
| `operations` | `pre.ssz`, one operand part (`block.ssz`, `attestation.ssz`, …), `post.ssz`, `meta.yaml` | yes | yes, for handlers with a `handlerOf` row | operation-handler run theorems over the state and one operand; an operand of a §1.2 block type also needs a searcher |
| `random` | `pre.ssz`, `blocks_*.ssz`, `post.ssz`, `meta.yaml` (`{blocks_count, bls_setting}`) | yes | no | never (needs generated blocks) |
| `rewards` | `pre.ssz`, per-delta outputs (`source_deltas.ssz`, `target_deltas.ssz`, `head_deltas.ssz`, `inactivity_penalty_deltas.ssz`), `meta.yaml`, no post | yes | no | none yet |
| `sanity` | handlers: `blocks` (`blocks_*.ssz`, `meta.yaml`), `slots` (`slots.yaml`, a plain integer) | yes | no | never (needs generated blocks) |
| `shuffling` | YAML in, YAML out | no | no | never (out of scope) |
| `ssz_static` | `serialized.ssz`, `roots.yaml` (the expected hash-tree-root) | yes (per-fork containers; the primitive vectors are SizzLean's own runner) | no | never (round-trip properties are not theorem records) |
| `sync` | SSZ + YAML | no | no | never (out of scope) |
| `transition` | `pre.ssz`, `blocks_*.ssz`, `post.ssz`, `meta.yaml` | yes | no records today | upgrade-run theorems, none yet |

Two shared parts sit outside the table. `meta.yaml` is optional per case
and carries `bls_setting` among other keys; the generator writes it in the
one-line flow form (§13.4). `manifest.yaml` is in every upstream case at
the pin, and the generator writes one in every case its two pyspec
layouts render (§13.4, §13.6): a block-style map of six scalar keys in
upstream order, `preset, fork, runner, handler, suite, case`, the values
repeating the case path's segments (§12.3). The function format writes
none, because it is not an upstream case layout. The checks read no
manifest.

A new upstream shape is one new `VectorFormat` value in `Formats.all`
(§13.1), never an edit to the existing three. Each value carries the
writer for its layout: the parts it emits, their file names, and the
replay its `check` runs.

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
theorem_vectors isValidIndexedPayloadAttestation_eq_true_iff_checks
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
theorem_vectors[!] <ident> [presets <presetId>+]
theorem_vectors skip <ident> <string>
```

- `characterized` selects every `@[characterizes]` theorem whose target the
  binding's fork owns (`Capture.specFunctionOwner?`). `tagged` selects every
  `@[theorem_vectors]` theorem under the fork's proof namespace. Each runs
  with the default budget and the clause's preset list, and a theorem with
  a `theorem_vectors_manual` registration (§14.6) runs its registration
  here too.
- `survey` takes every public theorem under the fork's proof namespace that
  no other clause or line selects, runs phase A alone (§3), and writes an
  outcome line with status `unselected`. It never searches a witness and
  never writes a record. It exists so the report shows the whole corpus: a
  reader sees which theorems the lines leave out and what the reader made
  of them. It takes no `presets` clause, because nothing runs per preset. A
  registered theorem never surveys (§14.6).
- `<ident>` resolves to a theorem in the environment, under the fork's proof
  namespace or fully qualified.
- `presets` lists the presets to run. The default is `minimal`.
- `!` turns every skip into an error. A tagged theorem is strict without it.
- `skip` excludes a theorem from discovery and records the reason in the
  outcome file. A `skip` validates against the potential selection, the
  tags of §14.1 and the fork's proof namespace, so a stale exclusion is
  still visible and the line can sit above the clauses it excludes from.

Manual terms are not part of the line grammar. A named line carries the
theorem and its `presets` clause alone; the witness terms live under the
theorem (§14.6), and every run of a registered theorem uses them.

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
an error, and the message says to move the line up. A clause's pass runs
the theorem at the clause's presets and strictness. The named line's
settings would reach the theorem only through a second run, and one
theorem runs once. A skip below it would only replace the
outcome the clause wrote. A line a precedence rule rejects leaves no
state: the elaborator records it only after its pass succeeded, so a
later line meets only the lines above it that passed.

Each per-preset run of phases B1 through B8 (§3) carries its own
heartbeat budget (`theorem_vectors.maxHeartbeats`, §14.4), which the
command sets around it. The run writes records, then one outcome line
(§16). Per record the command logs one info message with the path. Per
skipped preset it logs one warning with the reason, or an error for a
strict theorem.

**What this buys.** A new `@[characterizes]` proof gets a vector attempt on
the next build, and the report lists it with its outcome. An author who wants
a lemma's vectors adds one tag at the proof. The generator file shows every
strict line and every exclusion with a reason; the witness terms sit under
their theorems (§14.6), where an authoring mistake fails the proof file's
own build. Cost stays
bounded, because the discovered set runs with the default budget and a
theorem that needs more gets a named line.

### 14.4 Options

| Option | Default | Meaning |
| --- | --- | --- |
| `theorem_vectors.outDir` | `theorem_vectors` | the output root; the lakefile fixes it |
| `theorem_vectors.maxDisjuncts` | 16 | the DNF cap (§8.2) |
| `theorem_vectors.maxHeartbeats` | 1000000 | the heartbeat budget per run, in the units `set_option maxHeartbeats` takes; the command multiplies by 1000 for the reader field |
| `theorem_vectors.randomDraws` | 64 | redraws for the random searcher |
| `theorem_vectors.randomSize` | 8 | `Gen`'s size parameter |
| `theorem_vectors.shrinkSteps` | 40 | the shrink budget |
| `theorem_vectors.seed` | 0 | the random seed, so a build is reproducible |
| `theorem_vectors.hints` | `use` | `use`, `ignore`, or `require` (§9.8) |
| `theorem_vectors.hintsDir` | `""` | the committed hints root the hint searcher reads; the lakefile fixes it, the same repository-root-relative spelling `theorem_vectors.outDir` takes, and the empty default means the fork commits no hints (§9.8) |
| `theorem_vectors.builtSteps` | 6 at minimal, 3 at mainnet | how far down the builder grid the `built` searcher walks (§9.9) |

### 14.5 Concurrency

Lake elaborates modules in parallel. Each generator file writes under its own
`records/<fork>/`, `outcomes/<fork>/`, `hints/<fork>/`, and `built/<fork>/`
subtrees, so two files never write the same path. Theorems inside one file
run in order.

### 14.6 `theorem_vectors_manual`

The witness terms live under their theorems. `theorem_vectors_manual`
registers them in the theorem's own module, and the generator reads them
from the ledger on every run of the theorem:

```lean
theorem_vectors_manual increaseBalance_run_overflow
  let bs : SSZList Gwei Const.validatorRegistryLimit :=
    ((default : SSZList Gwei Const.validatorRegistryLimit)
      .push 18446744073709551615)
  state    := { (default : BeaconState) with balances := bs }
  preState := default
  i        := 0
  delta    := 1
```

The block above is the shape of the committed Fulu registration
(`Proofs/Fulu/Balances.lean`). That file factors the state term into
`maxBalanceState`, a `private` def beside the theorem, so its clause reads
`state := maxBalanceState`.

Grammar:

```
theorem_vectors_manual <ident>
  let <binder> [: <type>] := <term>
  <input>   [: <type>] := <term>
```

- `<ident>` names the theorem the registration witnesses.
- A `let` clause names a shared value. The clauses below it see it, and it
  never reaches the theorem.
- An assignment clause names one theorem input and its term. Assignments
  never see each other; a term that needs a helper names a `let` above it
  or a definition of the module.
- Indentation carries the block, the way a structure instance's fields do.
  A clause's term ends at the next clause's label, however many lines the
  term spans.

**The rules.** The command validates the registration before it adds any
declaration, so a failing registration leaves the environment untouched.
Every failure is a build error in the proof file's build:

- The target must be a theorem under a registered fork's proof namespace
  (`EthCLSpecs.Proofs.<Fork>`).
- The command must sit in the theorem's own module; a registration in a
  file that imports the theorem errors. The same-file rule re-elaborates
  every registration whenever the theorem's file changes.
- One registration per theorem. The ledger is global across imports, so a
  second registration errors wherever it sits.
- The theorem's instance binders come first in its binder chain. The
  holder quantifies the instance prefix alone, so a binder that breaks
  the prefix errors at the command.
- Each assignment's label must name an input, and one assignment per
  input.
- An input's type may depend on the instance binders alone. A type that
  mentions a type parameter or an earlier input errors, because no holder
  over the instance binders could exist.
- An ill-typed term, a `:` ascription that misses the input's type, or a
  shared `let` whose type holds a metavariable errors at its clause.
- A registration with `let`s and no assignments errors: it would record
  nothing.

**The holders.** The command elaborates each assignment over the theorem's
instance binders alone, then emits one `private` definition per
assignment. Its name joins the theorem's namespace, `TheoremVectorsManual`,
the theorem's name, and the input's name, so the example's `state`
assignment lands at
`EthCLSpecs.Proofs.Fulu.TheoremVectorsManual.increaseBalance_run_overflow.state`.
The holder takes the theorem's instance binders, in the theorem's order,
and the theorem's universe parameters, and nothing else. The definition is
compiled, because the probe serializes manual terms in compiled code
(§11.1). The registration records one `(theorem, input, holder)` name
triple per assignment in a `SimplePersistentEnvExtension`
(`manualTermsExt` in `EthCLLib.Internal.ManualTerms`); only names cross
the `.olean`.

**The generator's side.** The generator applies each holder through the
ledger's names, over the statement's instance binders (§11.2). Every run
of a registered theorem uses its registration: a named line,
`characterized`, and `tagged` alike. A registration is the theorem's only
manual source, and a `with` group after a named line is a parse error
(the grammar of §14.3 has no `with` form).

**Precedence with the generator file.** Two rules protect a registration:

- A `skip` line on a registered theorem errors. The registration belongs
  to the theorem, and the exclusion contradicts it.
- A registered theorem that only the `survey` clause selects errors. The
  survey searches no witness, so the registration would reach no vector;
  the author gives the theorem a named line above the discovery clauses
  (§14.3).

| Mistake | Where it errors |
| --- | --- |
| target is not a theorem, or sits under no fork's proof namespace | the command |
| the command sits in a file that imports the theorem | the command |
| a second registration for the theorem | the command |
| the theorem's instance binders do not come first | the command |
| a label names no input, or names one twice | the clause |
| an input's type mentions a binder outside the instance binders | the clause |
| an ill-typed term, a `:` ascription that misses the input's type, or a shared `let` whose type holds a metavariable | the clause |
| no assignments, only `let`s | the command |
| a `skip` line on a registered theorem | the generator line's pass |
| a registered theorem only `survey` selects | the generator line's pass |

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
theorem_vectors prysm-corpus [--out <dir>]
```

| Subcommand | Does | Exit code |
| --- | --- | --- |
| `render` | phase C1 over the selected records | 0, or 1 when a render throws |
| `check` | phase C2 over the rendered vectors | 0, or 1 when any check fails |
| `report` | phase C3; writes `report.md` | 0 |
| `list` | prints one line per record, for scripts | 0 |
| `prysm-corpus` | writes the snappy mirror of every rendered upstream case layout under `<out>/tests` (the Prysm suite's corpus); `meta.yaml` never copied | 0, or 1 when the manifest is missing or holds no case-layout entries, a case path is malformed, or a mirror write throws |

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
  "disjuncts": 2,
  "runs": [
    { "preset": "minimal", "status": "written", "records": 2,
      "witnessSearcher": "random", "hint": "replayed", "seconds": 4.1 },
    { "preset": "mainnet", "status": "skipped",
      "reason": "notFound after base, bitVec, built, random" } ] }
```

`origin` is one of `named`, `tagged`, `characterized`, `skipped`, `survey`.
`status` is one of `written`, `skipped`, `outOfScope`, `unsat`,
`unsupported`, `unselected`. A `survey` line has one run with status
`unselected`, or `unsupported` with the reader's reason, and no preset
field. `hint` is
one of `replayed`, `stale-replayed`, `failed`, `stale-failed`, `missing`,
`ignored`, one value per run folded from its disjuncts: a failure outranks
a missing entry, and a missing entry outranks a replay. `missing` also
names a run where a disjunct won from a search, so a theorem's first build
reads `missing` until the update recipe runs. `stale-` prefixes the replay
or the failure the fingerprint touched. `ignored` is mode `ignore`'s
answer, and a run with no disjunct carries no field. The file is JSON
(§12.3).

### 16.2 `report.md`

`report` folds the outcome files and the records into one Markdown file with
one table per fork:

| Theorem | Origin | Shape | Preset | Status | Witness searcher | Hint | Records | Formats | Seconds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |

followed by a list of records no format accepted and a list of theorems with
block inputs. The Formats column carries the client harness's answer for the
row's theorem (`prysm passed` / `prysm failed` / `prysm skipped`, the worst
answer across the theorem's records; empty when no client ran it), as of the
last harness run. The summary line above the tables counts the theorems with
outcomes, the box lemmas (§7.3), and the theorems with block inputs, so
the other `.unsupported` rows read as the shape gaps they are. The report
is the review surface: a reader sees which theorems produce vectors, which
do not, and why.

---

## 17. Build integration

### 17.1 Output tree

```
packages/EthCLSpecs/theorem_vectors/        gitignored
  records/<fork>/<preset>/<thm>/<index>/
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
    lake build EthCLLibTheoremVectors EthCLSpecs.Tests.TheoremVectorsPins
    lake build EthCLSpecsTheoremVectors
    lake exe theorem_vectors render
    lake exe theorem_vectors check
    lake exe theorem_vectors report

# Remove the output tree and the generator modules' build outputs, so the
# next build regenerates. Lake tracks the modules, not the files they write.
theorem-vectors-clean:
    rm -rf packages/EthCLSpecs/theorem_vectors
    rm -rf packages/EthCLSpecs/.lake/build/lib/lean/EthCLSpecs/TheoremVectors/Generators

# Copy the hints the last build wrote over the committed ones. Commit the
# diff. A build where nothing won writes no hints directory; the copy skips.
theorem-vectors-hints-update:
    mkdir -p packages/EthCLSpecs/EthCLSpecs/TheoremVectors/Hints
    if [ -d packages/EthCLSpecs/theorem_vectors/hints ]; then cp -r packages/EthCLSpecs/theorem_vectors/hints/. packages/EthCLSpecs/EthCLSpecs/TheoremVectors/Hints/; fi

# Search everything again, with the committed hints ignored, then update them.
theorem-vectors-hints-rebuild:
    just theorem-vectors-clean
    THEOREM_VECTORS_HINTS=ignore lake build EthCLSpecsTheoremVectors
    just theorem-vectors-hints-update
```

The `theorem-vectors` recipe builds the framework-half library and the
spec-half pins before the generator, so the toy tests and the pins run
with every vector build. The clean recipe exists because a deleted output
directory stays empty until the generator modules rebuild. Removing their
build outputs forces that. The rebuild recipe sets the hint mode through
the environment variable `THEOREM_VECTORS_HINTS`, which the command reads
ahead of the `theorem_vectors.hints` option; a set variable that names no
mode is a build error, so a typo never runs the build in `use` mode. A
declarative `lakefile.toml` cannot pass a command-line key to an option,
and the variable keeps the lakefile declarative. The variable is not part of Lake's traces, so a run in
`ignore` or `require` mode after a plain build sees the generator modules
up to date and leaves the last build's outcomes; a run in a mode other
than `use` starts from a clean generator build. The committed hint files
are outside Lake's traces too, so the build that follows an
`theorem-vectors-hints-update` run or a hand edit starts from the clean
recipe as well.

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
| a registration clause fails a §14.6 check | A0 | error in the proof file's build (§14.6) |
| `skip` line on a theorem with a `theorem_vectors_manual` registration | A0 | error (§14.6) |
| a registered theorem only `survey` selects | A0 | error (§14.6) |
| `.unsupported` shape | A1 | skip (error under `!` or `@[theorem_vectors]`) |
| block input, base searcher fails | B3 | `outOfScope` skip (error under `!` or the tag) |
| solver proves `¬P` | B3 | `unsat` skip, always reported |
| searchers exhausted | B3 | `notFound` skip (error under `!` or the tag) |
| fully covering manual terms win no disjunct | B3 | error: "fix the manual term in `theorem_vectors_manual`" |
| partial manual terms, no searcher finds a witness | B3 | `notFound` skip |
| hint fails the check, mode `use` | B3 | full search, `hint: failed` in the outcome |
| hint fails the check, or a disjunct wins from a search, mode `require` | B3 | error |
| `THEOREM_VECTORS_HINTS` set to a value that names no mode | A0 | error |
| `agree = false` | B5 | error, both values printed |
| read-back mismatch | B7 | error |
| no format accepts a record | C1 | listed in the report |
| pyspec check fails | C2 | `check` exits 1 |
| DNF cap hit | A3 | warning, unsplit fallback |

The rule behind the table: a claim the author made (`!`, the tag, a manual
term) fails hard.
A fact about the theorem (`unsat`, `notFound`, `unsupported`) is reported. A
disagreement between the kernel and the compiled code always fails hard.

---

## 19. Extension points

Each row adds code and edits none of the existing pipeline.

| To add | Write | Touch |
| --- | --- | --- |
| a fork | `Bindings/<Fork>.lean`, `Generators/<Fork>.lean` | the bindings table |
| a preset | one `PresetId` constructor, one entry per binding | `Types.lean`, the bindings |
| a witness searcher | one `WitnessSearcher` value | the searcher list |
| a format | one `VectorFormat` value | `Formats.all` |
| an operation handler | one `handlerOf` row on the fork binding naming `("operations", h)`; a handler with a new operand kind adds one `OpKind` arm and its `inputName` (§13.6) | nothing else |
| a shape | one `Shape` constructor, one reader arm, one executor row | `Statement`, `Execute` |
| a manual term | one clause in the theorem's `theorem_vectors_manual` registration (§14.6) | nothing else |
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
- **Disjunct.** One conjunction of hypotheses the search solves, from the
  DNF split, with a side for `iffTrue`. Renamed from case (owner decision
  of 2026-10-16).
- **Witness.** An assignment of SSZ bytes to every input that passes the
  check.
- **Witness searcher.** One strategy that proposes witnesses. The searchers
  run in a fixed order, cheapest first. Renamed from witness source
  (owner decision of 2026-10-16).
- **Manual term.** The author's hand-supplied input term for one theorem
  input, registered under the theorem with `theorem_vectors_manual`
  (§14.6). Renamed from seed (owner decision of 2026-10-16).
- **Check.** Compiled `decide P` on a candidate. The single arbiter.
- **Hint.** A committed note of how a witness was found, enough to rebuild
  the candidate without a search. The check still decides.
- **State builder.** A fork function that runs the spec to produce a
  reachable state from a few knobs. The `built` searcher walks a catalog of
  them, and the output tree caches their bytes.
- **Probe.** The compiled face of one statement at one preset: check,
  sample, shrink, reads, manuals, defaults, build, run.
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
