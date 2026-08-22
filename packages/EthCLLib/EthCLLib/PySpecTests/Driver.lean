import EthCLLib.PySpecTests.Interface

/-!
# `EthCLLib.PySpecTests.Driver`: the generic, fork-agnostic driver

The single-step / fold-compare-root half of `PySpecTests`
(`FRAMEWORK_ARCHITECTURE.md` §13.2). Written against `ForkInterface`, so it names
no concrete fork and lives in `EthCLLib`. A `CaseRequest` (decoded from the wire
by the runner) is dispatched by `(runner, handler)` to the right interface
method; the resulting post root is compared against the vector's expected root,
and the outcome is classified into one of the error model's buckets.

The reject-faithfulness audit (`SPECS_ARCHITECTURE.md` §10.2) is encoded in
`classify` and in the case's own `RunnerCaughtSet`, which names the reference
wrapper that scores it:

| Vector | Outcome | Result |
|---|---|---|
| valid (`post` present) | root matches | pass |
| valid | any error, or wrong root | fail |
| invalid (`post` absent) | `assert` reject, `expect_assertion_error` case | pass |
| invalid | `assert` reject, `except ValueError` case | fail, **flagged** (the reference re-raises "expected ValueError") |
| invalid | `outOfBounds` reject (caught `IndexError`), `expect_assertion_error` case | pass, **flagged** (bug-smell) |
| invalid | `outOfBounds` reject, `except ValueError` case | fail, **flagged** (bug-smell) |
| invalid | `decode` failure (our decoder, not a raise) | fail, **flagged** (bug-smell) |
| invalid | `arithmetic` reject, `expect_assertion_error` case | fail (the reference does not catch it) |
| invalid | `arithmetic` reject, `except ValueError` case | pass (that wrapper catches it) |
| invalid | `todo` reject | fail (an unimplemented path is not a validation) |
| invalid | ran clean | fail (should have rejected) |

The step/check interpreter (`fork_choice`) and the delta-comparison (`rewards`)
have different shapes and join in Phase 2.3 / 2.5; this driver reports them as
out-of-scope `todo` until then.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLLib.PySpecTests

/-- One pyspec case, decoded from the wire by the runner. `post = none`
marks an invalid vector (a reject is expected). `inputs` carries the
format-specific SSZ buffers (the `blocks_N`, the single operation, the genesis
eth1 inputs). -/
structure CaseRequest where
  /-- The case-path runner segment: `sanity`, `operations`, `epoch_processing`, … -/
  runner : String
  /-- The case-path handler segment: `blocks`, `proposer_slashing`, … -/
  handler : String
  /-- The decoded pre-state SSZ bytes. -/
  pre : ByteArray
  /-- The expected post-state SSZ bytes; `none` ⇒ invalid vector. -/
  post : Option ByteArray
  /-- Format-specific SSZ inputs (blocks, the operation, genesis eth1 data). -/
  inputs : Array ByteArray
  /-- The parsed `meta.yaml`. -/
  caseMeta : CaseMeta
  deriving Inhabited

/-- The driver's result for one case. `passed` is whether the outcome matched
the vector's valid/invalid marking; `bucket` is the reporting bucket (a passing
case is `passing` or `expectedRejection`; a failure carries its smell); `flagged`
marks an invalid vector rejected by a bug-smell rather than a clean `assert`. -/
structure CaseResult where
  /-- Did the outcome match the vector's marking? -/
  passed : Bool
  /-- The classify bucket for reporting. -/
  bucket : ClassifyBucket
  /-- A diagnostic line (root mismatch, reject descriptor, …). -/
  detail : String
  /-- A bug-smell worth surfacing on the wire: an invalid vector rejected by
  `outOfBounds`, or any case whose container failed to decode (`RunError.decode`). -/
  flagged : Bool := false
  deriving Inhabited, Repr

namespace CaseResult

/-- Collapse a detail string to one tab-free line. The detail is diagnostic only
(`reprStr` of a reject can wrap a long descriptor across lines), so newlines and
tabs are flattened to spaces; a multi-line detail would otherwise inject extra
lines into the one-line-per-case `PySpecTests` wire protocol and desync the
worker. -/
def flattenDetail (s : String) : String :=
  String.ofList (s.toList.map (fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c))

/-- A wire-friendly one-line rendering: `<pass|fail>\t<bucket>\t<detail>`. -/
def render (r : CaseResult) : String :=
  s!"{if r.passed then "pass" else "fail"}\t{r.bucket.tag}{if r.flagged then "!" else ""}\t{flattenDetail r.detail}"

end CaseResult

/-- Dispatch a request to the right `ForkInterface` entry point, returning the
post-state root or a typed reject. Unwired formats reject with `todo` so a vector
that reaches one fails loudly rather than passing silently. -/
def dispatch [ForkInterface] (req : CaseRequest) :
    Except (RunError StateTransitionError) ByteArray :=
  match req.runner, req.handler with
  | "sanity", "blocks"  => ForkInterface.runBlocks req.pre req.inputs req.caseMeta
  | "finality", _       => ForkInterface.runBlocks req.pre req.inputs req.caseMeta
  | "random", _         => ForkInterface.runBlocks req.pre req.inputs req.caseMeta
  | "sanity", "slots"   =>
    match req.inputs[0]? with
    | some b => ForkInterface.runSlots req.pre (b.toList.foldl (fun acc x => acc * 256 + x.toNat) 0)
    | none   => .error (.spec (.todo "sanity/slots: missing slot-count input"))
  | "epoch_processing", h =>
    -- Parse the wire handler name to its typed `EpochStep` here, the one boundary where
    -- the string is interpreted; an unrecognized name is out of scope.
    match EpochStep.ofString? h with
    | some step => ForkInterface.runEpochSubstep step req.pre
    | none      => .error (.spec (.todo s!"epoch_processing/{h}: no fork drives this substep"))
  | "operations", h     =>
    -- Parse the wire handler name to its typed `OpKind` here. Most operations carry one
    -- operand file; a few (e.g. Gloas `process_withdrawals`, which takes no payload) are
    -- operand-free, so a missing operand passes empty bytes and the handler ignores them.
    match OpKind.ofString? h with
    | some kind => ForkInterface.runOperation kind req.pre (req.inputs[0]?.getD ByteArray.empty) req.caseMeta
    | none      => .error (.spec (.todo s!"operations/{h}: no fork drives this handler"))
  | "genesis", _        => ForkInterface.runGenesis req.inputs req.caseMeta
  | "fork", _           => ForkInterface.runUpgrade req.pre
  | "transition", _     => ForkInterface.runTransition req.pre req.inputs req.caseMeta
  | r, h                => .error (.spec (.todo s!"format '{r}/{h}' not wired in the driver"))

/-- The caught set for a case-path `(runner, handler)` pair.

The reference writes each wrapper inside one test function. Almost every test uses
`expect_assertion_error`. One test writes its own `except ValueError`:
`test_invalid_large_withdrawable_epoch`, under `epoch_processing` / `registry_updates`. The match
below names both case-path segments for that reason. A key on the runner segment alone would put
every other `epoch_processing` handler in the same set.

This pair holds one post-less case in the pinned corpus. `test_pyspec.py` asserts that, and the
assertion is what catches a second post-less vector under the same pair.

The two strings are wire data, and `Spec/Errors.lean` carries no wire vocabulary, so they are
read here. `dispatch` reads the handler names at the same boundary. -/
def RunnerCaughtSet.ofCase : String → String → RunnerCaughtSet
  | "epoch_processing", "registry_updates" => .valueError
  | _,                  _                  => .assertionAndIndex

/-- The pass/fail answer for an invalid vector that rejected. `caught` names the reference
wrapper that scores the case.

The reject is faithful when the wrapper catches it. `admits` decides that. An unadmitted
reject must report a bucket that reads as a failure. `.assert` classifies as
`.expectedRejection`, and `ClassifyBucket.tag` maps that to `"reject"`, so `render` would
print a `fail` row under the pass tag. An `.outOfBounds` keeps the bug-smell marker in both
branches. `admits` is false for `.todo` and `.outOfScope` under either set, so those two rows
ignore it.

`classify` never answers `.passing`. The last row says so, rather than let a wildcard pass an
invalid vector. Split out of `runCase` so `#guard` can pin the table without a `ForkInterface`
or a decoded state. -/
def classifyReject (caught : RunnerCaughtSet) (e : StateTransitionError) : CaseResult :=
  match e.classify, caught.admits e with
  | .todo,              _     => { passed := false, bucket := .todo,              detail := reprStr e }
  | .outOfScope,        _     => { passed := false, bucket := .outOfScope,        detail := reprStr e }
  | .expectedRejection, true  => { passed := true,  bucket := .expectedRejection, detail := reprStr e }
  | .expectedRejection, false => { passed := false, bucket := .likelyBug,         detail := reprStr e, flagged := true }
  | .likelyBug,         true  => { passed := true,  bucket := .likelyBug,         detail := reprStr e, flagged := true }
  | .likelyBug,         false => { passed := false, bucket := .likelyBug,         detail := reprStr e, flagged := true }
  | .uncaughtFault,     true  => { passed := true,  bucket := .expectedRejection, detail := reprStr e }
  | .uncaughtFault,     false => { passed := false, bucket := .uncaughtFault,     detail := reprStr e }
  | .passing,           _     => { passed := false, bucket := .likelyBug,         detail := "unreachable classify" }

/-- Run one case and classify it. The fork-agnostic core of `PySpecTests`.

`rewards` has its own shape (compare several `Deltas` blobs, not a post root): the
expected delta files arrive as `req.inputs`, in the `[source, target, head,
inactivity]` order the runner returns, and each must match byte-for-byte. -/
def runCase [ForkInterface] (req : CaseRequest) : CaseResult :=
  if req.runner == "rewards" then
    match ForkInterface.runRewards req.pre with
    | .ok deltas =>
      if deltas == req.inputs then { passed := true, bucket := .passing, detail := "" }
      else { passed := false, bucket := .likelyBug, detail := "rewards deltas mismatch" }
    | .error e =>
      match e.classify with
      | .todo       => { passed := false, bucket := .todo, detail := reprStr e }
      | .outOfScope => { passed := false, bucket := .outOfScope, detail := reprStr e }
      | _           => { passed := false, bucket := .likelyBug, detail := reprStr e }
  else
  match dispatch req, req.post with
  | .ok actual, some postBytes =>
    -- Valid vector: the post root must match.
    match ForkInterface.stateRoot postBytes with
    | .ok expected =>
      if actual == expected then
        { passed := true, bucket := .passing, detail := "" }
      else
        { passed := false, bucket := .likelyBug, detail := "post-state root mismatch" }
    | .error e =>
      { passed := false, bucket := .likelyBug,
        detail := s!"could not root expected post-state: {reprStr e}" }
  | .ok _, none =>
    -- Invalid vector that ran clean: should have rejected.
    { passed := false, bucket := .likelyBug, detail := "expected a rejection but ran clean" }
  | .error e, some _ =>
    -- Valid vector that rejected: a failure, classified by the reject.
    { passed := false, bucket := e.classify, detail := reprStr e }
  | .error (.decode what), none =>
    -- A decode failure is our decoder's bug, never the invalid vector's expected raise.
    -- Every post-less case decodes before any spec code runs (`decodeState`, `decodeOp`,
    -- `runBlocksImpl`), so scoring this as a rejection would report a handler's whole
    -- `invalid_*` half as passing on one broken container layout. The store machine
    -- decided the same question the same way at `298bf02`
    -- (`StoreTransitionError.decodeFailure` is excluded from `isExpectedRejection`).
    -- Still flagged, so the wire keeps the smell marker.
    { passed := false, bucket := .likelyBug, detail := s!"decode failed: {what}",
      flagged := true }
  | .error (.spec e), none => classifyReject (RunnerCaughtSet.ofCase req.runner req.handler) e

end EthCLLib.PySpecTests
