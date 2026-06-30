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
`classify`:

| Vector | Result | Verdict |
|---|---|---|
| valid (`post` present) | root matches | pass |
| valid | any error, or wrong root | fail |
| invalid (`post` absent) | `assert` reject | pass |
| invalid | `outOfBounds` / `missingKey` reject | pass, **flagged** (bug-smell) |
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

/-- The driver's verdict for one case. `passed` is whether the outcome matched
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
  /-- An invalid vector rejected by `outOfBounds` / `missingKey` (rejected, but a
  smell worth surfacing). -/
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
  | .error e, none =>
    -- Invalid vector that rejected: faithful iff it was an `assert`. A bug-smell
    -- reject still counts as rejected but is flagged; a `todo` / `outOfScope` fails
    -- (not a validation) and reports as its own bucket (xfail / skip respectively).
    match e.classify with
    | .expectedRejection => { passed := true,  bucket := .expectedRejection, detail := reprStr e }
    | .likelyBug         => { passed := true,  bucket := .likelyBug, detail := reprStr e, flagged := true }
    | .todo              => { passed := false, bucket := .todo, detail := reprStr e }
    | .outOfScope        => { passed := false, bucket := .outOfScope, detail := reprStr e }
    | .passing           => { passed := false, bucket := .likelyBug, detail := "unreachable classify" }

end EthCLLib.PySpecTests
