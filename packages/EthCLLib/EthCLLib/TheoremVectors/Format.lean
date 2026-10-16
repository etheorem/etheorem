import Lean
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.ForkBinding

/-!
# `EthCLLib.TheoremVectors.Format`: the format seam

One consumer layout as a first-class value (`THEOREM_VECTORS_ARCHITECTURE.md` §13.1). The
registry is a list of values, because the exe iterates it, and a list of
values iterates where a set of instances does not. A new format appends one
value; `Formats.all` collects them.

## Lean idioms annotated

- `VectorFormat` is a structure, not a typeclass, for exactly the reason
  §13.1 gives: `Formats.all` is data the `render` and `check` subcommands
  fold over.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.TheoremVectors

/-- What a format's consumer check answered (`THEOREM_VECTORS_ARCHITECTURE.md` §13.1). -/
inductive CheckResult where
  /-- The consumer replayed the vector and it passed. -/
  | passed
  /-- The consumer replayed the vector and it failed, with the detail. -/
  | failed (detail : String)
  /-- No consumer answered: the format has no Lean-side consumer, or no
  client ran the record. -/
  | noConsumer

/-- The environment a render pass runs in (§13.1). -/
structure RenderEnv where
  /-- The output root. -/
  outDir   : System.FilePath
  /-- The fork binding by tag. -/
  bindings : String → Option ForkBinding

/-- One consumer layout (`THEOREM_VECTORS_ARCHITECTURE.md` §13.1). -/
structure VectorFormat where
  /-- The registry name, and the `--format` flag's value. -/
  name    : String
  /-- Does this format accept the record? The record names its fork by
  tag, and only the render environment resolves the tag to a binding, so
  the field takes the `RenderEnv` (the notes record the deviation from
  §13.1's one-argument sketch). -/
  accepts : RenderEnv → VectorRecord → Bool
  /-- Render one record into the consumer's layout: the input bytes in
  binder order, then the output's bytes when the record carries an output
  (the `ReadBack` bytes, so a container output renders its own hex and
  not an empty string; §13.1's sketch passes the input bytes alone). -/
  render  : RenderEnv → VectorRecord → Array ByteArray →
    Option ByteArray → IO (Array System.FilePath)
  /-- Replay the rendered vector through the format's consumer. -/
  check   : RenderEnv → VectorRecord → Array System.FilePath → IO CheckResult

end EthCLLib.TheoremVectors
