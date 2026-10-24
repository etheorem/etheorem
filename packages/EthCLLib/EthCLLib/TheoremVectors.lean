import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Scalar
import EthCLLib.TheoremVectors.Sampleable
import EthCLLib.TheoremVectors.Yaml
import EthCLLib.TheoremVectors.Snappy
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
import EthCLLib.TheoremVectors.Prepare
import EthCLLib.TheoremVectors.Preset
import EthCLLib.TheoremVectors.Probe
import EthCLLib.TheoremVectors.Execute
import EthCLLib.TheoremVectors.Witness.Searcher
import EthCLLib.TheoremVectors.Witness.Layers
import EthCLLib.TheoremVectors.Witness.Reuse
import EthCLLib.TheoremVectors.Witness.Base
import EthCLLib.TheoremVectors.Witness.Manual
import EthCLLib.TheoremVectors.Witness.BitVec
import EthCLLib.TheoremVectors.Witness.Built
import EthCLLib.TheoremVectors.Witness.Random
import EthCLLib.TheoremVectors.Witness.Hint
import EthCLLib.TheoremVectors.Witness.Shrink
import EthCLLib.TheoremVectors.Record
import EthCLLib.TheoremVectors.ClientResults
import EthCLLib.TheoremVectors.Format
import EthCLLib.TheoremVectors.Formats.Function
import EthCLLib.TheoremVectors.Formats.Pyspec
import EthCLLib.TheoremVectors.Formats.Operations
import EthCLLib.TheoremVectors.Outcome
import EthCLLib.TheoremVectors.Report
import EthCLLib.TheoremVectors.Command

/-!
# `EthCLLib.TheoremVectors`: the theorem-vector generator's framework half

Library root and public surface (`THEOREM_VECTORS_ARCHITECTURE.md` §2.1, §4.1). This half
works on `Expr`, `Name`, and `ByteArray` alone, and the fork facts arrive
as one `ForkBinding` value per fork (§6). The spec half
(`EthCLSpecs.TheoremVectors`) supplies the bindings and the generator
files.

These modules hold the core types (§5), the client-facing YAML writer
(§12.3), the fork binding seam (§6), the statement reader (§7), the scope
walk (§7.4), the prepare pass (§8), the preset binding (§10), the probe
and the executor (§11), the witness search's searchers (manual, base,
bit-vector, built, random, reuse, and hint) and the shrink (§9.2, §9.4,
§9.6, §9.8, §9.9, §10), the records
(§12), the client harness's results file (§13.3), the function format
(§13.3), the epoch_processing format (§13.4, §13.5), the operations format
(§13.6), the outcome lines (§16.1), the report (§16.2), and the
generator commands (§14).

No shipped module imports anything under `EthCLLib.TheoremVectors`, so the
`Plausible` dependency and the generator stay off the `EthCLLib` link line
(§2.2).
-/

set_option autoImplicit false
