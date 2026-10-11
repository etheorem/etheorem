import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Yaml
import EthCLLib.TheoremVectors.ForkBinding
import EthCLLib.TheoremVectors.Statement
import EthCLLib.TheoremVectors.Scope
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
walk (§7.4), the outcome lines (§16.1), the report (§16.2), and the
generator commands (§14). The module map (§4.1) places the prepare pass,
the witness sources, the probe, the executor, the records, and the formats
beside them as the library grows.

No shipped module imports anything under `EthCLLib.TheoremVectors`, so the
`Plausible` dependency and the generator stay off the `EthCLLib` link line
(§2.2).
-/

set_option autoImplicit false
