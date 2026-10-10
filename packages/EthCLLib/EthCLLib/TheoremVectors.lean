import EthCLLib.TheoremVectors.Types
import EthCLLib.TheoremVectors.Yaml
import EthCLLib.TheoremVectors.ForkBinding

/-!
# `EthCLLib.TheoremVectors`: the theorem-vector generator's framework half

Library root and public surface (`ARCHITECTURE.md` §2.1, §4.1). This half
works on `Expr`, `Name`, and `ByteArray` alone, and the fork facts arrive
as one `ForkBinding` value per fork (§6). The spec half
(`EthCLSpecs.TheoremVectors`) supplies the bindings and the generator
files.

These modules hold the core types (§5), the client-facing YAML writer
(§12.3), and the fork binding seam (§6). The module map (§4.1) places the
statement reader, the prepare pass, the witness sources, the probe, the
executor, the records, the formats, and the generator commands beside
them as the library grows.

No shipped module imports anything under `EthCLLib.TheoremVectors`, so the
`Plausible` dependency and the generator stay off the `EthCLLib` link line
(§2.2).
-/

set_option autoImplicit false
