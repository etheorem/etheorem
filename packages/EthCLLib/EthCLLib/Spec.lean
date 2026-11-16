import EthCLLib.Spec.Errors
import EthCLLib.Spec.Checked
import EthCLLib.Spec.CLUint
import EthCLLib.Spec.CLInt
import EthCLLib.Spec.CLTotal
import EthCLLib.Spec.Elab
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.State
import EthCLLib.Spec.Arith
import EthCLLib.Spec.MerklePath
import EthCLLib.Spec.SigningRoot
import EthCLLib.Spec.Loop
import EthCLLib.Spec.FiniteMap
import EthCLLib.Spec.RunState
import EthCLLib.Spec.Assert
import EthCLLib.Spec.NestedMachine
import EthCLLib.Spec.Header
import EthCLLib.Spec.Forms
import EthCLLib.Spec.Tiers
import EthCLLib.Spec.Crypto
import EthCLLib.Spec.Engine

/-!
# `EthCLLib.Spec`: the author-facing surface

`open EthCLLib.Spec` brings in everything a spec file writes against, in one
namespace (`SPEC_AUTHORING_MODEL.md` §3.2): the `fork*` forms and `inherit`
(scoped syntax, including the `forkpreset` / `forkconfig` tier forms and their
value sets), the header macros `state_preamble` / `state_section` /
`fork_choice_section`, `assert` and the step
primitives (`modifyState`, `todo`), the `HasherTag` selector, the `CryptoBackend`
seam, the state helpers (`getStateRoot` / `stateRoot!`), the checked operator
surface (the operand-matrix instances plus the scoped elaborator in
`Spec/Elab.lean` and the §4.4 lift in `Spec/Checked.lean`), and the size-aware
indexing layer (`ToIndex` / `getAt` / `setAt` in `Spec/State.lean`).
SizzLean's `sszGet` / `sszUpdate` are
global syntax brought in by `import SizzLean`, so they need no re-export.

What lives here is the *forms*, never a `Preset` / `Config` class or a `Const`
entry: the tier system is per fork (`SPECS_ARCHITECTURE.md` §9.1), and each fork
declares its own classes and constants in its own `Constants` module. The header
macros reference the fork's `Preset` and `State` by use-site identifiers, so they
resolve there.
-/
