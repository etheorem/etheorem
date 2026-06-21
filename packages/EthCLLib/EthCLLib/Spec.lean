import EthCLLib.Spec.Errors
import EthCLLib.Spec.Hasher
import EthCLLib.Spec.State
import EthCLLib.Spec.Arith
import EthCLLib.Spec.SigningRoot
import EthCLLib.Spec.Loop
import EthCLLib.Spec.FiniteMap
import EthCLLib.Spec.Assert
import EthCLLib.Spec.Header
import EthCLLib.Spec.Forms
import EthCLLib.Spec.Crypto

/-!
# `EthCLLib.Spec`: the author-facing surface

`open EthCLLib.Spec` brings in everything a spec file writes against, in one
namespace (`SPEC_AUTHORING_MODEL.md` §3.2): the `fork*` forms and `inherit`
(scoped syntax), the header macros `state_preamble` / `state_section` /
`fork_choice_section`, `assert` and the step
primitives (`modifyState`, `todo`), the `HasherTag` selector, the `CryptoBackend`
seam, and the state helpers (`getStateRoot` / `stateRoot!`). SizzLean's `sszGet` / `sszUpdate` are
global syntax brought in by `import SizzLean`, so they need no re-export.

The per-fork `Preset` / `Config` classes and the `Const` tier abbrevs are not
here: the tier system is per fork (`SPECS_ARCHITECTURE.md` §9.1), declared in the
fork's own `Constants` module. The header macros reference the fork's `Preset` and
`State` by use-site identifiers, so they resolve there.
-/
