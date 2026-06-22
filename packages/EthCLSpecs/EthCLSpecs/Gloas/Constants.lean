import EthCLSpecs.Fulu

/-!
# `EthCLSpecs.Gloas.Constants`: the Gloas fork declaration + version values

Gloas is a diff over Fulu (`SPECS_ARCHITECTURE.md` §2, §4.1). `fork Gloas from Fulu`
records the lineage so `inherit` can replay Fulu declarations in the Gloas
namespace, where their unqualified sibling references late-bind to Gloas's
overrides. The two `GLOAS_FORK_VERSION` values are the only Gloas-specific
constants; the numeric Gloas constants (`builderRegistryLimit`, `ptcSize`, the
churn quotients, …) live in the shared `Fulu.Constants` tier, reached through
`Const.*` / `open EthCLSpecs.Fulu`.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Gloas

fork Gloas from Fulu

/-- `GLOAS_FORK_VERSION` at the `minimal` config (`0x07000001`). -/
def gloasForkVersionMinimal : Version := ⟨#[0x07, 0x00, 0x00, 0x01], by decide⟩
/-- `GLOAS_FORK_VERSION` at the `mainnet` config (`0x07000000`). -/
def gloasForkVersionMainnet : Version := ⟨#[0x07, 0x00, 0x00, 0x00], by decide⟩

end EthCLSpecs.Gloas
