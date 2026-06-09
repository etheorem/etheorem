import LeanEthCS.Forks.Electra.LightClient
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Fulu.LightClient`: Fulu light-client objects

At v1.5.0, Fulu's light-client containers match Electra's verbatim.
Re-export.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Fulu

open SizzLean

abbrev LightClientHeader := LeanEthCS.Forks.Electra.LightClientHeader

abbrev LightClientBootstrap.Minimal := LeanEthCS.Forks.Electra.LightClientBootstrap.Minimal
abbrev LightClientBootstrap.Mainnet := LeanEthCS.Forks.Electra.LightClientBootstrap.Mainnet

abbrev LightClientUpdate.Minimal := LeanEthCS.Forks.Electra.LightClientUpdate.Minimal
abbrev LightClientUpdate.Mainnet := LeanEthCS.Forks.Electra.LightClientUpdate.Mainnet

abbrev LightClientFinalityUpdate.Minimal := LeanEthCS.Forks.Electra.LightClientFinalityUpdate.Minimal
abbrev LightClientFinalityUpdate.Mainnet := LeanEthCS.Forks.Electra.LightClientFinalityUpdate.Mainnet

abbrev LightClientOptimisticUpdate.Minimal := LeanEthCS.Forks.Electra.LightClientOptimisticUpdate.Minimal
abbrev LightClientOptimisticUpdate.Mainnet := LeanEthCS.Forks.Electra.LightClientOptimisticUpdate.Mainnet

end LeanEthCS.Forks.Fulu
