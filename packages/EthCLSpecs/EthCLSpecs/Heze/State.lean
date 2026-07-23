import EthCLSpecs.Heze.Containers.InclusionList

/-!
# `EthCLSpecs.Heze.State`: the Heze `BeaconState` (inherited from Gloas)

At alpha.11 Heze does not change `BeaconState`, so `inherit BeaconState` replays Gloas's
field block here unchanged. `state_preamble` declares the boxed `State` and `modifyState`.
The `Containers.InclusionList` import is the load-order entry: it transitively pulls
`Heze.Inherited` (the inherited containers) and the `fork Heze from Gloas` lineage that
`inherit` resolves against. It is load-bearing; do not drop it.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

inherit BeaconState

-- The once-per-fork preamble: declares `State` (the boxed `BeaconState`) and `modifyState`.
state_preamble BeaconState

end EthCLSpecs.Heze
