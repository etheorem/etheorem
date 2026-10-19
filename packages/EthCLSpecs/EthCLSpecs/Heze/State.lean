import EthCLSpecs.Heze.Containers.InclusionList

/-!
# `EthCLSpecs.Heze.State`: the Heze `BeaconState` (inherited from Gloas)

Heze's `BeaconState` keeps Gloas's 46 fields. `inherit BeaconState` replays that block,
including the progressive-container attribute, and `latestExecutionPayloadBid` late-binds
to Heze's bid (the extra `inclusionListBits` field). `state_preamble` declares the boxed
`State` and `modifyState`.
The `Containers.InclusionList` import is the load-order entry: it transitively pulls
`Heze.Inherited` (the inherited containers) and the `fork Heze from Gloas` lineage that
`inherit` resolves against. It is required; do not drop it.
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Heze

inherit BeaconState

-- The once-per-fork preamble: declares `State` (the boxed `BeaconState`) and `modifyState`.
state_preamble BeaconState

end EthCLSpecs.Heze
