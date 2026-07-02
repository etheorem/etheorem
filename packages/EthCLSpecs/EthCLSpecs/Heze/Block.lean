import EthCLSpecs.Heze.Containers.InclusionList

/-!
# `EthCLSpecs.Heze.Block`: the Heze block containers (inherited from Gloas)

`BeaconBlockBody` / `BeaconBlock` / `SignedBeaconBlock` are Gloas's, unchanged (EIP-7805
touches none of them), so all three are `inherit`ed verbatim, including the signed wrapper.
The `Containers.InclusionList` import is the load-order entry (it pulls `Heze.Inherited` +
the `fork Heze from Gloas` lineage that `inherit` resolves against); it is load-bearing,
do not drop it.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

inherit BeaconBlockBody
inherit BeaconBlock
inherit SignedBeaconBlock

end EthCLSpecs.Heze
