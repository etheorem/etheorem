import EthCLSpecs.Heze.Committees

/-!
# `EthCLSpecs.Tests.HezeCommitteesPins`: the FOCIL cyclic-resampling pins

The `#guard`s for `EthCLSpecs.Heze.cyclicSample`, the wrap-around index fill behind
`get_inclusion_list_committee`. Kernel-decidable (no hashing), so they cost no compiler
axiom.

They sit in `EthCLSpecsTests` for the reason the fork-choice pin modules do: the lakefile
declares that library for build gates, and a gate compiled into `EthCLSpecs` is weight
every consumer of the fork body carries.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false


namespace EthCLSpecs.Tests.HezeCommitteesPins

open EthCLSpecs.Heze

-- Pins for the cyclic resampling, expected values computed by hand from the Python
-- comprehension `[indices[i % len(indices)] for i in range(n)]`. First: a size-3 source over
-- n = 8 wraps as i % 3 = 0,1,2,0,1,2,0,1. Second: a size-2 source over the real
-- `INCLUSION_LIST_COMMITTEE_SIZE` (= 16) alternates 0,1,…; the 16-element result also pins
-- the constant, since a different size would change the list length and fail the `=`.
#guard (cyclicSample (#[10, 20, 30] : Array UInt64) 8).toList
  = [10, 20, 30, 10, 20, 30, 10, 20]
#guard (cyclicSample (#[7, 8] : Array UInt64) (@Const.inclusionListCommitteeSize minimal)).toList
  = [7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8]

end EthCLSpecs.Tests.HezeCommitteesPins
