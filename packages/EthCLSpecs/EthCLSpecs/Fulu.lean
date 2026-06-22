import EthCLSpecs.Fulu.Types
import EthCLSpecs.Fulu.Constants
import EthCLSpecs.Fulu.Containers
import EthCLSpecs.Fulu.State
import EthCLSpecs.Fulu.Time
import EthCLSpecs.Fulu.Signing
import EthCLSpecs.Fulu.Randao
import EthCLSpecs.Fulu.Balances
import EthCLSpecs.Fulu.Registry
import EthCLSpecs.Fulu.Committees
import EthCLSpecs.Fulu.Accessors
import EthCLSpecs.Fulu.RegistryUpdates
import EthCLSpecs.Fulu.Rewards
import EthCLSpecs.Fulu.Deposits
import EthCLSpecs.Fulu.Blocks
import EthCLSpecs.Fulu.Withdrawals
import EthCLSpecs.Fulu.EpochProcessing
import EthCLSpecs.Fulu.Operations
import EthCLSpecs.Fulu.Transition
import EthCLSpecs.Fulu.ForkChoice
import EthCLSpecs.Fulu.Interface

/-!
# `EthCLSpecs.Fulu`: the Fulu fork

Re-export of the Fulu spec modules in load order (`SPECS_ARCHITECTURE.md` §3.1):
the foundations (`Types`, `Constants`), the per-container files and `BeaconState`
(`Containers`, `State`), the state-operation concern files (`Time` through
`Operations`, split by concern with the read/write seam resolved), the state
transition (`Transition`), fork choice (`ForkChoice`), and the fork-interface
instance (`Interface`).
-/
