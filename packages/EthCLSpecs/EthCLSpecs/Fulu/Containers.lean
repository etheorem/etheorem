import EthCLSpecs.Fulu.Containers.Withdrawal

/-!
# `EthCLSpecs.Fulu.Containers`: the container re-export root

The component containers `BeaconState` references, one file per container in
dependency order under `Containers/` (`SPECS_ARCHITECTURE.md` §3.1 rows 3–15),
each carrying its `State`-free pure predicates. This module re-exports them so a
single `import EthCLSpecs.Fulu.Containers` brings the whole container layer into
scope; it holds no declarations of its own. `BeaconState` itself is row 19, in
`State` (it imports this module).

The block-body / attestation / execution-payload containers a `BeaconBlock`
carries live in `Blocks` (it also imports this module).
-/
