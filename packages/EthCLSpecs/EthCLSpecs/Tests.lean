import EthCLSpecs.Tests.AuthoringShapes
import EthCLSpecs.Tests.BoxBinderPins
import EthCLSpecs.Tests.ClockMigrationPins
import EthCLSpecs.Tests.ClockSamplingAuditPins
import EthCLSpecs.Tests.CommitteeBoundsAssertPins
import EthCLSpecs.Tests.CommitteeCoverageOrderPins
import EthCLSpecs.Tests.ConfigurationClockPins
import EthCLSpecs.Tests.ConstantAuditPins
import EthCLSpecs.Tests.ConstantViews
import EthCLSpecs.Tests.DeadlineMigrationPins
import EthCLSpecs.Tests.DepositOperationPins
import EthCLSpecs.Tests.EpochMigrationPins
import EthCLSpecs.Tests.FuluDeclarationsAuditPins
import EthCLSpecs.Tests.FuluForkChoicePins
import EthCLSpecs.Tests.GloasCommitteesPins
import EthCLSpecs.Tests.GloasForkChoicePins
import EthCLSpecs.Tests.GloasHezeAuditPins
import EthCLSpecs.Tests.GloasSlotMigrationPins
import EthCLSpecs.Tests.HezeCommitteesPins
import EthCLSpecs.Tests.HezeForkChoicePins
import EthCLSpecs.Tests.IndexMigrationPins
import EthCLSpecs.Tests.ParticipationFlagsMigrationPins
import EthCLSpecs.Tests.PendingDepositsScanPins
import EthCLSpecs.Tests.PlainArithmeticPins
import EthCLSpecs.Tests.SlotMigrationPins
import EthCLSpecs.Tests.SyncAggregateLookupPins
import EthCLSpecs.Tests.TransitionFamilyAuditPins
import EthCLSpecs.Tests.ValidatorIndexMigrationPins
import EthCLSpecs.Tests.WalkingSkeleton
import EthCLSpecs.Tests.WidthCastPins

/-!
# `EthCLSpecs.Tests`: Lean-internal spec self-tests

`#guard` / `native_decide` checks over hand-built inputs, confirming spec
behavior independently of the `pytest-xdist` pyspec harness. The sources
live under `EthCLSpecs/Tests/` (namespace `EthCLSpecs.Tests.*`), built as their
own `lean_lib` and excluded from the shipped library (`SPECS_ARCHITECTURE.md`
§3.6).

The `*Pins` modules are the vectorless build gates: reject branches and helper
values no conformance vector reaches, one module per fork body they pin. They
were written beside the declarations they pin and moved here, since a
`native_decide` compiled into a fork body is evaluation every consumer of that
body carries, for a check only the build gate reads. `ConstantViews` pins the
derived constant views of the arithmetic layer the same way.
-/
