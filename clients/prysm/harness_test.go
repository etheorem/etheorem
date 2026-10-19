package main

import (
	"fmt"
	"strings"
	"testing"

	"github.com/OffchainLabs/go-bitfield"
	fieldparams "github.com/OffchainLabs/prysm/v7/config/fieldparams"
	"github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
	ethpb "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
)

// loadTableForTest reads the coverage table the runner maps on.
func loadTableForTest(t *testing.T) coverageTable {
	t.Helper()
	table, err := loadCoverage("coverage.yaml")
	if err != nil {
		t.Fatalf("load coverage table: %v", err)
	}
	return table
}

// fixtureTable is the committed table with the fixture target's row
// widened to both presets. The committed row is scoped to minimal because
// the real corpus carries is_builder_index at minimal only, and a
// preset-scoped row is a tabled skip under the other build. The fixture
// exists to prove the harness under both builds, so the test widens the
// row in memory; the committed table file stays untouched.
func fixtureTable(t *testing.T) coverageTable {
	t.Helper()
	table := loadTableForTest(t)
	for i := range table.Rows {
		if table.Rows[i].PyspecName == "is_builder_index" {
			table.Rows[i].Preset = "both"
		}
	}
	return table
}

// checkFixturePresetScoping checks the records of the other preset: they
// are tabled skips, because this binary cannot decode them. It fails the
// test unless exactly one record ran, the one of this build's preset.
func checkFixturePresetScoping(t *testing.T, results []Result) {
	t.Helper()
	ran := 0
	for _, r := range results {
		if r.Preset == buildPreset {
			ran++
			continue
		}
		if r.Status != statusSkipped {
			t.Errorf("%s: status %s, want skipped; this binary compiles %s", r.Path, r.Status, buildPreset)
		}
	}
	if ran != 1 {
		t.Fatalf("the %s build ran %d fixture records, want 1", buildPreset, ran)
	}
}

// TestFixturePasses drives the runner over the fixture tree. The fixture's
// answer is hand-computed (see testdata), so a pass here proves the runner
// executed the record and matched its hand-computed answer.
func TestFixturePasses(t *testing.T) {
	results, err := Run("testdata", fixtureTable(t))
	if err != nil {
		t.Fatalf("run harness over testdata: %v", err)
	}
	if len(results) != 2 {
		t.Fatalf("the fixture tree holds %d records, want 2 (one per preset)", len(results))
	}
	checkFixturePresetScoping(t, results)
	for _, r := range results {
		if r.Preset != buildPreset {
			continue
		}
		if r.Status != statusPassed {
			t.Errorf("%s: status %s, want passed (detail %q)", r.Path, r.Status, r.Detail)
			continue
		}
		if r.Detail != "bool matched" {
			t.Errorf("%s: detail %q, want %q", r.Path, r.Detail, "bool matched")
		}
	}
}

// TestCorruptedFails drives the runner over the corrupted fixture tree,
// where the expected answer is flipped. The runner must detect the
// mismatch and name both answers in the detail.
func TestCorruptedFails(t *testing.T) {
	results, err := Run("testdata-corrupted", fixtureTable(t))
	if err != nil {
		t.Fatalf("run harness over testdata-corrupted: %v", err)
	}
	if len(results) != 2 {
		t.Fatalf("the corrupted tree holds %d records, want 2 (one per preset)", len(results))
	}
	checkFixturePresetScoping(t, results)
	for _, r := range results {
		if r.Preset != buildPreset {
			continue
		}
		if r.Status != statusFailed {
			t.Errorf("%s: status %s, want failed; the corrupted fixture must not pass", r.Path, r.Status)
			continue
		}
		if !strings.Contains(r.Detail, "bool mismatch: client true, expected false") {
			t.Errorf("%s: detail %q, want it to name the client's answer and the expected one", r.Path, r.Detail)
		}
	}
}

// gloasFixtureState returns a zero-valued but well-formed BeaconStateGloas:
// every fixed-size field carries its declared length, so the SSZ marshal
// and the Merkle root succeed. The root-gate test needs a real SSZ input,
// and the scalar-only fixture above cannot supply one. fieldparams carries
// the preset's lengths; the four Gloas-specific lengths sit in the switch,
// and a client bump that changes one fails the marshal here, loudly.
func gloasFixtureState(t *testing.T) *ethpb.BeaconStateGloas {
	t.Helper()
	lookahead, availability, payments, window := 16, 8, 16, 24
	if buildPreset == "mainnet" {
		lookahead, availability, payments, window = 64, 1024, 64, 96
	}
	roots := func(n int) [][]byte {
		rs := make([][]byte, n)
		for i := range rs {
			rs[i] = make([]byte, fieldparams.RootLength)
		}
		return rs
	}
	bid := func(n int) []primitives.ValidatorIndex {
		return make([]primitives.ValidatorIndex, n)
	}
	keys := func(n int) [][]byte {
		ks := make([][]byte, n)
		for i := range ks {
			ks[i] = make([]byte, fieldparams.BLSPubkeyLength)
		}
		return ks
	}
	paymentList := make([]*ethpb.BuilderPendingPayment, payments)
	for i := range paymentList {
		paymentList[i] = &ethpb.BuilderPendingPayment{
			Weight: primitives.Gwei(i),
			Withdrawal: &ethpb.BuilderPendingWithdrawal{
				FeeRecipient: make([]byte, fieldparams.FeeRecipientLength),
			},
			ProposerIndex: primitives.ValidatorIndex(i),
		}
	}
	windowList := make([]*ethpb.PTCs, window)
	for i := range windowList {
		windowList[i] = &ethpb.PTCs{ValidatorIndices: bid(fieldparams.PTCSize)}
	}
	return &ethpb.BeaconStateGloas{
		GenesisValidatorsRoot: make([]byte, fieldparams.RootLength),
		Fork: &ethpb.Fork{
			PreviousVersion: make([]byte, fieldparams.VersionLength),
			CurrentVersion:  make([]byte, fieldparams.VersionLength),
		},
		LatestBlockHeader: &ethpb.BeaconBlockHeader{
			ParentRoot: make([]byte, fieldparams.RootLength),
			StateRoot:  make([]byte, fieldparams.RootLength),
			BodyRoot:   make([]byte, fieldparams.RootLength),
		},
		BlockRoots:  roots(fieldparams.BlockRootsLength),
		StateRoots:  roots(fieldparams.StateRootsLength),
		RandaoMixes: roots(fieldparams.RandaoMixesLength),
		Slashings:   make([]uint64, fieldparams.SlashingsLength),
		Eth1Data: &ethpb.Eth1Data{
			DepositRoot: make([]byte, fieldparams.RootLength),
			BlockHash:   make([]byte, fieldparams.RootLength),
		},
		PreviousJustifiedCheckpoint: &ethpb.Checkpoint{Root: make([]byte, fieldparams.RootLength)},
		CurrentJustifiedCheckpoint:  &ethpb.Checkpoint{Root: make([]byte, fieldparams.RootLength)},
		FinalizedCheckpoint:         &ethpb.Checkpoint{Root: make([]byte, fieldparams.RootLength)},
		CurrentSyncCommittee: &ethpb.SyncCommittee{
			Pubkeys:         keys(fieldparams.SyncCommitteeLength),
			AggregatePubkey: make([]byte, fieldparams.BLSPubkeyLength),
		},
		NextSyncCommittee: &ethpb.SyncCommittee{
			Pubkeys:         keys(fieldparams.SyncCommitteeLength),
			AggregatePubkey: make([]byte, fieldparams.BLSPubkeyLength),
		},
		LatestExecutionPayloadBid: &ethpb.ExecutionPayloadBid{
			ParentBlockHash:       make([]byte, fieldparams.RootLength),
			ParentBlockRoot:       make([]byte, fieldparams.RootLength),
			BlockHash:             make([]byte, fieldparams.RootLength),
			PrevRandao:            make([]byte, fieldparams.RootLength),
			FeeRecipient:          make([]byte, fieldparams.FeeRecipientLength),
			ExecutionRequestsRoot: make([]byte, fieldparams.RootLength),
		},
		JustificationBits:            bitfield.Bitvector4(make([]byte, 1)),
		ProposerLookahead:            bid(lookahead),
		ExecutionPayloadAvailability: make([]byte, availability),
		BuilderPendingPayments:       paymentList,
		PtcWindow:                    windowList,
		LatestBlockHash:              make([]byte, fieldparams.RootLength),
	}
}

// TestRootGate drives the root gate directly. The gate is the harness's
// central check, so the test feeds it a well-formed Gloas state twice:
// once with the state's true root, which must decode through to the state
// argument, and once with a flipped root, which must fail with the
// mismatch message that names the input.
func TestRootGate(t *testing.T) {
	msg := gloasFixtureState(t)
	sszBytes, err := msg.MarshalSSZ()
	if err != nil {
		t.Fatalf("marshal the fixture state: %v", err)
	}
	root, err := msg.HashTreeRoot()
	if err != nil {
		t.Fatalf("merkleize the fixture state: %v", err)
	}
	row := &coverageRow{
		Status:  statusImplemented,
		Compare: comparePerShape,
		Args:    map[string]string{"preState": argDecodeGloasState},
	}
	input := func(root [32]byte) map[string]inputValue {
		return map[string]inputValue{
			"preState": {ssz: &sszHex{SSZ: sszBytes, Root: root, RootHex: fmt.Sprintf("%#x", root[:])}},
		}
	}

	env, err := decodeInputs(&vector{Fork: kindGloas, Inputs: input(root)}, row)
	if err != nil {
		t.Fatalf("the true root must pass the gate: %v", err)
	}
	if env.st == nil || env.kind != kindGloas {
		t.Fatalf("the gate must land the decoded state argument, got kind %q", env.kind)
	}
	bad := root
	bad[0] ^= 0xff
	_, err = decodeInputs(&vector{Fork: kindGloas, Inputs: input(bad)}, row)
	if err == nil {
		t.Fatal("the flipped root must fail the gate")
	}
	if !strings.HasPrefix(err.Error(), "root mismatch for input preState") {
		t.Fatalf("detail %q, want the root-mismatch message", err)
	}
	if !strings.Contains(err.Error(), fmt.Sprintf("%#x", bad[:])) {
		t.Fatalf("detail %q, want the computed root", err)
	}
}

// TestCoverageRowScoping drives the runner over the fixture tree with the
// committed table. The is_builder_index row is scoped to minimal, so under
// the mainnet build both records are tabled skips: one for the build
// mismatch, one for the row's preset scope. Under the minimal build the
// minimal record runs and passes.
func TestCoverageRowScoping(t *testing.T) {
	results, err := Run("testdata", loadTableForTest(t))
	if err != nil {
		t.Fatalf("run harness over testdata: %v", err)
	}
	for _, r := range results {
		if r.Preset != buildPreset {
			if r.Status != statusSkipped {
				t.Errorf("%s: status %s, want skipped; this binary compiles %s", r.Path, r.Status, buildPreset)
			}
			continue
		}
		if buildPreset == "minimal" {
			if r.Status != statusPassed {
				t.Errorf("%s: status %s, want passed; the row covers the minimal build", r.Path, r.Status)
			}
			continue
		}
		if r.Status != statusSkipped || !strings.Contains(r.Detail, "the coverage row is scoped to the other preset") {
			t.Errorf("%s: status %s detail %q, want a skip naming the row's preset scope", r.Path, r.Status, r.Detail)
		}
	}
}

// TestImplementedRowsResolveRunners binds the committed coverage table to
// the runner map: every implemented row's symbols must resolve to a
// runner, even when the corpus holds no record for the row and no run
// ever looks it up. A symbols string that drifts from mapping.go fails
// here instead of failing only on a real-corpus record.
func TestImplementedRowsResolveRunners(t *testing.T) {
	for _, row := range loadTableForTest(t).Rows {
		if row.Status != statusImplemented {
			continue
		}
		if _, ok := runnerFor(row.Symbols); !ok {
			t.Errorf("%s/%s/%s: no runner for symbols %q", row.Fork, row.Preset, row.PyspecName, row.Symbols)
		}
	}
}
