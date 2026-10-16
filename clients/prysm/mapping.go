package main

import (
	"context"
	"fmt"
	"strings"

	"github.com/OffchainLabs/prysm/v7/beacon-chain/core/gloas"
	"github.com/OffchainLabs/prysm/v7/beacon-chain/core/helpers"
	"github.com/OffchainLabs/prysm/v7/beacon-chain/state"
	state_native "github.com/OffchainLabs/prysm/v7/beacon-chain/state/state-native"
	"github.com/OffchainLabs/prysm/v7/consensus-types/primitives"
	ethpb "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
)

// State kinds a record's state argument can decode to.
const (
	kindFulu  = "fulu"
	kindGloas = "gloas"
)

// runEnv carries the decoded record inputs to the mapped symbols. The
// state argument is the one input the coverage row's args role maps to
// decode-*-state; scalars hold every scalar-uint64 input by name.
type runEnv struct {
	ctx     context.Context
	scalars map[string]uint64
	st      state.BeaconState
	kind    string
}

// runOutcome is what the mapped symbols produced. callErr is the mapped
// call's own error: an expected part of runError records, a failure
// everywhere else. Exactly one of the other fields is set per compare role.
type runOutcome struct {
	callErr error
	st      state.BeaconState
	kind    string
	entry   *ethpb.PTCs
	boolean bool
	scalar  uint64
}

// runFunc runs a coverage row's symbols against a decoded record.
type runFunc func(*runEnv) (runOutcome, error)

// runnerFor returns the runner for a row's symbol list. The key is the
// symbols joined in order, because two-symbol rows spell the composition
// the proved theorem states.
func runnerFor(symbols []string) (runFunc, bool) {
	r, ok := runners[strings.Join(symbols, " ")]
	return r, ok
}

// runners maps the coverage table's symbol lists to Go closures. Adding a
// row to the table means adding the entry here; a row with no entry is a
// harness gap the runner reports as a failure.
var runners = map[string]runFunc{
	"beacon-chain/core/helpers.IncreaseBalance": func(e *runEnv) (runOutcome, error) {
		err := helpers.IncreaseBalance(e.st, primitives.ValidatorIndex(e.scalars["i"]), e.scalars["delta"])
		return runOutcome{callErr: err, st: e.st, kind: e.kind}, nil
	},

	"beacon-chain/core/helpers.DecreaseBalance": func(e *runEnv) (runOutcome, error) {
		err := helpers.DecreaseBalance(e.st, primitives.ValidatorIndex(e.scalars["i"]), e.scalars["delta"])
		return runOutcome{callErr: err, st: e.st, kind: e.kind}, nil
	},

	"beacon-chain/core/gloas.ProcessBuilderPendingPayments": func(e *runEnv) (runOutcome, error) {
		err := gloas.ProcessBuilderPendingPayments(e.ctx, e.st)
		return runOutcome{callErr: err, st: e.st, kind: e.kind}, nil
	},

	"beacon-chain/core/gloas.InitiateBuilderExit": func(e *runEnv) (runOutcome, error) {
		err := gloas.InitiateBuilderExit(e.st, primitives.BuilderIndex(e.scalars["builderIndex"]))
		return runOutcome{callErr: err, st: e.st, kind: e.kind}, nil
	},

	"beacon-chain/state.CanBuilderCoverBid": func(e *runEnv) (runOutcome, error) {
		// CanBuilderCoverBid is a method on the state.BeaconState
		// interface's Gloas read-only fields.
		ok, err := e.st.CanBuilderCoverBid(
			primitives.BuilderIndex(e.scalars["builderIndex"]),
			primitives.Gwei(e.scalars["bidAmount"]),
		)
		return runOutcome{callErr: err, boolean: ok}, nil
	},

	// is_builder_index composes the conversion ahead of the test.
	"consensus-types/primitives.BuilderIndex.ToValidatorIndex consensus-types/primitives.ValidatorIndex.IsBuilderIndex": func(e *runEnv) (runOutcome, error) {
		vi := primitives.BuilderIndex(e.scalars["bi"]).ToValidatorIndex()
		return runOutcome{boolean: vi.IsBuilderIndex()}, nil
	},

	// The round-trip theorems compose both directions and expect the input back.
	"consensus-types/primitives.BuilderIndex.ToValidatorIndex consensus-types/primitives.ValidatorIndex.ToBuilderIndex": func(e *runEnv) (runOutcome, error) {
		bi := primitives.BuilderIndex(e.scalars["bi"]).ToValidatorIndex().ToBuilderIndex()
		return runOutcome{scalar: uint64(bi)}, nil
	},

	"consensus-types/primitives.ValidatorIndex.ToBuilderIndex consensus-types/primitives.BuilderIndex.ToValidatorIndex": func(e *runEnv) (runOutcome, error) {
		vi := primitives.ValidatorIndex(e.scalars["vi"]).ToBuilderIndex().ToValidatorIndex()
		return runOutcome{scalar: uint64(vi)}, nil
	},

	// initializePTCWindow is unexported at the pin; UpgradeToGloas is the
	// public path that computes it on the same input. The second symbol
	// names the PTCWindow getter on the upgraded state. The record's
	// output is one window entry, a spec Vector of uint64; Prysm spells
	// the entry as ethpb.PTCs. The two have the same bytes and the same
	// root, which is why the byte comparison holds.
	"beacon-chain/core/gloas.UpgradeToGloas beacon-chain/state.PTCWindow": func(e *runEnv) (runOutcome, error) {
		st, err := gloas.UpgradeToGloas(e.ctx, e.st)
		if err != nil {
			return runOutcome{}, fmt.Errorf("UpgradeToGloas: %w", err)
		}
		window, err := st.PTCWindow()
		if err != nil {
			return runOutcome{}, fmt.Errorf("PTCWindow: %w", err)
		}
		idx := e.scalars["i"]
		if int(idx) >= len(window) {
			return runOutcome{}, fmt.Errorf("window index %d out of range, the window has %d entries", idx, len(window))
		}
		return runOutcome{entry: window[idx]}, nil
	},
}

// marshaledState rebuilds the state's proto so the runner can marshal it
// and hash its root after the mapped call mutated it.
func marshaledState(kind string, st state.BeaconState) (sszMessage, error) {
	switch kind {
	case kindFulu:
		return state_native.ProtobufBeaconStateFulu(st.ToProtoUnsafe())
	case kindGloas:
		return state_native.ProtobufBeaconStateGloas(st.ToProtoUnsafe())
	default:
		return nil, fmt.Errorf("unknown state kind %q", kind)
	}
}
