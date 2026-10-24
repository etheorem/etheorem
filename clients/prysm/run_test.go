package main

import (
	"bytes"
	"errors"
	"fmt"
	"strings"
	"testing"

	state_native "github.com/OffchainLabs/prysm/v7/beacon-chain/state/state-native"
	fieldparams "github.com/OffchainLabs/prysm/v7/config/fieldparams"
	enginev1 "github.com/OffchainLabs/prysm/v7/proto/engine/v1"
)

// operandFixture builds a hand-set consolidation request, the SSZ operand
// the decode-consolidation-request role feeds to decodeInputs. It returns
// the proto, its serialized bytes, and its Merkle root, the triple a
// record stores for an SSZ input. The guard tests slice the bytes and
// flip the root; the happy test reads the proto's fields back out of the
// decoded operand. Non-zero bytes keep the fixture a real value, so a
// truncation bug cannot hide behind an all-zero field.
func operandFixture(t *testing.T) (*enginev1.ConsolidationRequest, []byte, [32]byte) {
	t.Helper()
	req := &enginev1.ConsolidationRequest{
		SourceAddress: make([]byte, fieldparams.FeeRecipientLength),
		SourcePubkey:  make([]byte, fieldparams.BLSPubkeyLength),
		TargetPubkey:  make([]byte, fieldparams.BLSPubkeyLength),
	}
	req.SourceAddress[0] = 0x01
	req.SourcePubkey[7] = 0x22
	req.TargetPubkey[fieldparams.BLSPubkeyLength-1] = 0x33
	sszBytes, err := req.MarshalSSZ()
	if err != nil {
		t.Fatalf("marshal the operand fixture: %v", err)
	}
	root, err := req.HashTreeRoot()
	if err != nil {
		t.Fatalf("merkleize the operand fixture: %v", err)
	}
	return req, sszBytes, root
}

// sszHexOf wraps any SSZ value's serialized bytes and root into the
// sszHex form both inputValue and outputValue carry.
func sszHexOf(sszBytes []byte, root [32]byte) *sszHex {
	return &sszHex{SSZ: sszBytes, Root: root, RootHex: fmt.Sprintf("%#x", root)}
}

// TestCompareRecordPerShapeAccepted pins the four (shape, output form)
// combinations the per-shape compare accepts. The SSZ cases carry a real
// decoded state and build the expected output from the same fixture, so
// the byte and root comparison genuinely runs instead of matching a
// canned string.
func TestCompareRecordPerShapeAccepted(t *testing.T) {
	proto := gloasFixtureState(t)
	sszBytes, err := proto.MarshalSSZ()
	if err != nil {
		t.Fatalf("marshal the fixture state: %v", err)
	}
	root, err := proto.HashTreeRoot()
	if err != nil {
		t.Fatalf("merkleize the fixture state: %v", err)
	}
	st, err := state_native.InitializeFromProtoUnsafeGloas(proto)
	if err != nil {
		t.Fatalf("initialize the fixture state: %v", err)
	}
	base := Result{
		Path:       "gloas/mainnet/target/rec.yaml",
		Fork:       "gloas",
		Preset:     buildPreset,
		PyspecName: "process_fixture",
	}

	tests := []struct {
		name       string
		shape      string
		out        runOutcome
		output     outputValue
		wantDetail string
	}{
		{
			name:       "run_error_with_marker",
			shape:      "runError",
			out:        runOutcome{callErr: errors.New("boom")},
			output:     outputValue{errSet: true},
			wantDetail: "error returned as expected",
		},
		{
			name:       "eq_with_error_marker",
			shape:      "eq",
			out:        runOutcome{callErr: errors.New("boom")},
			output:     outputValue{errSet: true},
			wantDetail: "error returned as expected",
		},
		{
			name:       "run_ok_with_ssz_output",
			shape:      "runOk",
			out:        runOutcome{st: st, kind: kindGloas},
			output:     outputValue{ssz: sszHexOf(sszBytes, root)},
			wantDetail: "post state matched (bytes and root)",
		},
		{
			name:       "eq_with_ssz_output",
			shape:      "eq",
			out:        runOutcome{st: st, kind: kindGloas},
			output:     outputValue{ssz: sszHexOf(sszBytes, root)},
			wantDetail: "post state matched (bytes and root)",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			vec := &vector{Shape: tt.shape, Output: tt.output}
			row := &coverageRow{Compare: comparePerShape}
			res := compareRecord(base, row, vec, tt.out)
			if res.Status != statusPassed {
				t.Fatalf("status %s with detail %q, want passed", res.Status, res.Detail)
			}
			if res.Detail != tt.wantDetail {
				t.Errorf("detail %q, want %q", res.Detail, tt.wantDetail)
			}
			if res.Path != base.Path || res.Fork != base.Fork ||
				res.Preset != base.Preset || res.PyspecName != base.PyspecName {
				t.Errorf("result carries path %q fork %q preset %q pyspec name %q, want the base record's",
					res.Path, res.Fork, res.Preset, res.PyspecName)
			}
		})
	}
}

// TestCompareRecordPerShapeRejected pins the combinations the per-shape
// compare rejects. A rejected combination is a (shape, output form)
// pair, so each row pins the stable message prefix and the form fragment
// that follows it.
func TestCompareRecordPerShapeRejected(t *testing.T) {
	_, sszBytes, root := operandFixture(t)

	tests := []struct {
		name     string
		shape    string
		out      runOutcome
		output   outputValue
		wantForm string
	}{
		{
			name:     "run_ok_with_error_marker",
			shape:    "runOk",
			output:   outputValue{errSet: true},
			wantForm: "error marker",
		},
		{
			name:     "run_error_with_ssz_output",
			shape:    "runError",
			out:      runOutcome{callErr: errors.New("boom")},
			output:   outputValue{ssz: sszHexOf(sszBytes, root)},
			wantForm: "ssz output",
		},
		{
			name:     "unknown_shape",
			shape:    "no-such-shape",
			output:   outputValue{errSet: true},
			wantForm: "error marker",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			vec := &vector{Shape: tt.shape, Output: tt.output}
			row := &coverageRow{Compare: comparePerShape}
			res := compareRecord(Result{}, row, vec, tt.out)
			if res.Status != statusFailed {
				t.Fatalf("status %s with detail %q, want failed", res.Status, res.Detail)
			}
			if !strings.Contains(res.Detail, "per-shape compare has no rule for shape") {
				t.Errorf("detail %q, want the no-rule message", res.Detail)
			}
			if !strings.Contains(res.Detail, tt.shape) {
				t.Errorf("detail %q, want it to name the shape %s", res.Detail, tt.shape)
			}
			if !strings.Contains(res.Detail, tt.wantForm) {
				t.Errorf("detail %q, want it to name the output form %s", res.Detail, tt.wantForm)
			}
		})
	}
}

// TestCompareRecordBool drives a second compare role, so the per-shape
// matrix cannot silently become the only covered path. An eq-shaped bool
// record passes when the client's answer matches and fails naming both
// answers when it does not.
func TestCompareRecordBool(t *testing.T) {
	tests := []struct {
		name       string
		out        runOutcome
		output     outputValue
		wantStatus string
		wantDetail string
	}{
		{
			name:       "eq_match",
			out:        runOutcome{boolean: true},
			output:     outputValue{boolean: true, isBool: true},
			wantStatus: statusPassed,
			wantDetail: "bool matched",
		},
		{
			name:       "eq_mismatch",
			out:        runOutcome{boolean: false},
			output:     outputValue{boolean: true, isBool: true},
			wantStatus: statusFailed,
			wantDetail: "bool mismatch: client false, expected true",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			vec := &vector{Shape: "eq", Output: tt.output}
			row := &coverageRow{Compare: compareBool}
			res := compareRecord(Result{}, row, vec, tt.out)
			if res.Status != tt.wantStatus {
				t.Fatalf("status %s with detail %q, want %s", res.Status, res.Detail, tt.wantStatus)
			}
			if res.Detail != tt.wantDetail {
				t.Errorf("detail %q, want %q", res.Detail, tt.wantDetail)
			}
		})
	}
}

// TestDecodeInputsOperandGuards drives the operand failure paths of
// decodeInputs: a truncated operand, a wrong root, a second operand, and
// a row that feeds an input the record lacks. Each must fail with the
// message that names the cause.
func TestDecodeInputsOperandGuards(t *testing.T) {
	_, sszBytes, root := operandFixture(t)
	truncated := sszBytes[:len(sszBytes)-1]
	badRoot := root
	badRoot[0] ^= 0xff

	tests := []struct {
		name       string
		inputs     map[string]inputValue
		args       map[string]string
		wantNeedle string
	}{
		{
			name: "truncated_operand",
			inputs: map[string]inputValue{
				"req": {ssz: sszHexOf(truncated, root)},
			},
			args:       map[string]string{"req": argDecodeConsolidationRequest},
			wantNeedle: "failed to deserialize",
		},
		{
			name: "wrong_operand_root",
			inputs: map[string]inputValue{
				"req": {ssz: sszHexOf(sszBytes, badRoot)},
			},
			args:       map[string]string{"req": argDecodeConsolidationRequest},
			wantNeedle: "root mismatch for input",
		},
		{
			name: "second_operand",
			inputs: map[string]inputValue{
				"req":  {ssz: sszHexOf(sszBytes, root)},
				"req2": {ssz: sszHexOf(sszBytes, root)},
			},
			args: map[string]string{
				"req":  argDecodeConsolidationRequest,
				"req2": argDecodeConsolidationRequest,
			},
			wantNeedle: "second consolidation request",
		},
		{
			name: "row_feeds_input_record_lacks",
			inputs: map[string]inputValue{
				"req": {ssz: sszHexOf(sszBytes, root)},
			},
			args: map[string]string{
				"req":   argDecodeConsolidationRequest,
				"ghost": argDecodeConsolidationRequest,
			},
			wantNeedle: "the coverage row feeds input",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			vec := &vector{Fork: kindGloas, Inputs: tt.inputs}
			row := &coverageRow{Args: tt.args}
			_, err := decodeInputs(vec, row)
			if err == nil {
				t.Fatal("decodeInputs must reject this record")
			}
			if !strings.Contains(err.Error(), tt.wantNeedle) {
				t.Errorf("error %q, want it to contain %q", err, tt.wantNeedle)
			}
		})
	}
}

// TestDecodeInputsOperandHappy decodes a well-formed operand end to end:
// the operand lands in the run env with its fields intact, no state
// argument appears beside it, and a scalar input rides along. The guard
// tests prove the rejections; this one proves the operand path decodes,
// so the guards cannot pass on a function that always errors.
func TestDecodeInputsOperandHappy(t *testing.T) {
	req, sszBytes, root := operandFixture(t)
	vec := &vector{
		Fork: kindGloas,
		Inputs: map[string]inputValue{
			"req":   {ssz: sszHexOf(sszBytes, root)},
			"delta": {scalar: 7},
		},
	}
	row := &coverageRow{Args: map[string]string{
		"req":   argDecodeConsolidationRequest,
		"delta": argScalarUint64,
	}}
	env, err := decodeInputs(vec, row)
	if err != nil {
		t.Fatalf("decodeInputs: %v", err)
	}
	if env.req == nil {
		t.Fatal("the operand must land in the run env")
	}
	if !bytes.Equal(env.req.SourceAddress, req.SourceAddress) ||
		!bytes.Equal(env.req.SourcePubkey, req.SourcePubkey) ||
		!bytes.Equal(env.req.TargetPubkey, req.TargetPubkey) {
		t.Errorf("decoded operand %+v, want the fixture's fields", env.req)
	}
	if env.st != nil {
		t.Errorf("an operand decode must not land a state argument, got kind %q", env.kind)
	}
	if env.scalars["delta"] != 7 {
		t.Errorf("scalar delta = %d, want 7", env.scalars["delta"])
	}
}
