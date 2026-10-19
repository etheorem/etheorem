package main

import (
	"bytes"
	"context"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/OffchainLabs/prysm/v7/beacon-chain/state"
	state_native "github.com/OffchainLabs/prysm/v7/beacon-chain/state/state-native"
	ethpb "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
)

// Record statuses the runner reports. A record ends passed, failed, or
// skipped; only a failure fails the run.
const (
	statusPassed  = "passed"
	statusFailed  = "failed"
	statusSkipped = "skipped"
)

// Result is the runner's answer for one record. It is one line of the
// summary and one entry of client-results.json.
type Result struct {
	Path       string `json:"path"`
	Fork       string `json:"fork"`
	Preset     string `json:"preset"`
	PyspecName string `json:"pyspecName"`
	Status     string `json:"status"`
	Detail     string `json:"detail"`
}

// sszMessage is the surface the runner needs from a Prysm proto type:
// decode, marshal, and merkleize. Both state protos and the PTCs entry
// satisfy it.
type sszMessage interface {
	UnmarshalSSZ([]byte) error
	MarshalSSZ() ([]byte, error)
	HashTreeRoot() ([32]byte, error)
}

// Run walks <outDir>/formats/function/<fork>/<preset>/ and returns one
// Result per record. The tree holds records of both presets; only the
// records of the preset this binary compiles execute, and the rest are
// tabled skips with a reason. A record's failures never abort the walk.
func Run(outDir string, table coverageTable) ([]Result, error) {
	root := filepath.Join(outDir, "formats", "function")
	if _, err := os.Stat(root); err != nil {
		return nil, fmt.Errorf("no function-format tree at %s", root)
	}
	results := []Result{}
	err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() || !strings.HasSuffix(path, ".yaml") {
			return nil
		}
		rel, relErr := filepath.Rel(outDir, path)
		if relErr != nil {
			return relErr
		}
		// The layout under the tree root is <fork>/<preset>/<target>/<file>.
		parts := strings.Split(filepath.ToSlash(rel), "/")
		if len(parts) != 6 {
			// A stray file is a per-record failure, so the rest of the
			// corpus still runs and the results file still lands.
			results = append(results, Result{
				Path:   filepath.ToSlash(rel),
				Status: statusFailed,
				Detail: "the record is not under <fork>/<preset>/<target>/",
			})
			return nil
		}
		// The Result path is relative to outDir, so the entries stay
		// joinable to the records no matter where the run started.
		results = append(results, runRecord(filepath.ToSlash(rel), path, parts[2], parts[3], parts[4], table))
		return nil
	})
	if err != nil {
		return nil, err
	}
	return results, nil
}

// runRecord runs one record through the gate, the mapped symbols, and the
// comparison. Every outcome lands in the Result; nothing panics and
// nothing stays silent. relPath names the record relative to outDir, path
// is the on-disk path, and targetDir is the record's target directory.
func runRecord(relPath, path, fork, preset, targetDir string, table coverageTable) Result {
	res := Result{Path: relPath, Fork: fork, Preset: preset}
	fail := func(format string, args ...any) Result {
		res.Status = statusFailed
		res.Detail = fmt.Sprintf(format, args...)
		return res
	}
	skip := func(reason string) Result {
		res.Status = statusSkipped
		res.Detail = reason
		return res
	}

	vec, err := loadVector(path)
	if err != nil {
		return fail("%v", err)
	}
	res.PyspecName = vec.Function

	// The file's own header must agree with the directory it sits in.
	if vec.Fork != fork || vec.Preset != preset {
		return fail("the record header says %s/%s, the directory says %s/%s", vec.Fork, vec.Preset, fork, preset)
	}

	// Prysm compiles one preset per binary. A record of the other preset
	// cannot even be decoded here, so it is a tabled skip with a reason.
	if preset != buildPreset {
		return skip(fmt.Sprintf("tabled skip: the record is %s, this binary compiles %s", preset, buildPreset))
	}

	row, otherPreset := table.lookup(fork, preset, vec.Function)
	if row == nil {
		if otherPreset {
			return skip("tabled skip: the coverage row is scoped to the other preset")
		}
		return skip(fmt.Sprintf("tabled skip: no coverage row for %s/%s/%s", fork, preset, vec.Function))
	}
	// A record filed under the wrong target names the row but not the
	// target the row was written for.
	if row.Target != "*" && row.Target != targetDir {
		return fail("the coverage row targets %s, the record sits under %s", row.Target, targetDir)
	}
	if row.Status != statusImplemented {
		return skip(row.skipReason())
	}
	if row.Compare == compareNone {
		return skip("tabled skip: the coverage row compares none")
	}

	env, err := decodeInputs(vec, row)
	if err != nil {
		return fail("%v", err)
	}

	run, ok := runnerFor(row.Symbols)
	if !ok {
		return fail("no runner mapped for symbols [%s]", strings.Join(row.Symbols, ", "))
	}
	out, err := run(env)
	if err != nil {
		return fail("%v", err)
	}
	return compareRecord(res, row, vec, out)
}

// decodeInputs decodes every record input per its args role and checks
// every SSZ input's root, the cheap gate every record that runs pays. A
// root mismatch is a failure that names the input, the file's root, and
// the computed one. The decoded state argument lands in the runEnv;
// inputs with the ignore role pay the gate and are never arguments.
func decodeInputs(vec *vector, row *coverageRow) (*runEnv, error) {
	env := &runEnv{ctx: context.Background(), scalars: map[string]uint64{}}
	// Sorted names keep the root-gate details, and so client-results.json,
	// the same across runs.
	names := make([]string, 0, len(vec.Inputs))
	for name := range vec.Inputs {
		names = append(names, name)
	}
	slices.Sort(names)
	seen := map[string]bool{}
	for _, name := range names {
		in := vec.Inputs[name]
		role, ok := row.Args[name]
		if !ok {
			return nil, fmt.Errorf("input %s has no args role in the coverage row", name)
		}
		seen[name] = true
		if in.ssz == nil {
			if role != argScalarUint64 {
				return nil, fmt.Errorf("scalar input %s has args role %s, want %s", name, role, argScalarUint64)
			}
			env.scalars[name] = in.scalar
			continue
		}

		// An SSZ input decodes with the state type its role names. An
		// ignored SSZ input decodes with the record fork's state type.
		var msg sszMessage
		var kind string
		switch {
		case role == argDecodeFuluState || (role == argIgnore && vec.Fork == kindFulu):
			msg, kind = &ethpb.BeaconStateFulu{}, kindFulu
		case role == argDecodeGloasState || (role == argIgnore && vec.Fork == kindGloas):
			msg, kind = &ethpb.BeaconStateGloas{}, kindGloas
		case role == argIgnore:
			return nil, fmt.Errorf("cannot decode ignored SSZ input %s of an unknown type", name)
		default:
			return nil, fmt.Errorf("SSZ input %s has args role %s, which decodes no SSZ", name, role)
		}
		if err := msg.UnmarshalSSZ(in.ssz.SSZ); err != nil {
			return nil, fmt.Errorf("input %s failed to deserialize: %v", name, err)
		}
		root, err := msg.HashTreeRoot()
		if err != nil {
			return nil, fmt.Errorf("input %s failed to merkleize: %v", name, err)
		}
		if root != in.ssz.Root {
			return nil, fmt.Errorf("root mismatch for input %s: file %s, computed %#x", name, in.ssz.RootHex, root)
		}

		if role == argIgnore {
			continue
		}
		if env.st != nil {
			return nil, fmt.Errorf("the coverage row maps a second state argument, input %s", name)
		}
		var st state.BeaconState
		if kind == kindFulu {
			st, err = state_native.InitializeFromProtoUnsafeFulu(msg.(*ethpb.BeaconStateFulu))
		} else {
			st, err = state_native.InitializeFromProtoUnsafeGloas(msg.(*ethpb.BeaconStateGloas))
		}
		if err != nil {
			return nil, fmt.Errorf("input %s failed to initialize: %v", name, err)
		}
		env.st, env.kind = st, kind
	}
	if row.Compare == comparePerShape && env.st == nil {
		return nil, fmt.Errorf("the coverage row decodes no state argument for a per-shape compare")
	}
	// A role the record never supplies would read as a zero scalar or a
	// nil state downstream, so every name the row feeds must exist.
	for name := range row.Args {
		if !seen[name] {
			return nil, fmt.Errorf("the coverage row feeds input %s, the record lacks it", name)
		}
	}
	return env, nil
}

// compareRecord checks the run outcome per the row's compare role. The
// detail names the client's answer and the expected one on a mismatch.
// base carries the record's path, fork, preset, and pyspec name.
func compareRecord(base Result, row *coverageRow, vec *vector, out runOutcome) Result {
	res := base
	pass := func(detail string) Result {
		res.Status = statusPassed
		res.Detail = detail
		return res
	}
	fail := func(format string, args ...any) Result {
		res.Status = statusFailed
		res.Detail = fmt.Sprintf(format, args...)
		return res
	}

	switch row.Compare {
	case comparePerShape:
		if vec.Shape == "runError" {
			if !vec.Output.errSet {
				return fail("the runError record carries no error marker")
			}
			if out.callErr != nil {
				return pass("error returned as expected")
			}
			return fail("the call succeeded, the record expects an error")
		}
		if vec.Shape != "runOk" {
			return fail("per-shape compare has no rule for shape %s", vec.Shape)
		}
		if out.callErr != nil {
			return fail("the call errored: %v", out.callErr)
		}
		if vec.Output.ssz == nil {
			return fail("the runOk record carries no SSZ output")
		}
		msg, err := marshaledState(out.kind, out.st)
		if err != nil {
			return fail("%v", err)
		}
		return compareSSZ(msg, vec, pass, fail, "post state")

	case compareBool:
		if !shapeSupports(vec.Shape, "eq", "iffTrue") {
			return fail("compare-bool has no rule for shape %s", vec.Shape)
		}
		if out.callErr != nil {
			return fail("the call errored: %v", out.callErr)
		}
		if !vec.Output.isBool {
			return fail("the record output is not a bool")
		}
		if out.boolean != vec.Output.boolean {
			return fail("bool mismatch: client %t, expected %t", out.boolean, vec.Output.boolean)
		}
		return pass("bool matched")

	case compareScalar:
		if !shapeSupports(vec.Shape, "eq", "iffTrue") {
			return fail("compare-scalar has no rule for shape %s", vec.Shape)
		}
		if out.callErr != nil {
			return fail("the call errored: %v", out.callErr)
		}
		if !vec.Output.isScalar {
			return fail("the record output is not an integer")
		}
		if out.scalar != vec.Output.scalar {
			return fail("scalar mismatch: client %d, expected %d", out.scalar, vec.Output.scalar)
		}
		return pass("scalar matched")

	case compareWindowEntry:
		if !shapeSupports(vec.Shape, "eq", "iffTrue", "bound") {
			return fail("compare-window-entry has no rule for shape %s", vec.Shape)
		}
		if out.callErr != nil {
			return fail("the call errored: %v", out.callErr)
		}
		if vec.Output.ssz == nil {
			return fail("the record carries no SSZ output for the window entry")
		}
		return compareSSZ(out.entry, vec, pass, fail, "window entry")

	default:
		return fail("unknown compare role %s", row.Compare)
	}
}

// shapeSupports reports whether the record's shape is one the compare
// role has a rule for. A bound-shaped record under a scalar compare, for
// one, would compare the wrong things, so the runner rejects the
// combination.
func shapeSupports(shape string, allowed ...string) bool {
	return slices.Contains(allowed, shape)
}

// compareSSZ compares a client-computed SSZ value with the record's
// output: bytes first, then the Merkle root. It is shared by the post
// state and the window entry.
func compareSSZ(msg sszMessage, vec *vector, pass func(string) Result, fail func(string, ...any) Result, what string) Result {
	got, err := msg.MarshalSSZ()
	if err != nil {
		return fail("%s failed to marshal: %v", what, err)
	}
	if !bytes.Equal(got, vec.Output.ssz.SSZ) {
		return fail("%s bytes differ: client %s, expected %s", what, hexBrief(got), hexBrief(vec.Output.ssz.SSZ))
	}
	root, err := msg.HashTreeRoot()
	if err != nil {
		return fail("%s failed to merkleize: %v", what, err)
	}
	if root != vec.Output.ssz.Root {
		return fail("%s root mismatch: client %#x, expected %s", what, root, vec.Output.ssz.RootHex)
	}
	return pass(what + " matched (bytes and root)")
}

// hexBrief renders a byte slice for a failure detail: the first bytes in
// hex, then the length. A post state is tens of kilobytes; the detail
// stays one line.
func hexBrief(b []byte) string {
	const brief = 16
	if len(b) <= brief {
		return fmt.Sprintf("%#x", b)
	}
	return fmt.Sprintf("%#x... (%d bytes)", b[:brief], len(b))
}
