package main

import (
	"fmt"
	"os"

	"gopkg.in/yaml.v3"
)

// Status values the coverage table uses. A row with any status other than
// statusImplemented is a tabled skip; a skip never fails the run.
const (
	statusImplemented = "implemented"
	statusNotImpl     = "not-implemented"
	statusForkNoSup   = "fork-not-supported"
)

// Compare roles the coverage table uses. See the header of coverage.yaml.
const (
	comparePerShape    = "per-shape"
	compareBool        = "compare-bool"
	compareScalar      = "compare-scalar"
	compareWindowEntry = "compare-window-entry"
	compareNone        = "none"
)

// Arg roles the coverage table uses for a record's named inputs.
const (
	argDecodeGloasState = "decode-gloas-state"
	argDecodeFuluState  = "decode-fulu-state"
	argScalarUint64     = "scalar-uint64"
	argIgnore           = "ignore"
)

// coverageRow is one row of the coverage table. It maps one
// (fork, preset, specName) triple to the Prysm symbols that carry the
// spec function, the roles that feed the record's inputs to them, and
// the comparison the runner makes.
type coverageRow struct {
	Fork     string            `yaml:"fork"`
	Preset   string            `yaml:"preset"`
	SpecName string            `yaml:"specName"`
	Target   string            `yaml:"target"`
	Status   string            `yaml:"status"`
	Reason   string            `yaml:"reason"`
	Symbols  []string          `yaml:"symbols"`
	Args     map[string]string `yaml:"args"`
	Compare  string            `yaml:"compare"`
}

// skipReason returns the reason a record with this row is a tabled skip.
func (r coverageRow) skipReason() string {
	if r.Reason != "" {
		return "tabled skip: " + r.Reason
	}
	return "tabled skip: status " + r.Status
}

// coverageTable is the parsed coverage.yaml. It is data the runner reads;
// the table lives beside the harness and the runner never edits it.
type coverageTable struct {
	Rows []coverageRow `yaml:"rows"`
}

// lookup finds the first row for a (fork, preset, specName) triple. A row
// with preset "both" matches either preset. A row with specName "*"
// matches any spec name of its fork, and a row with fork "*" matches any
// fork, so wildcard rows must follow specific rows in the table or they
// shadow them. The second return value reports whether a row exists but
// is scoped to the other preset, which is its own kind of tabled skip.
func (t coverageTable) lookup(fork, preset, specName string) (row *coverageRow, otherPreset bool) {
	for i := range t.Rows {
		r := &t.Rows[i]
		if r.Fork != fork && r.Fork != "*" {
			continue
		}
		if r.SpecName != specName && r.SpecName != "*" {
			continue
		}
		if r.Preset == "both" || r.Preset == preset {
			return r, false
		}
		otherPreset = true
	}
	return nil, otherPreset
}

// loadCoverage reads the coverage table at path.
func loadCoverage(path string) (coverageTable, error) {
	var table coverageTable
	data, err := os.ReadFile(path) // #nosec G304 -- the path is a flag or the file beside the module
	if err != nil {
		return table, fmt.Errorf("read coverage table: %w", err)
	}
	if err := yaml.Unmarshal(data, &table); err != nil {
		return table, fmt.Errorf("parse coverage table %s: %w", path, err)
	}
	return table, nil
}
