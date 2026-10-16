// Command prysm runs the function-format theorem vectors against Prysm.
//
// The harness walks the generator's function-format tree, maps each
// record through the coverage table, decodes the SSZ inputs of every
// record that runs with Prysm's SSZ library, checks each input's
// Merkle root, runs the mapped symbols, and compares the answer with
// the record's expected output. A record the coverage table maps to
// nothing, or maps to a status other than implemented, is a tabled
// skip with its reason in the summary. A skip never fails the run; a
// mismatch does.
//
// Prysm compiles one preset per binary. Build with `-tags minimal` for
// the minimal preset; the default build is mainnet. Run once per build:
//
//	go run . --out ../../packages/EthCLSpecs/theorem_vectors
//	go run -tags minimal . --out ../../packages/EthCLSpecs/theorem_vectors
package main

import (
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"os"
	"path/filepath"
)

// errFailedRecords reports that at least one record failed the run. main
// maps it to exit code 1; every other error is a harness-level problem
// and exits 2.
var errFailedRecords = errors.New("some records failed")

func main() {
	outDir := flag.String("out", "../../packages/EthCLSpecs/theorem_vectors", "directory the theorem-vector generator wrote")
	coveragePath := flag.String("coverage", "coverage.yaml", "path to the coverage table")
	flag.Parse()

	if err := runMain(*outDir, *coveragePath); err != nil {
		if errors.Is(err, errFailedRecords) {
			os.Exit(1)
		}
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
}

// runMain is main's body, split out so the flag handling stays at the top.
func runMain(outDir, coveragePath string) error {
	// The state functions read the chain config through params. The build
	// tag selects the proto fixed-vector lengths; the config needs the
	// matching preset set at startup, the way Prysm's own spectest
	// runners do it.
	applyPresetConfig()

	table, err := loadCoverage(coveragePath)
	if err != nil {
		return err
	}
	results, err := Run(outDir, table)
	if err != nil {
		return err
	}

	var passed, failed, skipped int
	var skipReasons []string
	skipCounts := map[string]int{}
	for _, r := range results {
		fmt.Printf("%s %s %s\n", r.Status, r.Path, r.Detail)
		switch r.Status {
		case statusPassed:
			passed++
		case statusFailed:
			failed++
		case statusSkipped:
			skipped++
			if skipCounts[r.Detail] == 0 {
				skipReasons = append(skipReasons, r.Detail)
			}
			skipCounts[r.Detail]++
		}
	}
	fmt.Printf("counts: passed=%d failed=%d skipped=%d\n", passed, failed, skipped)
	for _, reason := range skipReasons {
		fmt.Printf("skipped %d x %s\n", skipCounts[reason], reason)
	}

	data, err := json.MarshalIndent(results, "", "  ")
	if err != nil {
		return err
	}
	resultsPath := filepath.Join(outDir, "client-results.json")
	if err := os.WriteFile(resultsPath, append(data, '\n'), 0o644); err != nil {
		return fmt.Errorf("write %s: %w", resultsPath, err)
	}
	if failed > 0 {
		return errFailedRecords
	}
	return nil
}
