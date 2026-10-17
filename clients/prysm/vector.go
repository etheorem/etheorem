package main

import (
	"encoding/hex"
	"fmt"
	"os"
	"strconv"
	"strings"

	"gopkg.in/yaml.v3"
)

// rootLen is the byte length of an SSZ Merkle root.
const rootLen = 32

// sszHex is an SSZ value in the function format: the serialized bytes in
// hex, with the Merkle root beside them.
type sszHex struct {
	SSZ     []byte
	Root    [rootLen]byte
	RootHex string
}

// parseSSZHex decodes the {ssz, root} pair of a function-format node.
func parseSSZHex(node *yaml.Node) (*sszHex, error) {
	var fields map[string]string
	if err := node.Decode(&fields); err != nil {
		return nil, fmt.Errorf("line %d: ssz value: %w", node.Line, err)
	}
	sszStr, ok := fields["ssz"]
	if !ok {
		return nil, fmt.Errorf("line %d: ssz value has no ssz field", node.Line)
	}
	rootStr, ok := fields["root"]
	if !ok {
		return nil, fmt.Errorf("line %d: ssz value has no root field", node.Line)
	}
	raw, err := hex.DecodeString(strings.TrimPrefix(sszStr, "0x"))
	if err != nil {
		return nil, fmt.Errorf("line %d: ssz bytes: %w", node.Line, err)
	}
	rootBytes, err := hex.DecodeString(strings.TrimPrefix(rootStr, "0x"))
	if err != nil {
		return nil, fmt.Errorf("line %d: root: %w", node.Line, err)
	}
	if len(rootBytes) != rootLen {
		return nil, fmt.Errorf("line %d: root is %d bytes, want %d", node.Line, len(rootBytes), rootLen)
	}
	v := &sszHex{SSZ: raw, RootHex: rootStr}
	copy(v.Root[:], rootBytes)
	return v, nil
}

// inputValue is one named record input: either an SSZ value or a scalar
// uint64 literal. The coverage row's args role decides how the runner
// uses it.
type inputValue struct {
	ssz    *sszHex
	scalar uint64
}

// UnmarshalYAML implements yaml.Unmarshaler. A mapping node is an SSZ
// value, a scalar node is a uint64 literal.
func (v *inputValue) UnmarshalYAML(node *yaml.Node) error {
	if node.Kind == yaml.MappingNode {
		s, err := parseSSZHex(node)
		if err != nil {
			return err
		}
		v.ssz = s
		return nil
	}
	if node.Tag != "!!int" {
		return fmt.Errorf("line %d: scalar input is %s, want an integer", node.Line, node.Tag)
	}
	n, err := strconv.ParseUint(node.Value, 10, 64)
	if err != nil {
		return fmt.Errorf("line %d: scalar input: %w", node.Line, err)
	}
	v.scalar = n
	return nil
}

// outputValue is a record's expected output. A mapping is an SSZ value
// with its root, a bool or an integer is a scalar literal, and an empty
// string marks a record whose function must return an error.
type outputValue struct {
	ssz      *sszHex
	boolean  bool
	isBool   bool
	scalar   uint64
	isScalar bool
	errSet   bool
}

// UnmarshalYAML implements yaml.Unmarshaler.
func (v *outputValue) UnmarshalYAML(node *yaml.Node) error {
	if node.Kind == yaml.MappingNode {
		s, err := parseSSZHex(node)
		if err != nil {
			return err
		}
		v.ssz = s
		return nil
	}
	switch node.Tag {
	case "!!bool":
		b, err := strconv.ParseBool(node.Value)
		if err != nil {
			return fmt.Errorf("line %d: bool output: %w", node.Line, err)
		}
		v.boolean, v.isBool = b, true
	case "!!int":
		n, err := strconv.ParseUint(node.Value, 10, 64)
		if err != nil {
			return fmt.Errorf("line %d: scalar output: %w", node.Line, err)
		}
		v.scalar, v.isScalar = n, true
	case "!!str":
		// The generator writes '' for a shape that expects the function
		// to return an error. No other string is a valid output.
		if node.Value != "" {
			return fmt.Errorf("line %d: string output %q, want an SSZ value, a bool, an integer, or ''", node.Line, node.Value)
		}
		v.errSet = true
	default:
		return fmt.Errorf("line %d: output is %s, want a mapping, a bool, an integer, or ''", node.Line, node.Tag)
	}
	return nil
}

// vector is one function-format file: a self-contained YAML per vector
// (THEOREM_VECTORS_ARCHITECTURE.md §13.3).
type vector struct {
	Theorem         string                `yaml:"theorem"`
	Function        string                `yaml:"function"`
	Fork            string                `yaml:"fork"`
	Preset          string                `yaml:"preset"`
	Shape           string                `yaml:"shape"`
	Inputs          map[string]inputValue `yaml:"inputs"`
	Output          outputValue           `yaml:"output"`
	WitnessSearcher string                `yaml:"witnessSearcher"`
}

// loadVector reads one function-format file.
func loadVector(path string) (*vector, error) {
	data, err := os.ReadFile(path) // #nosec G304 -- the path comes from the directory walk
	if err != nil {
		return nil, fmt.Errorf("read record: %w", err)
	}
	var v vector
	if err := yaml.Unmarshal(data, &v); err != nil {
		return nil, fmt.Errorf("parse record: %w", err)
	}
	if v.Function == "" || v.Fork == "" || v.Preset == "" || v.Shape == "" {
		return nil, fmt.Errorf("record is missing function, fork, preset, or shape")
	}
	return &v, nil
}
