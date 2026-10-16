//go:build minimal

package main

import (
	"github.com/OffchainLabs/prysm/v7/config/params"
)

// buildPreset names the preset this binary compiles. See preset.go.
const buildPreset = "minimal"

// applyPresetConfig points Prysm's chain config at this build's preset.
// MinimalSpecConfig returns a fresh config per call; the override needs
// no further copy. Prysm's own spectest runners pair the minimal build
// tag with this same call.
func applyPresetConfig() {
	params.OverrideBeaconConfig(params.MinimalSpecConfig())
}
