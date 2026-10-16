//go:build !minimal

package main

import (
	"github.com/OffchainLabs/prysm/v7/config/params"
)

// buildPreset names the preset this binary compiles. Prysm selects the
// fixed-vector lengths of the state protos with the `minimal` build tag;
// the default build is mainnet. The runner walks the whole function-format
// tree but executes only the records of this preset, and table-skips the
// rest with a reason.
const buildPreset = "mainnet"

// applyPresetConfig points Prysm's chain config at this build's preset.
// MainnetConfig returns a fresh config, so the override starts clean.
func applyPresetConfig() {
	params.OverrideBeaconConfig(params.MainnetConfig())
}
