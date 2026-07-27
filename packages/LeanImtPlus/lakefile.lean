import Lake
open Lake DSL

package LeanImtPlus where
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  moreLeancArgs := #["-march=native"]

require LeanSha256 from "../LeanSha256"
require LeanHazmatSha256 from "../LeanHazmatSha256"
require LeanPoseidon from "../LeanPoseidon"

-- Keep the generic core independent from native backends at link time.
-- Precompiling this aggregate would make Lake link every extern_lib owned
-- by adapter dependencies, including LeanPoseidon's test-only Rust oracle.
@[default_target]
lean_lib LeanImtPlus

lean_lib LeanImtPlusTests where
  roots := #[`LeanImtPlusTests]
  globs := #[.andSubmodules `LeanImtPlusTests]
