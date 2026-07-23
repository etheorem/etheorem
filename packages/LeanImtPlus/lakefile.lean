import Lake
open Lake DSL

package LeanImtPlus where
  license := "LGPL-3.0-only"
  licenseFiles := #["../../LICENSE"]
  moreLeancArgs := #["-march=native"]

require LeanSha256 from "../LeanSha256"

@[default_target]
lean_lib LeanImtPlus where
  precompileModules := true

lean_lib LeanImtPlusTests where
  roots := #[`LeanImtPlusTests]
  globs := #[.andSubmodules `LeanImtPlusTests]
