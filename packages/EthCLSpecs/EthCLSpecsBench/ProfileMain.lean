import EthCLSpecsBench.Profile
import SizzLeanBench.Runner

/-!
# `EthCLSpecsBench.ProfileMain`: the `specs_profile` exe driver

Runs the Stage 17d pass-2 container profile over one upstream vector.
The caller supplies raw (snappy-removed) buffers as paths:

```
specs_profile <pre.ssz> [<block_0.ssz> …]
```

`just ethcl-profile` wraps the snappy step and the TSV redirection, so
day to day nobody types this. Stdout carries the TSV; stderr carries
the vector's shape and the anti-DCE sink, so a redirect keeps the TSV
clean.
-/

set_option autoImplicit false

open SizzLeanBench.Runner

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: specs_profile <pre.ssz> [<block_0.ssz> …]"
    return 1
  | prePath :: blockPaths =>
    let preBytes ← IO.FS.readBinFile prePath
    let blockBuffers ← (blockPaths.toArray).mapM fun p =>
      IO.FS.readBinFile (System.FilePath.mk p)
    printHeader
    EthCLSpecsBench.Profile.runAll preBytes blockBuffers
    return 0
