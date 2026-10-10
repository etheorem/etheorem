import EthCLSpecs.TheoremVectors

/-!
# `EthCLSpecs.TheoremVectors.Main`: the command-line harness

The `theorem_vectors` executable (`ARCHITECTURE.md` §15). It never
elaborates a theorem; the records on disk are its input. Four subcommands:

- `render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]`
  turns every record into every format that accepts it;
- `check` replays the rendered vectors through each format's consumer;
- `report [--out <dir>]` folds the outcome files into `report.md`;
- `list [--out <dir>]` prints one line per record.

Every subcommand answers `not implemented` with exit code 2 (§3 stages
the phases C1 through C3).
-/

set_option autoImplicit false

open EthCLLib.TheoremVectors

namespace EthCLSpecs.TheoremVectors.Main

/-- One exe subcommand (`ARCHITECTURE.md` §15). -/
inductive Subcommand where
  | render
  | check
  | report
  | list
  deriving DecidableEq, Repr, Inhabited

/-- Parse a subcommand name. -/
def Subcommand.ofString? : String → Option Subcommand
  | "render" => some .render
  | "check"  => some .check
  | "report" => some .report
  | "list"   => some .list
  | _        => none

/-- The flag names the subcommand takes: `render` and `check` take all
four, `report` and `list` take only `--out`. -/
def Subcommand.flags : Subcommand → List String
  | .render | .check => ["--fork", "--preset", "--format", "--out"]
  | .report | .list  => ["--out"]

/-- The flags the subcommands share. An `out` of `none` means
`EthCLSpecs.TheoremVectors.outDir`, the path the lakefile pins
(`ARCHITECTURE.md` §2.3, §15). -/
structure Options where
  fork   : Option String := none
  preset : Option PresetId := none
  format : Option String := none
  out    : Option String := none
  deriving Repr

/-- The usage text, printed on a malformed invocation. -/
def usage : String :=
  "usage: theorem_vectors <subcommand> [flags]\n" ++
  "  render [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]\n" ++
  "  check  [--fork <tag>] [--preset <id>] [--format <name>] [--out <dir>]\n" ++
  "  report [--out <dir>]\n" ++
  "  list   [--out <dir>]\n" ++
  "  presets: minimal | mainnet; --out defaults to " ++
    EthCLSpecs.TheoremVectors.outDir ++ "\n"

mutual
/-- Parse the flag list: every flag takes exactly one value, and a
repeated flag keeps its last occurrence. An unknown flag, a missing value,
a value that starts with `--`, or a preset name outside `minimal` /
`mainnet` fails. -/
def parseOptions (allowed : List String) : List String → Option Options
  | [] => some {}
  | [_] => none
  | flag :: value :: rest =>
    if value.startsWith "--" then none
    else parseFlag allowed flag value rest

/-- One flag with its value, and the tail still to parse. -/
def parseFlag (allowed : List String) (flag value : String)
    (rest : List String) : Option Options :=
  if flag == "--fork" && allowed.contains "--fork" then
    (parseOptions allowed rest).map fun o =>
      { o with fork := o.fork.orElse fun _ => some value }
  else if flag == "--preset" && allowed.contains "--preset" then
    match PresetId.ofTag? value with
    | none => none
    | some p => (parseOptions allowed rest).map fun o =>
      { o with preset := o.preset.orElse fun _ => some p }
  else if flag == "--format" && allowed.contains "--format" then
    (parseOptions allowed rest).map fun o =>
      { o with format := o.format.orElse fun _ => some value }
  else if flag == "--out" && allowed.contains "--out" then
    (parseOptions allowed rest).map fun o =>
      { o with out := o.out.orElse fun _ => some value }
  else none
end

/-- Parse the invocation, then answer `not implemented` with exit code 2
(`ARCHITECTURE.md` §15). -/
def run (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln usage
    return 2
  | sub :: rest =>
    match Subcommand.ofString? sub with
    | none =>
      IO.eprintln s!"theorem_vectors: unknown subcommand '{sub}'\n{usage}"
      return 2
    | some sc =>
      match parseOptions sc.flags rest with
      | none =>
        IO.eprintln s!"theorem_vectors {sub}: bad flags\n{usage}"
        return 2
      | some _opts =>
        IO.println s!"theorem_vectors {sub}: not implemented"
        return 2

end EthCLSpecs.TheoremVectors.Main

/-- The executable entry point. -/
def main (args : List String) : IO UInt32 :=
  EthCLSpecs.TheoremVectors.Main.run args
