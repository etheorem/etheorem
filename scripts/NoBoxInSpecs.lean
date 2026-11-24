import Lean

/-!
# `scripts/NoBoxInSpecs.lean`: the CL specs hold plain values

The CL specs (the `EthCLLib` framework and the `EthCLSpecs` fork bodies, their
proofs, tests, and runners) hold plain SSZ structs. `SizzLean` keeps the box
(`SizzLean.Cache.SSZ.Box`), its two backings (`UncachedSSZ`, `TreeBacked`), and
the macros over them, for callers outside the specs. This script is the rule that
keeps the box out of the specs. Run it from the repo root, after the build:

```
lake env lean --run scripts/NoBoxInSpecs.lean
```

`just check-no-box` runs it after a source search for the box names. The search
catches a macro spelling such as `sszGet` that leaves no constant behind; this
script catches a use under any spelling, an `open` or an alias included.

## The rule

A **spec constant** is a constant whose module sits under `EthCLLib` or
`EthCLSpecs`. A **box constant** is a constant under one of the namespaces in
`boxRoots`. The rule fails when a spec constant depends on a box constant: its
type or its value names one, directly or through any chain of other constants.
A constructor counts as part of its inductive, so a type with a boxed field
carries the dependency to every constant that names the type.

The script reads the compiled `.olean`s, so it sees what the elaborator produced
after every macro and every notation ran. The bench library `EthCLSpecsBench`
sits outside the scope on purpose: its profile roots a `BeaconState` through
`SSZ.FastBox` to measure the cache.

## The scope is complete

A source file that no library root imports never reaches an `.olean`, so the
rule could not see it. The script discovers every `.lean` file under the two
source trees and imports each module by name. It fails first, and names the
file, when a module has no `.olean`.

## Lean idioms annotated on first appearance

* `importModules`: builds an `Environment` from compiled `.olean`s. The script
  reads `env.constants` alone, so it passes no `loadExts`. That keeps the
  imported `initialize` blocks from running, one of which calls the FFI hasher
  the interpreter has no native code for.
* `ConstantInfo.getUsedConstantsAsSet`: every constant the type and the value
  name, a proof term included. A theorem whose proof unfolds the box depends on
  the box.
* `EnvironmentHeader.moduleNames`: the imported modules in import order, each
  module after the modules it imports. One pass in that order computes which
  modules can reach a box module.
-/

set_option autoImplicit false

open Lean

namespace NoBoxInSpecs

/-! ## Pinned names and paths -/

/-- The namespaces the box lives in. `SizzLean.Cache.SSZ` holds `Box` and its
flavours (`FastBox`, `PureBox`, `CachedBox`, `UncachedBox`). The other two are the
backings a box wraps: `UncachedSSZ` (a value beside its root) and `TreeBacked`,
which `CachedSSZ` names. -/
def boxRoots : Array Name :=
  #[`SizzLean.Cache.SSZ, `SizzLean.Cache.UncachedSSZ, `SizzLean.Cache.TreeBacked,
    `SizzLean.Cache.CachedSSZ]

/-- The module that declares `SizzLean.Cache.SSZ.Box`. The script imports it
beside the spec modules, so the box constants are in the environment even when no
spec module imports them, and the guard in `run` can tell a clean tree from a
stale `boxRoots`. -/
def boxModule : Name := `SizzLean.Cache.Box

/-- The module prefixes of the spec constants. `Name.isPrefixOf` compares whole
components, so `EthCLSpecs` does not match `EthCLSpecsBench`. -/
def specRoots : Array Name := #[`EthCLLib, `EthCLSpecs]

/-- One source tree the rule covers: the directory `<packageDir>/<rootModule>`
and the root file `<packageDir>/<rootModule>.lean` beside it. -/
structure SourceTree where
  /-- The package directory, the root a module path is relative to. -/
  packageDir : System.FilePath
  /-- The library's root module, `EthCLLib` for `EthCLLib.lean`. -/
  rootModule : String

/-- The two source trees: `packages/EthCLLib/EthCLLib` and
`packages/EthCLSpecs/EthCLSpecs`, and the root file beside each. -/
def sourceTrees : Array SourceTree :=
  #[{ packageDir := "packages/EthCLLib", rootModule := "EthCLLib" },
    { packageDir := "packages/EthCLSpecs", rootModule := "EthCLSpecs" }]

/-- The most dependency chains the report prints. One chain is enough to find a
use, and the last line counts the chains left out. -/
def maxReported : Nat := 20

/-! ## Module discovery -/

/-- The module a source file declares: `packages/EthCLLib/EthCLLib/Spec/State.lean`
under `packages/EthCLLib` is `EthCLLib.Spec.State`. -/
def moduleOf (packageDir file : System.FilePath) : Name :=
  let parts := file.withExtension "" |>.components.drop packageDir.components.length
  parts.foldl (fun n p => n ++ p.toName) Name.anonymous

/-- Every module of one source tree: the root file and each `.lean` file under the
root directory. -/
def treeModules (tree : SourceTree) : IO (Array Name) := do
  let rootFile := tree.packageDir / s!"{tree.rootModule}.lean"
  let mut modules : Array Name := #[]
  if ← rootFile.pathExists then
    modules := modules.push (moduleOf tree.packageDir rootFile)
  for file in ← (tree.packageDir / tree.rootModule).walkDir do
    if file.extension == some "lean" then
      modules := modules.push (moduleOf tree.packageDir file)
  return modules

/-- Every module of both source trees, sorted so the import order is stable. -/
def specModules : IO (Array Name) := do
  let mut modules : Array Name := #[]
  for tree in sourceTrees do
    modules := modules ++ (← treeModules tree)
  return modules.qsort fun a b => toString a < toString b

/-! ## The dependency walk -/

/-- Does `name` sit under one of `roots`? -/
def under (roots : Array Name) (name : Name) : Bool :=
  roots.any (·.isPrefixOf name)

/-- Which imported modules can declare or reach a box constant, indexed like
`moduleNames`. A module reaches the box when it is one of the `declaring` modules
or imports a module that reaches it. A constant
of any other module cannot name a box constant, so the walk never opens it: the
Lean core and `Init` stay closed. -/
def modulesReachingBox (env : Environment) (declaring : NameSet) : Array Bool := Id.run do
  let names := env.header.moduleNames
  let mut index : Std.HashMap Name Nat := {}
  let mut reaches : Array Bool := Array.replicate names.size false
  for h : i in [0:names.size] do
    let name := names[i]
    index := index.insert name i
    let data := env.header.moduleData[i]!
    -- `moduleNames` lists a module after its imports, so every import's answer
    -- is already in `reaches`.
    let viaImport := data.imports.any fun imp =>
      match index.get? imp.module with
      | some j => reaches[j]!
      | none => false
    reaches := reaches.set! i (declaring.contains name || viaImport)
  return reaches

/-- The modules that declare a box constant. -/
def boxModules (env : Environment) : NameSet := Id.run do
  let mut modules : NameSet := {}
  for (name, _) in env.constants.map₁.toList do
    if under boxRoots name then
      if let some idx := env.getModuleIdxFor? name then
        modules := modules.insert env.header.moduleNames[idx.toNat]!
  return modules

/-- The module a constant was declared in, if it came from an import. -/
def moduleOfConst (env : Environment) (name : Name) : Option Name :=
  env.getModuleIdxFor? name |>.map fun idx => env.header.moduleNames[idx.toNat]!

/-- The constants `name` depends on in one step: the constants its type and value
name, and its constructors when it is an inductive. -/
def directDeps (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | none => #[]
  | some info =>
    let used : NameSet := info.getUsedConstantsAsSet
    let ctors : List Name := match info with
      | .inductInfo ind => ind.ctors
      | _ => []
    used.toArray ++ ctors.toArray

/-- One failure: the chain of constants from a spec constant to a box constant. -/
structure Violation where
  /-- The chain, spec constant first and box constant last. -/
  chain : Array Name

/-- Walk the dependencies of every spec constant, and return the chains that end
at a box constant. The result is empty exactly when no spec constant depends on
the box.

The walk is one breadth-first search from all spec constants at once. It visits
each constant once and records the constant it came from. A box constant met on
the way closes a chain, and the walk does not open it. Every constant on a chain
to the box sits in a module that reaches the box, so `opens` never cuts a chain
short.

The walk lists one chain for each spec constant at which a chain starts. A spec
constant that reaches the box only through another spec constant, or through a
constant the walk already visited, gets no line of its own. Removing the listed
uses removes the others, and the next run lists any that remain. -/
def findViolations (env : Environment) : Array Violation := Id.run do
  let reaches := modulesReachingBox env (boxModules env)
  let opens (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some idx => reaches[idx.toNat]!
    | none => false
  -- The roots: every spec constant. A spec module always imports what its
  -- constants name, so a root whose module cannot reach the box needs no walk.
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[]
  for (name, _) in env.constants.map₁.toList do
    if let some module := moduleOfConst env name then
      if under specRoots module && opens name then
        parent := parent.insert name name
        queue := queue.push name
  let mut hits : Std.HashMap Name Violation := {}
  let mut i := 0
  while h : i < queue.size do
    let current := queue[i]
    i := i + 1
    for dep in directDeps env current do
      if under boxRoots dep then
        -- Rebuild the chain through the parents, back to the spec constant.
        -- A root is its own parent. Each other constant got its parent when the
        -- walk first queued it, so the parents form a forest, and `queue.size`
        -- steps reach a root.
        let mut chain : Array Name := #[dep, current]
        let mut node := current
        let mut fuel := queue.size
        while fuel > 0 do
          fuel := fuel - 1
          let up := parent.getD node node
          if up == node then break
          chain := chain.push up
          node := up
        let start := chain.back!
        unless hits.contains start do
          hits := hits.insert start { chain := chain.reverse }
      else if !parent.contains dep && opens dep then
        parent := parent.insert dep current
        queue := queue.push dep
  return hits.toArray.map (·.2) |>.qsort fun a b =>
    toString a.chain[0]! < toString b.chain[0]!

/-! ## The entry point -/

/-- Load the spec modules and report the chains that reach the box. -/
def run : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules ← specModules
  -- `findOLean` resolves a module through the search path to the `.olean` the
  -- build would write. A missing file is a source file no library root imports.
  let mut unbuilt : Array Name := #[]
  for module in modules do
    unless ← (← findOLean module).pathExists do
      unbuilt := unbuilt.push module
  unless unbuilt.isEmpty do
    IO.eprintln s!"no-box rule: spec modules with no `.olean` ({unbuilt.size}). \
      Import each from its library root (`EthCLLib.lean`, `EthCLLib/Tests.lean`, \
      `EthCLSpecs.lean`, `EthCLSpecs/Tests.lean`), so the build compiles it and \
      the rule can read it:"
    for module in unbuilt do IO.eprintln s!"  {module}"
    return 1
  let env ← importModules ((modules.push boxModule).map fun m => { module := m }) {}
  -- Without the box in the environment, every walk would pass for the wrong
  -- reason. The explicit import of `boxModule` makes this a renamed-box check.
  if (boxModules env).isEmpty then
    IO.eprintln s!"no-box rule: no constant under {boxRoots} is in the environment. \
      The box moved or was renamed; update `boxRoots` and `boxModule`."
    return 1
  let violations := findViolations env
  if violations.isEmpty then
    IO.println s!"no-box rule: {modules.size} spec modules, no constant depends on \
      the box."
    return 0
  IO.eprintln s!"no-box rule: the CL specs depend on the box \
    (`SizzLean.Cache.SSZ`, `UncachedSSZ`, `TreeBacked`). Each line is one chain, \
    from a spec constant to a box constant. The CL specs hold plain values; see \
    `packages/EthCLSpecs/docs/FRAMEWORK_ARCHITECTURE.md` §5.1."
  for v in violations.extract 0 maxReported do
    IO.eprintln s!"  {" → ".intercalate (v.chain.toList.map toString)}"
  if violations.size > maxReported then
    IO.eprintln s!"  … and {violations.size - maxReported} more."
  return 1

end NoBoxInSpecs

/-- Run the rule. The exit code is the answer: 0 when no spec constant depends on
the box, 1 otherwise. -/
def main (_args : List String) : IO UInt32 := NoBoxInSpecs.run
