import SizzLean.Hasher.Sha256
import SizzLean.Spec.Type
import SizzLean.Spec.Interp
import SizzLean.Spec.Serialize
import SizzLean.Spec.Deserialize
import SizzLean.Spec.HashTreeRoot

/-!
# `ssz_generic_runner`: the SSZ wire-format conformance server

`ssz_generic` is the fork-agnostic half of the upstream `consensus-spec-tests`
SSZ suite. It addresses shapes by string identifier (`uint_64`, `vec_bool_16`,
`bitlist_32`, the test-only `VarTestStruct`, …), not by any consensus container,
so it exercises `SizzLean`'s primitive wire format directly: the `SSZType`
universe and its `serialize` / `deserialize` / `hashTreeRoot`. That is why the
runner lives here in `SizzLean` rather than in a fork's spec library.

A `valid` case must decode, re-serialize to the exact input bytes, and root to
the value in `meta.yaml`. An `invalid` case must fail to decode (or leave trailing
bytes). A shape identifier `SizzLean`'s universe does not model (the EIP-7495 /
7916 / 8016 progressive / stable / compatible forms `Spec/Type.lean` omits) is
reported `todo`, so the harness xfails it rather than failing.

## The wire protocol

The Python harness snappy-decompresses each case to a temp file and sends one
tab-separated request line; the runner reads the file and writes one result line.
This mirrors `EthCLSpecs.PySpecTests.Server` so the two pytest harnesses share a
shape:

```
check   ⇥ shape ⇥ serializedPath ⇥ expectedRootHex
invalid ⇥ shape ⇥ serializedPath
```
Result: `pass|fail ⇥ bucket ⇥ detail`, where `bucket` is `passing` / `bug` /
`todo`. Each request is wrapped in a `try`/`catch`, so a malformed line or an
unreadable file reports `fail ⇥ bug` and the loop continues.
-/

open SizzLean
open SizzLean.Hasher
open SizzLean.Spec

namespace SszGenericRunner

/-- Lowercase hex of a byte buffer (root diagnostics). -/
def toHex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length == 1 then "0" ++ s else s)

/-- One hex digit's value (`0` for a non-digit; the caller controls the input). -/
private def hexDigit (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Parse a `0x`-prefixed (or bare) hex string into a `ByteArray`. -/
private def hexToBytes (s : String) : ByteArray := Id.run do
  let cs0 := s.toList.toArray
  let cs := if s.startsWith "0x" then cs0.extract 2 cs0.size else cs0
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (hexDigit cs[2*i]! * 16 + hexDigit cs[2*i+1]!))
  return out

/-! ### `ssz_generic` shape parsing

The harness sends the shape PREFIX (variant suffix stripped). Supported prefixes,
matching the `consensus-spec-tests` `ssz_generic` layout:

* `bool`
* `uint_<N>` for `N ∈ {8, 16, 32, 64, 128, 256}`
* `vec_<elem>_<size>` where `elem ∈ {bool, uint8, …, uint256}`
* `bitvec_<size>`
* `bitlist_<cap>`
* the test-only container names (`VarTestStruct`, `ComplexTestStruct`, …),
  whose SSZ shapes are hard-coded below from `formats/ssz_generic/containers.md`.
-/

/-- Parse a uintN element identifier (`uint8`, `uint16`, …). -/
private def parseUintElem (s : String) : Option SSZType :=
  match s with
  | "uint8"   => some (.uintN 8)
  | "uint16"  => some (.uintN 16)
  | "uint32"  => some (.uintN 32)
  | "uint64"  => some (.uintN 64)
  | "uint128" => some (.uintN 128)
  | "uint256" => some (.uintN 256)
  | _         => none

/-- Parse a basic-type element identifier (uintN, bool). -/
private def parseElem (s : String) : Option SSZType :=
  if s == "bool" then some .bool else parseUintElem s

private def varTestStructShape : SSZType :=
  .container [.uintN 16, .list (.uintN 16) 1024, .uintN 8]

private def fixedTestStructShape : SSZType :=
  .container [.uintN 8, .uintN 64, .uintN 32]

private def complexTestStructShape : SSZType :=
  .container [
    .uintN 16,
    .list (.uintN 16) 128,
    .uintN 8,
    .list (.uintN 8) 256,
    varTestStructShape,
    .vector fixedTestStructShape 4,
    .vector varTestStructShape 2
  ]

private def bitsStructShape : SSZType :=
  .container [.bitlist 5, .bitvector 2, .bitvector 1, .bitlist 6, .bitvector 8]

/-- Parse a shape prefix into an `SSZType`. `none` ⇒ a form `SizzLean`'s universe
does not model (reported `todo` upstream). -/
def parseShape (s : String) : Option SSZType :=
  if s == "bool" then some .bool
  else if s == "SingleFieldTestStruct" then some (.container [.uintN 8])
  else if s == "SmallTestStruct" then some (.container [.uintN 16, .uintN 16])
  else if s == "FixedTestStruct" then some fixedTestStructShape
  else if s == "VarTestStruct" then some varTestStructShape
  else if s == "ComplexTestStruct" then some complexTestStructShape
  else if s == "BitsStruct" then some bitsStructShape
  else if s.startsWith "uint_" then
    match (s.drop 5).toString.toNat? with
    | some 8 => some (.uintN 8)   | some 16 => some (.uintN 16)
    | some 32 => some (.uintN 32) | some 64 => some (.uintN 64)
    | some 128 => some (.uintN 128) | some 256 => some (.uintN 256)
    | _ => none
  else if s.startsWith "bitvec_" then
    (s.drop 7).toString.toNat?.map .bitvector
  else if s.startsWith "bitlist_" then
    (s.drop 8).toString.toNat?.map .bitlist
  else if s.startsWith "vec_" then
    -- `vec_<elem>_<size>`: split the trailing `_<size>` off, recurse on the elem.
    let parts := (s.drop 4).toString.splitOn "_"
    match parts.reverse with
    | sizeStr :: elemRevParts =>
        match parseElem (String.intercalate "_" elemRevParts.reverse), sizeStr.toNat? with
        | some elemShape, some n => some (.vector elemShape n)
        | _, _ => none
    | _ => none
  else none

/-- A `valid` case: decode, consume all bytes, re-serialize to the exact input,
and root to `expectedRoot`. Any deviation is the runner's bug (a well-formed
vector should round-trip and root). -/
private def runCheck (shape : SSZType) (raw expectedRoot : ByteArray) : Except String Unit :=
  match SSZType.deserialize shape raw with
  | .error e => .error s!"deserialize failed: {repr e}"
  | .ok (v, used) =>
      if used ≠ raw.size then
        .error s!"trailing bytes: consumed {used}/{raw.size}"
      else if SSZType.serialize shape v ≠ raw then
        .error "re-serialize ≠ input"
      else
        let root := Spec.hashTreeRoot (H := Sha256) shape v
        if root ≠ expectedRoot then
          .error s!"root mismatch: got {toHex root}, expected {toHex expectedRoot}"
        else .ok ()

/-- An `invalid` case: deserialization must fail, or leave trailing bytes. -/
private def runInvalid (shape : SSZType) (raw : ByteArray) : Except String Unit :=
  match SSZType.deserialize shape raw with
  | .error _ => .ok ()
  | .ok (_, used) =>
      if used ≠ raw.size then .ok ()
      else .error "expected deserialize to fail, but it succeeded"

/-- Render an `Except String Unit` outcome as the `pass|fail ⇥ bucket ⇥ detail`
result line. -/
private def render : Except String Unit → String
  | .ok ()    => "pass\tpassing\t"
  | .error d  => s!"fail\tbug\t{d.replace "\t" " " |>.replace "\n" " "}"

/-- Process one request line into a result line. An unknown shape is `todo`
(out of `SizzLean`'s universe); a missing file / malformed line is a `bug`. -/
def handleLine (line : String) : IO String := do
  try
    let fields := (line.splitOn "\t").toArray
    match fields[0]? with
    | some "check" =>
      match parseShape fields[1]! with
      | none       => return s!"fail\ttodo\tshape not in SizzLean's universe: {fields[1]!}"
      | some shape =>
        let raw ← IO.FS.readBinFile fields[2]!
        return render (runCheck shape raw (hexToBytes fields[3]!))
    | some "invalid" =>
      match parseShape fields[1]! with
      | none       => return s!"fail\ttodo\tshape not in SizzLean's universe: {fields[1]!}"
      | some shape =>
        let raw ← IO.FS.readBinFile fields[2]!
        return render (runInvalid shape raw)
    | other => return s!"fail\tbug\tunknown request: {other.getD "<empty>"}"
  catch e =>
    return s!"fail\tbug\t{(toString e).replace "\t" " " |>.replace "\n" " "}"

/-- The request/result loop: read a line, emit a result, flush, repeat; the empty
line / EOF ends it. -/
partial def serve : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO UInt32 := do
    let line := ((← stdin.getLine).dropEndWhile (fun c => c == '\n' || c == '\r')).toString
    if line.isEmpty then return 0
    stdout.putStrLn (← handleLine line)
    stdout.flush
    loop
  loop

end SszGenericRunner

/-- `ssz_generic_runner`: read tab-separated requests on stdin, write one result
line each, until EOF. The SizzLean half of the upstream SSZ conformance suite. -/
def main (_args : List String) : IO UInt32 :=
  SszGenericRunner.serve
