/-!
# `EthCLLib.TheoremVectors.Yaml`: the client-facing YAML writer

The writer for the two YAML files a consumer reads (`ARCHITECTURE.md`
§12.3): a pyspec case's `meta.yaml` (§13.4) and the function format (§13.3).
`meta.yaml` goes out as one flow line, the form the cached upstream corpus
writes, and the function format goes out in block style per §13.3. The
writer has no reader, because the generator never reads a YAML file. The
generator's own files (records, outcomes, hints) are JSON through
`Lean.Json` and need no format code.

The grammar:

- a document is a mapping from plain keys to values, one entry per line,
  or, through `renderFlowDoc`, one flow map on a single line, the form the
  upstream corpus writes `meta.yaml` in;
- a value is a leaf (`bool`, `int`, `str`, `hex`, `raw`), a list, or a
  nested map;
- a map directly under a top-level key renders as a block, one indent
  step deeper; a map two keys deep renders inline as `{ … }`, the
  function format's `inputs:` entries;
- a list renders one `- ` item per line, the first entry of a map item on
  its dash line, or empty inline as `[]`;
- a list adds indentation but no map depth, so a map under a list under a
  top-level key still renders as a block;
- `hex` is a byte string written single-quoted, `'0x…'` with two
  lowercase hex digits per byte, the form the upstream `roots.yaml` writes
  and the one that keeps a consumer's parser from reading a root as an
  integer;
- `raw` is a leaf the caller already shaped, such as a scalar's `int`
  or `bool` in literal form from a record, and the writer emits it
  verbatim;
- a string renders plain when no consumer's YAML parser would coerce it
  to another type, and double-quoted with `\"`, `\\`, `\n`, `\t`, `\r`,
  and `\uXXXX` escapes otherwise.

A later format that needs `steps.yaml` or `roots.yaml` adds one shape
here. The writer picks flow by depth; the upstream dumper picks it by leaf
content, so a format that needs byte-for-byte agreement with the corpus
re-derives its shape here.

## Lean idioms annotated

- The writer is `partial`. It recurses over a value's children through
  `Array.toList`, and structural recursion cannot see a subterm behind
  that conversion, so termination by structure cannot be stated. The
  recursion always advances over the value tree, which is the same shape
  Lean's own `Json` printer takes (`Lean.Json.render` is `partial` too).
- `renderEntryAt` separates the line indent from the child indent, so a
  dash-item entry and a plain entry share one body: `renderItem` passes
  the dash prefix as the line indent and the alignment column as the
  child indent.
-/

set_option autoImplicit false

namespace EthCLLib.TheoremVectors

/-- One YAML value in the writer's grammar (`ARCHITECTURE.md` §12.3). -/
inductive Yaml where
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- A decimal integer with an optional leading `-`. -/
  | int (n : Int)
  /-- A string, plain or double-quoted. -/
  | str (s : String)
  /-- A byte string, written single-quoted, `'0x…'`, with two lowercase
  hex digits per byte. -/
  | hex (bytes : ByteArray)
  /-- A leaf emitted verbatim: a scalar literal the caller already
  shaped, with no newline and no indicator, so the quoting rules leave it
  alone. The record layer guarantees the shape when it decides raw versus
  quoted. -/
  | raw (text : String)
  /-- A list: empty inline as `[]`, otherwise one `- ` item per line. -/
  | list (items : Array Yaml)
  /-- A mapping from plain keys to values, order preserved. -/
  | map (entries : Array (String × Yaml))
  deriving BEq, Inhabited

/-! ## Leaf rendering -/

/-- The lowercase hex digit for `d`, with `d` below 16. -/
private def hexDigit (d : Nat) : Char :=
  match d with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e'
  | _ => 'f'

/-- A byte string as the formats write a Merkle root: `0x` and two
lowercase hex digits per byte, single-quoted. A plain `0x…` reads back as
an integer in a consumer's parser, and the upstream `roots.yaml` quotes
the same way. -/
def Yaml.renderHex (bytes : ByteArray) : String :=
  "'" ++ "0x" ++ bytes.foldl (fun acc b =>
    (acc.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) "" ++ "'"

/-- Whether a character must go out as a `\u` escape: a C0 control, DEL,
a C1 control, or one of the line breaks YAML folds (NEL, LINE SEPARATOR,
PARAGRAPH SEPARATOR). -/
private def needsEscape (c : Char) : Bool :=
  let n := c.toNat
  n < 32 || n == 127 || (n ≥ 128 && n ≤ 159)
  || c == '\u2028' || c == '\u2029'

/-- The body of a double-quoted string, escapes applied. -/
private def escapeChars : List Char → List Char
  | [] => []
  | '"' :: rest => '\\' :: '"' :: escapeChars rest
  | '\\' :: rest => '\\' :: '\\' :: escapeChars rest
  | '\n' :: rest => '\\' :: 'n' :: escapeChars rest
  | '\t' :: rest => '\\' :: 't' :: escapeChars rest
  | '\r' :: rest => '\\' :: 'r' :: escapeChars rest
  | c :: rest =>
    if needsEscape c then
      let n := c.toNat
      '\\' :: 'u' ::
        hexDigit (n / 4096 % 16) :: hexDigit (n / 256 % 16) ::
          hexDigit (n / 16 % 16) :: hexDigit (n % 16) :: escapeChars rest
    else c :: escapeChars rest

/-- A character a plain scalar may carry: letters, digits, and the
punctuation a theorem name, a path, or a phrase with spaces needs. -/
private def plainChar (c : Char) : Bool :=
  c.isAlphanum || c == '.' || c == '_' || c == '-' || c == '/' || c == ' '

/-- Whether the characters open a `- ` list item. -/
private def isDash (cs : List Char) : Bool :=
  match cs with
  | '-' :: ' ' :: _ => true
  | _ => false

/-- Whether the characters are a word a consumer's parser coerces to a
bool or the null value: the YAML 1.1 set (`y`, `yes`, `on`, and their
negations, any casing) plus YAML 1.2's `true`, `false`, `null`, `~`, and
the `.inf` / `.nan` floats. -/
private def coercibleWord (cs : List Char) : Bool :=
  coercibleWords.contains (cs.map (·.toLower))
where
  coercibleWords : List (List Char) :=
    ["y".toList, "n".toList, "yes".toList, "no".toList, "on".toList,
     "off".toList, "true".toList, "false".toList, "null".toList, ['~'],
     ".inf".toList, "-.inf".toList, ".nan".toList]

/-- Whether the characters take an integer shape: an optional `-` and
digits. A `+` never reaches the shape checks, because the plain-character
set quotes it first. -/
private def intShape (cs : List Char) : Bool :=
  match cs with
  | '-' :: rest => digits rest
  | _ => digits cs
where
  digits (ds : List Char) : Bool := !ds.isEmpty && ds.all (·.isDigit)

/-- Whether the characters take a radix shape: `0o17` or `0b101`. -/
private def radixShape (cs : List Char) : Bool :=
  match cs with
  | '0' :: 'o' :: rest => !rest.isEmpty && rest.all (·.isDigit)
  | '0' :: 'b' :: rest => !rest.isEmpty && rest.all (fun c => c == '0' || c == '1')
  | _ => false

/-- The characters before and after the first dot. -/
private def splitDot (cs : List Char) : Option (List Char × List Char) :=
  go [] cs
where
  go (pre : List Char) : List Char → Option (List Char × List Char)
    | [] => none
    | '.' :: rest => some (pre.reverse, rest)
    | c :: rest => go (c :: pre) rest

/-- Whether the characters take a decimal-fraction shape, either side of
the dot possibly empty: `4.25`, `1.`, `.5`. -/
private def fracShape (cs : List Char) : Bool :=
  match splitDot cs with
  | some (w, f) => w.all (·.isDigit) && f.all (·.isDigit) && (!w.isEmpty || !f.isEmpty)
  | none => false

/-- One leading `-`, dropped. -/
private def stripSign (cs : List Char) : List Char :=
  match cs with
  | '-' :: rest => rest
  | _ => cs

/-- Whether a plain string would take a hex shape in a consumer's
parser. -/
private def hexShape (cs : List Char) : Bool :=
  match cs with
  | '0' :: 'x' :: rest =>
    !rest.isEmpty && rest.all fun c => c.isDigit || "abcdefABCDEF".toList.contains c
  | _ => false

/-- Whether the characters take a scientific shape: a mantissa, an `e`
or `E`, and an optionally signed exponent, as in `1e3` or `1.5E-2`. The
mantissa may carry a sign. -/
private def sciShape (cs : List Char) : Bool :=
  go [] cs
where
  go (pre : List Char) : List Char → Bool
    | [] => false
    | c :: rest =>
      if c == 'e' || c == 'E' then
        let mantissa := stripSign pre.reverse
        (intShape mantissa || fracShape mantissa) && expShape rest
      else go (c :: pre) rest
  expShape (es : List Char) : Bool :=
    match es with
    | '-' :: rest => digitsOnly rest
    | _ => digitsOnly es
  digitsOnly (ds : List Char) : Bool := !ds.isEmpty && ds.all (·.isDigit)

/-- Whether the characters start a timestamp shape, `2001-12-14`, which a
consumer's parser coerces to a date. -/
private def dateShape (cs : List Char) : Bool :=
  match cs with
  | a :: b :: c :: d :: '-' :: e :: f :: '-' :: g :: h :: _ =>
    [a, b, c, d, e, f, g, h].all (·.isDigit)
  | _ => false

/-- Whether a plain string would take a numeric shape in a consumer's
parser: a coercible word, an integer, a radix form, a decimal fraction, a
scientific form, a timestamp, a hex form, or any of the numeric ones with
`_` digit separators. Each shape checks its own sign where it has one. -/
private def numShape (cs : List Char) : Bool :=
  let plain := cs.filter (· != '_')
  coercibleWord plain
  || intShape plain
  || radixShape (stripSign plain)
  || fracShape (stripSign plain)
  || sciShape plain
  || dateShape plain
  || hexShape (stripSign plain)

/-- Whether a string needs double quotes: when a plain rendering would
read back as another type in a consumer's parser, carry a YAML indicator,
or lose its edge spaces. The plain-character set already rejects the
indicators `:`, `#`, and `+`, so the shape checks never see them. -/
def Yaml.needsQuote (s : String) : Bool :=
  let cs := s.toList
  cs.isEmpty
  || cs.head? == some ' ' || cs.getLast? == some ' '
  || cs.any fun c => !plainChar c
  || numShape cs
  || cs == ['-'] || isDash cs
  || cs == ['-','-','-'] || cs == ['.','.','.']

/-- A string as it appears in a document: plain when safe, double-quoted
with escapes otherwise. -/
def Yaml.renderStr (s : String) : String :=
  if Yaml.needsQuote s then "\"" ++ String.ofList (escapeChars s.toList) ++ "\"" else s

/-! ## Document rendering -/

mutual
/-- Flow style, the unpadded form the upstream corpus writes:
`{bls_setting: 1}`, `{k: v, …}` for a map, `[ … ]` for a list, the leaf
itself otherwise. -/
private partial def renderFlow : Yaml → String
  | .bool b => if b then "true" else "false"
  | .int n => toString n
  | .str s => Yaml.renderStr s
  | .hex bs => Yaml.renderHex bs
  | .raw t => t
  | .map es =>
    match es.toList with
    | [] => "{}"
    | es' => "{" ++ flowEntries es' ++ "}"
  | .list items =>
    match items.toList with
    | [] => "[]"
    | items' => "[" ++ flowItems items' ++ "]"

private partial def flowEntries : List (String × Yaml) → String
  | [] => ""
  | (k, v) :: rest =>
    let restS := flowEntries rest
    Yaml.renderStr k ++ ": " ++ renderFlow v ++
      (if restS.isEmpty then "" else ", " ++ restS)

private partial def flowItems : List Yaml → String
  | [] => ""
  | item :: rest =>
    let restS := flowItems rest
    renderFlow item ++ (if restS.isEmpty then "" else ", " ++ restS)

/-- One entry per line: `lineInd` prefixes the entry's own line, and
`childInd` prefixes every line its value contributes. -/
private partial def renderEntries (lineInd childInd : String) (depth : Nat) :
    List (String × Yaml) → String
  | [] => ""
  | (k, v) :: rest =>
    renderEntryAt lineInd childInd k v depth ++ renderEntries lineInd childInd depth rest

/-- One `- ` item per line. `ind` is the dash column and `childInd` the
alignment column of the item's entries, two spaces past the dash. -/
private partial def renderItems (ind childInd : String) (depth : Nat) :
    List Yaml → String
  | [] => ""
  | item :: rest => renderItem ind childInd item depth ++ renderItems ind childInd depth rest

/-- The body of one entry, with the line indent and the child indent
given separately. -/
private partial def renderEntryAt (lineInd childInd : String) (k : String)
    (v : Yaml) (depth : Nat) : String :=
  let k := Yaml.renderStr k
  match v with
  | .map es =>
    match es.toList with
    | [] => lineInd ++ k ++ ": {}\n"
    | _ =>
      if depth < 2 then
        lineInd ++ k ++ ":\n" ++ renderEntries childInd (childInd ++ "  ") (depth + 1) es.toList
      else
        lineInd ++ k ++ ": " ++ renderFlow v ++ "\n"
  | .list #[] => lineInd ++ k ++ ": []\n"
  | .list items =>
    -- a list adds indentation but no block-map depth
    lineInd ++ k ++ ":\n" ++ renderItems childInd (childInd ++ "  ") depth items.toList
  | leaf => lineInd ++ k ++ ": " ++ renderFlow leaf ++ "\n"

/-- One `- ` list item: a scalar, or a mapping whose first entry sits on
the dash line and whose remaining entries align on `childInd`. -/
private partial def renderItem (ind childInd : String) (item : Yaml)
    (depth : Nat) : String :=
  match item with
  | .map es =>
    match es.toList with
    | [] => ind ++ "- {}\n"
    | (k, v) :: rest =>
      renderEntryAt (ind ++ "- ") (childInd ++ "  ") k v depth ++
        renderEntries childInd (childInd ++ "  ") depth rest
  | .list #[] => ind ++ "- []\n"
  | .list items =>
    ind ++ "-\n" ++ renderItems childInd (childInd ++ "  ") depth items.toList
  | leaf => ind ++ "- " ++ renderFlow leaf ++ "\n"
end

/-- The whole document as one flow map with a trailing newline, the
form the upstream vectors write `meta.yaml` in (`{bls_setting: 1}` in the
cached corpus). -/
def Yaml.renderFlowDoc (v : Yaml) : String :=
  renderFlow v ++ "\n"

/-- The document text for `v`: one newline-terminated line per entry,
with no trailing blank line. An empty map or list renders inline, since an
empty document reads back as null. -/
def Yaml.render (v : Yaml) : String :=
  match v with
  | .map #[] => "{}\n"
  | .list #[] => "[]\n"
  | .map es => renderEntries "" "  " 1 es.toList
  | .list items => renderItems "" "  " 1 items.toList
  | leaf => renderFlow leaf ++ "\n"

/-! ## Pins -/

/-- The `meta.yaml` of a pyspec case (`ARCHITECTURE.md` §13.4), the two
keys the format writes, in the upstream flow form. -/
private def metaDoc : Yaml :=
  .map #[
    ("bls_setting", .int 2),
    ("theorem", .str "EthCLSpecs.Proofs.Gloas.processBuilderPendingPayments_run")
  ]

/-- One function-format file (`ARCHITECTURE.md` §13.3): flat scalars, the
inputs map with an SSZ value and its root inline, and the output literal. -/
private def functionDoc : Yaml :=
  .map #[
    ("theorem", .str "EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff"),
    ("function", .str "EthCLSpecs.Gloas.canBuilderCoverBid"),
    ("fork", .str "gloas"),
    ("preset", .str "minimal"),
    ("shape", .str "iffTrue"),
    ("inputs", .map #[
      ("state", .map #[("ssz", .hex (ByteArray.mk #[0x00, 0x11, 0x22, 0x33])),
                       ("root", .hex (ByteArray.mk #[0xab, 0xcd, 0xef, 0x01]))]),
      ("builderIndex", .int 3),
      ("bidAmount", .int 32000000000)]),
    ("output", .bool true),
    ("source", .str "random")
  ]

/-- A `steps`-shaped list of maps, the layout a later format writes
(`ARCHITECTURE.md` §12.3): a map value under a dash-item entry, a list
value under another, and a sibling entry after both. -/
private def stepsDoc : Yaml :=
  .map #[
    ("steps", .list #[
      .map #[("checks", .map #[("head", .int 1)])],
      .map #[("blocks", .list #[.str "a"]), ("after", .int 2)]
    ])
  ]

-- meta.yaml, byte for byte in the upstream flow form
#guard Yaml.renderFlowDoc metaDoc ==
  "{bls_setting: 2, theorem: EthCLSpecs.Proofs.Gloas.processBuilderPendingPayments_run}\n"

-- the function format, with the value-and-root pair inline and the
-- scalars plain
#guard Yaml.render functionDoc ==
  "theorem: EthCLSpecs.Proofs.Gloas.canBuilderCoverBid_iff\n" ++
  "function: EthCLSpecs.Gloas.canBuilderCoverBid\n" ++
  "fork: gloas\n" ++
  "preset: minimal\n" ++
  "shape: iffTrue\n" ++
  "inputs:\n" ++
  "  state: {ssz: '0x00112233', root: '0xabcdef01'}\n" ++
  "  builderIndex: 3\n" ++
  "  bidAmount: 32000000000\n" ++
  "output: true\n" ++
  "source: random\n"

-- the steps shape: dash lines carry no dash on their children
#guard Yaml.render stepsDoc ==
  "steps:\n" ++
  "  - checks:\n" ++
  "      head: 1\n" ++
  "  - blocks:\n" ++
  "      - a\n" ++
  "    after: 2\n"

-- a string a plain rendering would let a consumer coerce goes out quoted
#guard !Yaml.needsQuote "gloas"
#guard Yaml.needsQuote ""
#guard Yaml.needsQuote "a: b"
#guard Yaml.needsQuote "0x1a"
#guard Yaml.needsQuote "0x1_a"
#guard Yaml.needsQuote "true"
#guard Yaml.needsQuote "True"
#guard Yaml.needsQuote "y"
#guard Yaml.needsQuote "Off"
#guard Yaml.needsQuote "4.1"
#guard Yaml.needsQuote "-1.0"
#guard Yaml.needsQuote "+4.25"
#guard Yaml.needsQuote "1."
#guard Yaml.needsQuote ".5"
#guard Yaml.needsQuote "1e3"
#guard Yaml.needsQuote "-1.5e-2"
#guard Yaml.needsQuote "1_000"
#guard Yaml.needsQuote "0o17"
#guard Yaml.needsQuote "0b101"
#guard Yaml.needsQuote "-0x1a"
#guard Yaml.needsQuote ".inf"
#guard Yaml.needsQuote "2001-12-14"
#guard Yaml.needsQuote "- leading"

-- a key goes through the quoting rules too, since a consumer coerces
-- boolean-looking keys
#guard Yaml.render (.map #[("n", .int 1)]) == "\"n\": 1\n"

-- an empty document renders inline, since an empty file reads as null
#guard Yaml.render (.map #[]) == "{}\n"
#guard Yaml.render (.list #[]) == "[]\n"
#guard Yaml.render (.list #[.list #[]]) == "- []\n"

-- a control character escapes as \u, and a document marker quotes
#guard Yaml.renderStr "\x01" == "\"\\u0001\""
#guard Yaml.renderStr "\x7f" == "\"\\u007f\""
#guard Yaml.needsQuote "---"
#guard Yaml.needsQuote "..."

end EthCLLib.TheoremVectors
