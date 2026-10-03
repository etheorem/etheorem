/-!
# `LeanRlp.Spec.Error`: byte-level decode failures

`DecodeError` names one reason a byte sequence is not a canonical
RLP item, and each constructor carries the byte offset it fired at.
One reason, one constructor (ARCHITECTURE.md §6):

* `truncated`: the input ends inside a header or a payload.
* `nonCanonicalByte`: `0x81` in front of a byte below `0x80`.
* `nonCanonicalLength`: a leading zero in the length, or the long
  form for a payload of 55 bytes or fewer.
* `listOverrun`: an item crosses the end of its list payload.
* `trailingBytes`: input left over after a whole item (added by
  `decode`, which must consume all of it).
* `tooDeep`: nesting deeper than the decoder's depth bound.
* `outOfFuel`: the fuel ran out. A dead branch for the public entry
  points, which pass fuel certified by the sufficiency lemma
  (ARCHITECTURE.md §2.1).

`EthELLib` maps the canonical rejections to EEST exception names.
LeanRlp knows no EEST name.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

/-- One reason a byte sequence is not a canonical RLP item, with the
byte offset the decoder was at when the reason fired. -/
inductive DecodeError where
  | truncated (offset : Nat)
  | nonCanonicalByte (offset : Nat)
  | nonCanonicalLength (offset : Nat)
  | listOverrun (offset : Nat)
  | trailingBytes (offset : Nat)
  | tooDeep (offset : Nat)
  | outOfFuel (offset : Nat)
  deriving DecidableEq, Repr

/-- Decidable equality on `Except`. Core has no instance for it on
the pinned toolchain. The gates decide `decode … = …` with it.
Scoped to this namespace, so an importer opts in by opening
`LeanRlp.Spec`.
TODO: delete this instance when a toolchain bump adds a core
`DecidableEq (Except ε α)`. -/
scoped instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error e, .error e' =>
    if h : e = e' then .isTrue (by rw [h])
    else .isFalse (fun h' => h (Except.error.inj h'))
  | .ok a, .ok a' =>
    if h : a = a' then .isTrue (by rw [h])
    else .isFalse (fun h' => h (Except.ok.inj h'))
  | .error _, .ok _ => .isFalse (by intro h; cases h)
  | .ok _, .error _ => .isFalse (by intro h; cases h)

end LeanRlp.Spec
