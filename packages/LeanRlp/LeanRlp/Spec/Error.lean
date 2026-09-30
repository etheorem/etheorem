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

Filled in PLAN.md Stage 1.
-/

set_option autoImplicit false

namespace LeanRlp.Spec

end LeanRlp.Spec
