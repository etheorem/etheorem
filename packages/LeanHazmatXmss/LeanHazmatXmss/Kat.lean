/-!
# `LeanHazmatXmss.Kat`: KAT-support hashing

A single `@[extern]` binding to the SHAKE128 already compiled into the
xmss-reference archive (`fips202.c`). The test suite uses it to reproduce the
`shake128(·, 10)` digests that xmss-reference's own `test/vectors.c` prints, so
the committed anchors are cross-checked against upstream's reference vectors
rather than only against this shim's own extraction.

This is **not** part of the XMSS signature surface. It lives in its own module,
and `LeanHazmatXmss.lean` does not re-export it, so `import LeanHazmatXmss` never
brings SHAKE into scope; only the tests `import LeanHazmatXmss.Kat`. It must sit
in the precompiled library (not the test module) so `native_decide` can resolve
the native symbol.
-/

set_option autoImplicit false

namespace LeanHazmat.Xmss.Kat

/-- `shake128 data outLen` returns the first `outLen` bytes of SHAKE128 over
`data`. KAT support only (see the module docstring).

Runtime: `csrc/xmss_shim.c`'s `lean_hazmat_xmss_shake128`, wrapping the
vendored `fips202.c`. -/
@[extern "lean_hazmat_xmss_shake128"]
opaque shake128 (data : @& ByteArray) (outLen : USize) : ByteArray

end LeanHazmat.Xmss.Kat
