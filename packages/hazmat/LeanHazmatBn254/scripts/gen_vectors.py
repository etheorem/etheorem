#!/usr/bin/env python3
"""Cross-check the committed BN254 KAT vectors against py_ecc.

The vectors in `LeanHazmatBn254Tests/Vectors.lean` were generated from
ethereum/py_ecc, the reference implementation EIP-197 itself links.
This script is that provenance, kept runnable: it recomputes every
committed anchor with py_ecc and asserts the bytes match. It writes
nothing; a mismatch exits nonzero, so running it is a gate:

    python3 packages/hazmat/LeanHazmatBn254/scripts/gen_vectors.py

py_ecc is a test-only dependency (not in the repo's requirements.txt):

    uv venv && uv pip install py_ecc
    .venv/bin/python packages/hazmat/LeanHazmatBn254/scripts/gen_vectors.py

Encodings, pinned by the EIPs and mirrored by the C shim:

* G1: 64 bytes, affine `x ‖ y`, big-endian; the point at infinity is
  all zeros.
* G2: 128 bytes; coordinate `a*i + b` encodes as `(a, b)`, the
  imaginary half first. py_ecc's `FQ2([c0, c1])` is `b + a*i`, real
  first, so the halves swap here.
* The off-curve-rejection anchor: an on-curve G2 point OUTSIDE the
  order-`q` subgroup, derived from its committed `x` by square root in
  F_p2 (`p = 3 mod 4`, so `y = a^((p^2+1)/4)`). The script re-derives
  it and asserts both properties the shim's rejection depends on:
  on-curve, and `q * P != infinity`.

py_ecc is pure Python and slow: expect ~1 min for the full run.
"""

import sys

from py_ecc.bn128 import (
    FQ12,
    FQ2,
    G1,
    G2,
    add,
    curve_order,
    final_exponentiate,
    is_on_curve,
    multiply,
    pairing,
)

# py_ecc's bn128 points are affine 2-tuples; the point at infinity is
# `None`. G1 IS (1, 2), the EIP-196 generator.
P1 = G1


def g1_hex(p):
    x, y = p
    return f"{int(x):064x}{int(y):064x}"


def fq2_eip(c):
    """EIP-197 encoding of an FQ2 coordinate `c0 + c1*i`: imag first."""
    return f"{int(c.coeffs[1]):064x}{int(c.coeffs[0]):064x}"


def g2_hex(p):
    x, y = p
    return fq2_eip(x) + fq2_eip(y)


# The committed values, verbatim from LeanHazmatBn254Tests/Vectors.lean.
COMMITTED = {
    "g1_2P1": ("030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd3"
               "15ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4"),
    "g1_3P1": ("0769bf9ac56bea3ff40232bcb1b6bd159315d84715b8e679f2d355961915abf0"
               "2ab799bee0489429554fdb7c8d086475319e63b40b9c5b57cdf1ff3dd9fe2261"),
    "g1_5P1": ("17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa9"
               "01e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c"),
    "g1_neg": ("0000000000000000000000000000000000000000000000000000000000000001"
               "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45"),
    "g2_2P2": ("203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad79"
               "27dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9"
               "195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de152"
               "04bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e"),
    "g2_3P2": ("1014772f57bb9742735191cd5dcfe4ebbc04156b6878a0a7c9824f32ffb66e85"
               "06064e784db10e9051e52826e192715e8d7e478cb09a5e0012defa0694fbc7f5"
               "021e2335f3354bb7922ffcc2f38d3323dd9453ac49b55441452aeaca147711b2"
               "058e1d5681b5b9e0074b0f9c8d2c68a069b920d74521e79765036d57666c5597"),
    "g2_5P2": ("0a09ccf561b55fd99d1c1208dee1162457b57ac5af3759d50671e510e428b2a1"
               "2e539c423b302d13f4e5773c603948eaf5db5df8ae8a9a9113708390a06410d8"
               "19b763513924a736e4eebd0d78c91c1bc1d657fee4214057d21414011cfcc763"
               "2f8d9f9ab83727c77a2fec063cb7b6e5eb23044ccf535ad49d46d394fb6f6bf6"),
    "g2_qminus2": ("203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad79"
                   "27dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9"
                   "1705c3cd29af2bc64624b9a1485000c0627c1426199281b8a33f062687df1bf5"
                   "2ba8faba49b3409717940e8f3ebcd55452dbcf4181c00a46cdf61e69c651a019"),
    "g2_4P2": ("290668479e567ad5a2485a93f976d784206f66f690a18c3f5a6d85c29571236f"
               "29dddbf86f6a2f47c38063a850ccc442131570e5084c45fd7709b4ddb436e22c"
               "1e74a4bf519c267a5b16431b2413b00402d4d3b670c9414b8efff5bee661a8f6"
               "299f0af7f72b3a93ca7c3cc32443c83b05d041bd14276e5adca2546728bc37f7"),
    "g2_nonsubgroup": ("0000000000000000000000000000000000000000000000000000000000000003"
                       "0000000000000000000000000000000000000000000000000000000000000002"
                       "1b3983aba87e776f3bce1885442ec3e9c6ad7f6f05321c57eebe5dcf0c2e7f32"
                       "0239d6264efb1d130c43464ef93b83508adf1cf49b9571dc36dbbaa2a17dc655"),
}


def check(name, got, want):
    if got != want:
        sys.exit(f"{name}: got {got}, want {want}")
    print(f"  ok  {name}")


def main():
    # Sanity: the committed generator encodings match py_ecc's G1 / G2.
    check("g1_P1", g1_hex(P1),
          "0000000000000000000000000000000000000000000000000000000000000001"
          "0000000000000000000000000000000000000000000000000000000000000002")
    check("g2_P2", g2_hex(G2),
          "198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2"
          "1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed"
          "090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b"
          "12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa")

    # G1 arithmetic anchors.
    check("g1_2P1", g1_hex(multiply(P1, 2)), COMMITTED["g1_2P1"])
    check("g1_3P1", g1_hex(add(multiply(P1, 2), P1)), COMMITTED["g1_3P1"])
    check("g1_5P1", g1_hex(multiply(P1, 5)), COMMITTED["g1_5P1"])
    check("g1_neg", g1_hex(multiply(P1, curve_order - 1)), COMMITTED["g1_neg"])

    # G2 arithmetic anchors.
    check("g2_2P2", g2_hex(multiply(G2, 2)), COMMITTED["g2_2P2"])
    check("g2_3P2", g2_hex(add(multiply(G2, 2), G2)), COMMITTED["g2_3P2"])
    check("g2_5P2", g2_hex(multiply(G2, 5)), COMMITTED["g2_5P2"])
    check("g2_qminus2", g2_hex(multiply(G2, curve_order - 2)),
          COMMITTED["g2_qminus2"])
    check("g2_4P2", g2_hex(multiply(G2, 4)), COMMITTED["g2_4P2"])

    # Pairing-check anchors: the product vanishes exactly when the
    # discrete-log sum does (2*3 + 3*(q-2) = 3q = 0, vs 2*3 + 3*4 = 18).
    p2 = {n: multiply(G2, n) for n in (2, 3, 4, curve_order - 2)}
    p1 = {n: multiply(P1, n) for n in (2, 3)}
    true_prod = pairing(p2[3], p1[2]) * pairing(p2[curve_order - 2], p1[3])
    if final_exponentiate(true_prod) != FQ12.one():
        sys.exit("true pairing check: product did not reduce to one")
    print("  ok  pairing true (2*3 + 3*(q-2) == 0 mod q)")
    false_prod = pairing(p2[3], p1[2]) * pairing(p2[4], p1[3])
    if final_exponentiate(false_prod) == FQ12.one():
        sys.exit("false pairing check: product unexpectedly one")
    print("  ok  pairing false (2*3 + 3*4 != 0 mod q)")

    # The infinity anchor: q * P1 is the point at infinity (`None`).
    if multiply(P1, curve_order) is not None:
        sys.exit("q * P1 is not the infinity point")
    print("  ok  infinity (q * P1 == point at infinity)")

    # The non-subgroup G2 anchor: re-derive y from the committed x by
    # square root in F_p2, then assert on-curve and q*P != infinity.
    raw = bytes.fromhex(COMMITTED["g2_nonsubgroup"])
    x_re, x_im = (int.from_bytes(raw[i:i + 32], "big") for i in (32, 0))
    y_re, y_im = (int.from_bytes(raw[i:i + 32], "big") for i in (96, 64))
    x = FQ2([x_re, x_im])
    y = FQ2([y_re, y_im])
    # EIP-197: y^2 = x^3 + 3/(9+i) over F_p2, the alt_bn128 G2 curve
    # equation (3 is the G1 constant; the G2 one differs).
    b2 = FQ2([3, 0]) / FQ2([9, 1])
    if y * y != x * x * x + b2:
        sys.exit("non-subgroup anchor: committed (x, y) is not on the curve")
    point = (x, y)
    if not is_on_curve(point, b2):
        sys.exit("non-subgroup anchor: py_ecc rejects the point as off-curve")
    if multiply(point, curve_order) is None:
        sys.exit("non-subgroup anchor: the point IS in the order-q subgroup")
    print("  ok  non-subgroup anchor (on curve, outside the order-q subgroup)")

    print("all committed BN254 anchors reproduced with py_ecc")


if __name__ == "__main__":
    main()
