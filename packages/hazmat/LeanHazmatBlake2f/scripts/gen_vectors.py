#!/usr/bin/env python3
"""Generate and cross-check the nonzero-counter BLAKE2f vectors.

The five published EIP-152 test vectors all use `t0 = 3, t1 = 0`, so a
shim that drops `t1` (or the high bytes of `t0`) still passes them.
`LeanHazmatBlake2fTests/Vectors.lean` therefore pins two extra cases on
the same `h` / `m` block with both counter words nonzero. This script
is the provenance for those two cases:

1. It implements RFC 7693 section 3.2 (`F`, the BLAKE2b compression)
   independently of the C shim.
2. It first checks itself against all five published EIP-152 vectors
   (parameters and expected outputs embedded below, verbatim from the
   EIP text; the 213-byte inputs are built in the EIP layout).
3. Only then does it emit the two nonzero-counter digests and assert
   they equal the values committed in `Vectors.lean`.

Any mismatch exits nonzero, so running the script is a gate:

    python3 packages/hazmat/LeanHazmatBlake2f/scripts/gen_vectors.py

By default the self-check covers the four published vectors with
`rounds < 0xffffffff`; the fifth (4294967295 rounds) is opt-in behind
`--full`, because CPython needs hours for what the compiled shim does
in ~50 s (the Lean KAT gates it against the C shim either way).

Paths resolve relative to this script's location inside the
`LeanHazmatBlake2f` package, so it runs from anywhere. Stdlib only.
"""

import sys

FULL = "--full" in sys.argv[1:]

MASK = 0xFFFFFFFFFFFFFFFF

# RFC 7693 section 2.6: the BLAKE2b IV.
IV = [
    0x6A09E667F3BCC908, 0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
    0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179,
]

# RFC 7693 section 2.7: the ten-round permutation schedule.
SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
]


def rotr(x, n):
    return ((x >> n) | (x << (64 - n))) & MASK


def g(v, a, b, c, d, x, y):
    v[a] = (v[a] + v[b] + x) & MASK
    v[d] = rotr(v[d] ^ v[a], 32)
    v[c] = (v[c] + v[d]) & MASK
    v[b] = rotr(v[b] ^ v[c], 24)
    v[a] = (v[a] + v[b] + y) & MASK
    v[d] = rotr(v[d] ^ v[a], 16)
    v[c] = (v[c] + v[d]) & MASK
    v[b] = rotr(v[b] ^ v[c], 63)


def f(h, m, t0, t1, last, rounds):
    """RFC 7693 section 3.2. h: 8 words, m: 16 words."""
    v = list(h) + list(IV)
    v[12] ^= t0
    v[13] ^= t1
    if last:
        v[14] ^= MASK
    for r in range(rounds):
        s = SIGMA[r % 10]
        g(v, 0, 4, 8, 12, m[s[0]], m[s[1]])
        g(v, 1, 5, 9, 13, m[s[2]], m[s[3]])
        g(v, 2, 6, 10, 14, m[s[4]], m[s[5]])
        g(v, 3, 7, 11, 15, m[s[6]], m[s[7]])
        g(v, 0, 5, 10, 15, m[s[8]], m[s[9]])
        g(v, 1, 6, 11, 12, m[s[10]], m[s[11]])
        g(v, 2, 7, 8, 13, m[s[12]], m[s[13]])
        g(v, 3, 4, 9, 14, m[s[14]], m[s[15]])
    return [h[i] ^ v[i] ^ v[8 + i] for i in range(8)]


# The RFC 7693 appendix-E test block, the `h` and `m` every published
# EIP-152 vector shares: h is the 64-byte chaining value, m is "abc"
# zero-padded to the 128-byte block.
H_BLOCK = bytes.fromhex(
    "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b")
M_BLOCK = bytes.fromhex("616263" + "00" * 125)
assert len(H_BLOCK) == 64 and len(M_BLOCK) == 128

H_WORDS = [int.from_bytes(H_BLOCK[8 * i:8 * i + 8], "little") for i in range(8)]
M_WORDS = [int.from_bytes(M_BLOCK[8 * i:8 * i + 8], "little") for i in range(16)]


def eip152_input(rounds, t0, t1, last):
    """The 213-byte precompile input:
    rounds(4 BE) ‖ h(64) ‖ m(128) ‖ t0(8 LE) ‖ t1(8 LE) ‖ f(1)."""
    return (rounds.to_bytes(4, "big") + H_BLOCK + M_BLOCK
            + t0.to_bytes(8, "little") + t1.to_bytes(8, "little")
            + bytes([1 if last else 0]))


def words_out(out_bytes):
    return [int.from_bytes(out_bytes[8 * i:8 * i + 8], "little") for i in range(8)]


def hex_le_words(words):
    return b"".join(w.to_bytes(8, "little") for w in words).hex()


# The five published EIP-152 vectors: (rounds, t0, t1, last, expected
# 64-byte output), verbatim outputs from the EIP text.
PUBLISHED = [
    (0x00000000, 3, 0, True,
     "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5"
     "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b"),
    (0x0000000c, 3, 0, True,
     "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
     "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"),
    (0x0000000c, 3, 0, False,
     "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752"
     "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735"),
    (0x00000001, 3, 0, True,
     "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb"
     "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421"),
    (0xffffffff, 3, 0, True,
     "fc59093aafa9ab43daae0e914c57635c5402d8e3d2130eb9b3cc181de7f0ecf9"
     "b22bf99a7815ce16419e200e01846e6b5df8cc7703041bbceb571de6631d2615"),
]

# The two nonzero-counter cases committed in
# `LeanHazmatBlake2fTests/Vectors.lean`: the same `h` / `m` block, both
# counter words nonzero, (12 rounds, final flag true) and (1 round,
# final flag false).
T0_NONZERO = 0x1122334455667788
T1_NONZERO = 0x99AABBCCDDEEFF00
COMMITTED = [
    "a4485332b3bed911dc3120d5173d3960e8cf0bd633a1966db0ae508f3635e2e7"
    "9441d136c83f0d15dde62f7f3b57e2d6d41dc9e20d04e85fc004bd93a71ca29e",
    "76df1abdd8ee76fca0705e6216b426f7aaedfef4459e2984151adf57bc634043"
    "541e54c922a65f0e2cb629e49d6ec62fdf38d339eb7bc70c4c37d5d4dbc4f0d7",
]


def main():
    # Step 1: the implementation must reproduce the published vectors
    # before it is trusted for anything else. The 0xffffffff-rounds
    # vector is opt-in (see the module docstring).
    checked = 0
    for i, (rounds, t0, t1, last, want_hex) in enumerate(PUBLISHED):
        if rounds == 0xFFFFFFFF and not FULL:
            continue
        got = hex_le_words(f(H_WORDS, M_WORDS, t0, t1, last, rounds))
        if got != want_hex:
            sys.exit(f"published EIP-152 vector {4 + i}: got {got}, want {want_hex}")
        checked += 1
    print(f"self-check ok: {checked} published EIP-152 vectors reproduced"
          + ("" if FULL else " (the 0xffffffff-rounds vector needs --full)"))

    # Step 2: regenerate the two nonzero-counter cases and assert they
    # match the committed values.
    emitted = [
        hex_le_words(f(H_WORDS, M_WORDS, T0_NONZERO, T1_NONZERO, True, 12)),
        hex_le_words(f(H_WORDS, M_WORDS, T0_NONZERO, T1_NONZERO, False, 1)),
    ]
    for got, want in zip(emitted, COMMITTED):
        if got != want:
            sys.exit(f"committed vector mismatch: got {got}, want {want}")
    print("regenerated nonzero-counter vectors match the committed values")
    for out in emitted:
        print(f'  hex "{out[:64]}" ++\n    "{out[64:]}"')


if __name__ == "__main__":
    main()
