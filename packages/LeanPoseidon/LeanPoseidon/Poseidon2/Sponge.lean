import LeanPoseidon.Poseidon2.Permutation

/-!
# `LeanPoseidon.Sponge`: a sponge over arbitrary-length input

`hash` absorbs an arbitrary-length sequence of field elements into the
width-3 state and squeezes one element out.

## Sponge vocabulary (for the Lean-fluent reader)

A *sponge* absorbs input `rate` elements at a time into the state, running
the permutation between absorptions, then *squeezes* output elements out.
*Rate* is how many state slots take input per permutation (here
`t − 1 = 2`); *capacity* (here the 1 remaining slot) is held back and
never directly touched by input, that reserved slot is what gives the
construction its security margin.

## ⚠ Conformance status: convention documented, external KAT pending

Unlike `compress` (whose definition is pinned by `zkhash`'s
`MerkleTreeHash` and KAT-validated), **the sponge construction over
arbitrary input is not pinned by an upstream reference we can test
against**: `zkhash` ships only the permutation and the 2-to-1 `compress`,
and EIP-7864's `bytes → field` / domain-separation encoding is explicitly
undetermined (see `docs/ARCHITECTURE.md` §"Relationship to the rest of the
monorepo"). So this file fixes *a* concrete, documented convention and
checks it for internal consistency against `permute`; a
cross-implementation KAT is deferred until an upstream Poseidon2 sponge
(or EIP-7864) settles the convention. Per the project's
"don't invent ahead of the spec" stance, depend on `compress` for
consensus-relevant work; treat `hash` as a documented reference sponge.

## The convention fixed here

* state width `t = 3`, `rate = 2`, capacity `1`; initial state `[0,0,0]`;
* **padding**: append a single `1`, then `0`s, until the length is a
  multiple of `rate` (a field analogue of `10*` multi-rate padding, it
  keeps inputs differing only by trailing structure distinct);
* **absorb**: for each `rate`-element chunk, *add* the chunk into the
  first `rate` state slots and permute;
* **squeeze**: output the single element at position 0.
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

/-- Sponge rate: `t − 1 = 2` input slots per permutation. -/
def rate : Nat := 2

/-- Pad `input` to a multiple of `rate` by appending `1` then `0`s. -/
def pad (input : Array Bn254Fr) : Array Bn254Fr :=
  let withMark := input.push (Bn254Fr.ofNat 1)
  let r := withMark.size % rate
  let zeros := if r = 0 then 0 else rate - r
  withMark ++ Array.replicate zeros (Bn254Fr.ofNat 0)

/-- Absorb a `rate`-aligned array into the state, permuting after each
chunk. `padded.size` is a multiple of `rate` (the caller pads), so every
`padded[rate·k]!` / `padded[rate·k+1]!` is in bounds. -/
def absorb (st0 : Vector Bn254Fr 3) (padded : Array Bn254Fr) : Vector Bn254Fr 3 :=
  Nat.fold (padded.size / rate) (fun k _ st =>
    permute bn254Params
      (#v[st[0] + padded[rate * k]!, st[1] + padded[rate * k + 1]!, st[2]])) st0

/-- Sponge hash of an arbitrary-length input to a single field element.
Returns a one-element `Array Bn254Fr` (the squeezed state position 0). See the
module docstring for the convention and its conformance status. -/
def hash (input : Array Bn254Fr) : Array Bn254Fr :=
  let final := absorb (#v[Bn254Fr.ofNat 0, Bn254Fr.ofNat 0, Bn254Fr.ofNat 0]) (pad input)
  #[final[0]]

/-! ## Internal-consistency gates

These check the sponge *plumbing* against `permute` under the convention
above, not against an external reference (none is pinned; see the module
docstring). The empty input pads to one chunk `[1, 0]`, so its hash must be
`permute([1,0,0])[0]`. -/

#guard (hash #[Bn254Fr.ofNat 5]).size = 1

#guard hash #[] = #[(permute bn254Params (#v[Bn254Fr.ofNat 1, Bn254Fr.ofNat 0, Bn254Fr.ofNat 0]))[0]]

end LeanPoseidon.Poseidon2
