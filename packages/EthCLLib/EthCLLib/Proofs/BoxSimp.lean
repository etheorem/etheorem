import Lean

/-!
# `EthCLLib.Proofs.BoxSimp`: the `box_reduce` simp set

A spec step's record update on the uncached box is a `match` on the box, and the state it
leaves is that update's view. A proof that reads a field of such a state has to expose the
`.uncached` constructor, reduce the `match`, and project the field. The `box_reduce` simp set
gathers the lemmas that do it. The attribute is declared here, alone, because Lean requires a
simp attribute to be declared in a module before any module that tags lemmas with it.
-/

register_simp_attr box_reduce
