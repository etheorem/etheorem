import SizzLean.Cache.Update

/-!
# `SizzLean.Proofs.UncachedBox`: reduction facts for the uncached box

`SSZ.UncachedBox H v` (`Cache/Box.lean`) is the uncached box flavour: no cache, no
invariant, and every `Box` dispatch reduces to the value itself. Proof code that
reasons over plain values builds this one box, reaches it through a wrapper of its
own, and takes the facts here as the reduction behind the wrapper.

Every fact closes by `rfl`. The uncached arm of each `Box` dispatch carries no cache
and no invariant, so `Box.view` and `Box.hashTreeRoot` reduce to the value on an
uncached box.

There is deliberately no `sszUpdate_uncachedBox` lemma. `sszUpdate` is a term elaborator
that expands per path (`Cache/Update.lean`), so no single statement can cover an
arbitrary clause; on `SSZ.UncachedBox H v` each expansion reduces to the record update
on `v` by `rfl`, and `view_uncachedBox` is the `simp` lemma that makes the reads meet the
writes.
-/

set_option autoImplicit false

namespace SizzLean.Proofs

open SizzLean.Cache
open SizzLean.Hasher

/-- The uncached box of `v` views as `v`. The read-side fact: `sszGet
(SSZ.UncachedBox H v) f` expands to `(SSZ.UncachedBox H v).view.f`, and this lemma
reduces it to `v.f`. -/
@[simp] theorem view_uncachedBox {H T : Type} [Hasher H] [SSZRepr T] (v : T) :
    (SSZ.UncachedBox H v).view = v := rfl

/-- Hash-tree root of an uncached box: the root computed from the value, and the input
box handed back unchanged. The cached flavour commits a fresh box here; the uncached
one has no state, so a root read leaves the uncached box of `v` itself. -/
theorem hashTreeRoot_uncachedBox {H T : Type} [Hasher H] [SSZRepr T] (v : T) :
    (SSZ.UncachedBox H v).hashTreeRoot = (SSZ.hashTreeRoot H v, SSZ.UncachedBox H v) := rfl

end SizzLean.Proofs
