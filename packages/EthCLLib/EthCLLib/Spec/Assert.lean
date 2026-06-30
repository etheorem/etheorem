import Lean
import EthCLLib.Spec.Errors

/-!
# `EthCLLib.Spec.Assert`: the `assert` macro and the `todo` deferral

`assert cond` is the spec-assertion primitive (`SPEC_AUTHORING_MODEL.md` §7). It
renders `cond`'s own source text into the error descriptor and throws the section's
`assert` reject when the condition is false, so the author writes no message and the
failure describes itself. The descriptor is diagnostic only; nothing branches on it (the
harness reads the constructor).

`todo what` is the typed deferral: a branch not yet wired, carrying a documented
unreachable-in-scope claim. A vector that reaches one fails loudly as `todo` rather than
passing silently, the deferral safety net of `FRAMEWORK_ARCHITECTURE.md` §6.1.

Both `assert` and `todo` resolve their reject type from the section's monad through
`SpecReject` (`EthCLLib.Spec.Errors`): the same `assert` / `todo` throw a
`StateTransitionError` in a state section and a `StoreTransitionError` in a fork-choice
section, so a fork-choice handler writes `assert` / `todo`, not a store-specific spelling.
-/

set_option autoImplicit false

open Lean

namespace EthCLLib.Spec

universe u

/-- The typed deferral, throwing the section's `todo` reject (resolved through
`SpecReject` from the monad's error type). A work-queue item the harness reports
as `xfail`; it is expected to pass once the branch is filled. Polymorphic in the
result so it stubs any step or helper. -/
@[inline] def todo {m : Type → Type u} {α E : Type} [MonadExcept E m] [SpecReject E]
    (what : String) : m α :=
  throw (SpecReject.todo what)

/-- The typed out-of-scope reject (resolved through `SpecReject` from the monad's
error type). For a branch we deliberately do not model, a runner or type chosen
not to implement, so the harness reports it as `skip` rather than counting it in
the `xfail` work-queue. Polymorphic in the result, like `todo`. -/
@[inline] def outOfScope {m : Type → Type u} {α E : Type} [MonadExcept E m] [SpecReject E]
    (what : String) : m α :=
  throw (SpecReject.outOfScope what)

/-- Run the nested state machine from a store action: execute `act` (the
specialised `state_transition` / `process_slots` as an `EStateM StateTransitionError
S` action) on `pre`, returning the post-state, or re-throwing the inner failure
wrapped as `StoreTransitionError.transition` (`FRAMEWORK_ARCHITECTURE.md` §6, §7.2).
The store handler binds the result in its own monad `m`. This is the one-way bridge:
the store machine runs the state machine, never the reverse. -/
@[inline] def runStateTransition {S : Type} {m : Type → Type u} [Monad m]
    [MonadExceptOf StoreTransitionError m] (pre : S)
    (act : EStateM StateTransitionError S Unit) : m S :=
  match act.run pre with
  | .ok _ post => pure post
  | .error e _ => throw (ErrorConv.conv e : StoreTransitionError)

/-- Collapse a reprinted condition to a single tab-free line. `reprint` keeps the
trailing trivia after `cond` (whitespace and any following comment), which would
embed newlines / the next line's text in the descriptor and break the
tab-separated `PySpecTests` wire protocol. The descriptor is diagnostic only, so
the first line, trimmed and tab-stripped, is enough. -/
def sanitizeDescr (raw : String) : String :=
  (((raw.splitOn "\n").headD raw).replace "\t" " ").trimAscii.toString

/-- `assert cond` throws the section's `assert` reject (a `StateTransitionError` in a
state section, a `StoreTransitionError` in a fork-choice section, resolved through
`SpecReject` from the monad's error type) carrying `<rendered cond>` as its descriptor
when `cond : Bool` is false, and is a no-op otherwise. The descriptor is `cond`'s
reprinted source, captured at macro-expansion time. Expands to a plain `if`, so it
threads the section's monad with no extra structure.

`scoped`, so `open EthCLLib.Spec` activates it. -/
scoped macro (name := assertStx) "assert " cond:term:max : term => do
  let descr := sanitizeDescr (cond.raw.reprint.getD "assertion")
  let descrLit := Syntax.mkStrLit descr
  `(if $cond then (pure PUnit.unit) else throw (EthCLLib.Spec.SpecReject.assert $descrLit))

/-- `assertH cond` is `assert` that **returns the proof** of its condition. It throws the
section's `assert` reject when `cond` is false, exactly as `assert`; when `cond` holds it binds
the witness, lifted through `PLift` so a proof can ride in the `Type`-valued monad. Bind it
(`let h ← assertH cond`) when a later step needs `cond` as a hypothesis: a spec-validated index
becomes a proof-carrying read `xs[i]'h.down`, whose bound *is* the asserted `i < xs.size`. The
monad reaches the continuation only when the check passed, so `h.down` is a sound witness and
the read carries no reject branch, the bad index already rejected at the `assertH`. Plain
`assert` stays the Unit-returning form for a validation whose proof nothing downstream needs.

`scoped`, so `open EthCLLib.Spec` activates it. -/
scoped macro (name := assertHStx) "assertH " cond:term:max : term => do
  let descr := sanitizeDescr (cond.raw.reprint.getD "assertion")
  let descrLit := Syntax.mkStrLit descr
  `(if h : $cond then pure (PLift.up h) else throw (EthCLLib.Spec.SpecReject.assert $descrLit))

end EthCLLib.Spec
