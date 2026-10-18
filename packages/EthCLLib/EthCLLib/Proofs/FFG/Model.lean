/-!
# `EthCLLib.Proofs.FFG.Model`: Casper FFG over two chains

An abstract model of Casper FFG (Buterin and Griffith 2017, "Casper the Friendly Finality
Gadget"), in the form the beacon chain runs it. The model has no slots, no blocks, and no
signatures. It keeps the parts that accountable safety reads:

- a checkpoint, an epoch and a root (`Checkpoint`);
- a vote of one validator, from a source checkpoint to a target checkpoint (`Vote`);
- a chain, with its votes, its stake and total at each epoch, its validators, its checkpoint
  at each epoch, and the checkpoints justified at the start (`Chain`).

A chain is linear. So a checkpoint is on a chain when it is the chain's checkpoint at its
epoch (`Chain.OnChain`). Two chains model the two sides of a fork. Each chain has its own
stake, because each side of a fork runs its own state transition.

## Links, justification, finalization

A supermajority link from `s` to `t` (`Link`) has voters that hold two thirds of the total of
the chain at one epoch `e`. The spec weighs a link in `weigh_justification_and_finalization`.
That step weighs the target of the current epoch and the target of the previous epoch, both
with the total of the current epoch. So `e` is the epoch of `t` or the next epoch.

`Justified` closes the start checkpoints under links. `Finalized` has the two finalization
forms of the spec. In the first, a link joins `b` to a justified checkpoint one epoch later.
In the second, the link skips one epoch, and the checkpoint between is justified. The spec's
four finalization tests are these two forms, each weighed in the current or the previous
epoch.

## The slashing conditions

`DoubleVote` and `SurroundVote` are the two conditions of `is_slashable_attestation_data`
(`EthCLSpecs.Proofs.Heze.isSlashableAttestationData_iff`), on votes. A double vote compares
the two targets here. The spec compares the roots of the two attestation data, which differ
when the targets differ, unless two data share a root.

## The shared history

The two chains share their history up to the fork. `CommonBase` says that the start
checkpoints are on both chains and before the finalized checkpoint. `Agree` says that two
chains with one checkpoint in common agree at every earlier epoch. Two chains of one block
tree meet `Agree`, because a block fixes its ancestors.
-/

set_option autoImplicit false

namespace EthCLLib.Proofs.FFG

/-- A checkpoint: an epoch and a root. -/
structure Checkpoint (R : Type) where
  epoch : Nat
  root : R
deriving DecidableEq

/-- A vote: a validator, a source and a target. -/
structure Vote (V R : Type) where
  val : V
  source : Checkpoint R
  target : Checkpoint R

/-- One chain: its votes, its stake and total at each epoch, its validators, its checkpoint at
each epoch, and the checkpoints justified at the start. -/
structure Chain (V R : Type) where
  votes : List (Vote V R)
  stake : Nat → V → Nat
  total : Nat → Nat
  vals : List V
  cpAt : Nat → Option R
  base : List (Checkpoint R)

variable {V R : Type} [DecidableEq V] [DecidableEq R]

/-- The sum of `w` over a list. -/
def stakeSum (w : V → Nat) (xs : List V) : Nat := (xs.map w).sum

/-- The checkpoint is the chain's checkpoint at its epoch. -/
def Chain.OnChain (c : Chain V R) (x : Checkpoint R) : Prop := c.cpAt x.epoch = some x.root

/-- The validator `v` has a vote from `s` to `t` on the chain. -/
def voted (c : Chain V R) (s t : Checkpoint R) (v : V) : Bool :=
  c.votes.any fun x => decide (x.val = v ∧ x.source = s ∧ x.target = t)

/-- The validators of the chain with a vote from `s` to `t`. -/
def linkVoters (c : Chain V R) (s t : Checkpoint R) : List V :=
  c.vals.filter (voted c s t)

/-- A supermajority link from `s` to `t`, weighed at an epoch `e`: the epoch of `t` or the
next epoch. -/
def Link (c : Chain V R) (s t : Checkpoint R) : Prop :=
  s.epoch < t.epoch ∧ c.OnChain s ∧ c.OnChain t ∧
    ∃ e, t.epoch ≤ e ∧ e ≤ t.epoch + 1 ∧
      3 * stakeSum (c.stake e) (linkVoters c s t) ≥ 2 * c.total e

/-- The justified checkpoints: the start checkpoints, closed under links. -/
inductive Justified (c : Chain V R) : Checkpoint R → Prop
  | base {b : Checkpoint R} : b ∈ c.base → Justified c b
  | link {s t : Checkpoint R} : Justified c s → Link c s t → Justified c t

/-- The finalized checkpoints. In `one`, a link joins `b` to a justified checkpoint one epoch
later. In `two`, the link joins `b` to a justified checkpoint two epochs later, and the
checkpoint `m` between is justified. -/
inductive Finalized (c : Chain V R) : Checkpoint R → Prop
  | one {b t : Checkpoint R} : Justified c b → Justified c t → t.epoch = b.epoch + 1 →
      Link c b t → Finalized c b
  | two {b m t : Checkpoint R} : Justified c b → Justified c m → Justified c t →
      m.epoch = b.epoch + 1 → t.epoch = b.epoch + 2 → Link c b t → Finalized c b

/-- Two votes of one validator for two targets of one epoch. -/
def DoubleVote (x y : Vote V R) : Prop :=
  x.val = y.val ∧ x.target.epoch = y.target.epoch ∧ x.target ≠ y.target

/-- Two votes of one validator, where the first surrounds the second. -/
def SurroundVote (x y : Vote V R) : Prop :=
  x.val = y.val ∧ x.source.epoch < y.source.epoch ∧ y.target.epoch < x.target.epoch

/-- The validator `v` cast a vote `x` of the first list and a vote `y` of the second list that
meet a slashing condition: a double vote, or one vote surrounds the other. -/
def Slashable (votes₁ votes₂ : List (Vote V R)) (v : V) : Prop :=
  ∃ x ∈ votes₁, ∃ y ∈ votes₂, x.val = v ∧ y.val = v ∧
    (DoubleVote x y ∨ SurroundVote x y ∨ SurroundVote y x)

/-- The start checkpoints of the two chains are the same. Each is on both chains, before the
epoch of `b`. -/
def CommonBase (c₁ c₂ : Chain V R) (b : Checkpoint R) : Prop :=
  c₁.base = c₂.base ∧ ∀ x ∈ c₁.base, x.epoch < b.epoch ∧ c₁.OnChain x ∧ c₂.OnChain x

/-- Two chains that hold one checkpoint hold the same checkpoints at every earlier epoch. -/
def Agree (c₁ c₂ : Chain V R) : Prop :=
  ∀ e₁ r, c₁.cpAt e₁ = some r → c₂.cpAt e₁ = some r → ∀ e ≤ e₁, c₁.cpAt e = c₂.cpAt e

/-- A justified checkpoint is on its chain, when the start checkpoints are. -/
theorem Justified.onChain {c : Chain V R} (hb : ∀ x ∈ c.base, c.OnChain x) {x : Checkpoint R}
    (h : Justified c x) : c.OnChain x := by
  cases h with
  | base hx => exact hb _ hx
  | link _ hl => exact hl.2.2.1

/-- A justified checkpoint after every start checkpoint came from a link. -/
theorem Justified.link_of_not_base {c : Chain V R} {x : Checkpoint R} (h : Justified c x)
    (hx : x ∉ c.base) : ∃ s, Justified c s ∧ Link c s x := by
  cases h with
  | base hb => exact absurd hb hx
  | link hs hl => exact ⟨_, hs, hl⟩

omit [DecidableEq V] [DecidableEq R] in
/-- Under `Agree`, a checkpoint on both chains at or after the epoch of `b` puts `b` on both
chains. So when `b` is on chain 1 only, a checkpoint `x` of chain 1 and a checkpoint `y` of
chain 2, at one epoch at or after `b`, differ. -/
theorem ne_of_agree {c₁ c₂ : Chain V R} (hagree : Agree c₁ c₂) {b x y : Checkpoint R}
    (hb₁ : c₁.OnChain b) (hb₂ : ¬ c₂.OnChain b) (hx : c₁.OnChain x) (hy : c₂.OnChain y)
    (hep : b.epoch ≤ x.epoch) : x ≠ y := by
  rintro rfl
  exact hb₂ ((hagree _ _ hx hy _ hep).symm.trans hb₁)

end EthCLLib.Proofs.FFG
