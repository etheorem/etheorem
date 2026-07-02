import EthCLSpecs.Heze.Focil
import EthCLSpecs.Fulu.ForkChoice
import EthCLLib.Spec.FiniteMap

/-!
# `EthCLSpecs.Heze.InclusionList`: the EIP-7805 (FOCIL) inclusion-list store + helpers

The fork-choice-side inclusion-list machinery Heze adds: the `InclusionListStore` and the
three helpers that maintain and read it (`consensus-specs/specs/heze/inclusion-list.md`).
An inclusion-list-committee member gossips a `SignedInclusionList`; the node files each one
under the committee root it names, tracks per-validator equivocation, and later reads back
the union of transactions every honest committee member committed to, so fork choice can
refuse to extend a payload that dropped them.

## One structural divergence from the spec: one store instead of two

The spec keeps `InclusionListStore` as a process-lifetime singleton, reached through
`get_inclusion_list_store()` (`cached_or_new_inclusion_list_store`), separate from the
fork-choice `Store`. This framework's fork choice is a pure `EStateM` over one `Store`, with
no ambient mutable singleton to hang a second store off. So the `InclusionListStore` is modeled
as a plain `forkstruct` and **held as a field of the
fork-choice `Store`** (`Heze.Store.inclusionListStore`, wired in `Heze/ForkChoice.lean`).
The handlers thread it through `Store` like every other piece of fork-choice state. Where the
Python calls `get_inclusion_list_store()` for the ambient singleton, the Lean call site passes
`store.inclusionListStore` instead; the helpers here take the `InclusionListStore` directly, so
they are agnostic to where it lives.

## Map / set representation

`inclusionLists` is the spec's `DefaultDict[Root, Dict[Root, InclusionList]]`, a nested
fork-choice map (`map Root (map Root InclusionList)`); a `defaultdict` miss (`store.X[key]`
for an absent key) is `(FcMap.lookup … key).getD FcMap.empty`, the empty inner collection.
`equivocators` is the spec's `DefaultDict[Root, Set[ValidatorIndex]]`; the `Set` is an
`Array ValidatorIndex` (membership via `.contains`, insertion via a guarded `push`). The
guard is real: an equivocator is only ever appended on the branch that has just confirmed the
validator is *not* already in the set, so the array never accumulates a duplicate and carries
true set semantics. `inclusionListTimeliness` is the flat `Dict[Root, bool]`.

`get_inclusion_list_transactions` is reached from the `on_execution_payload_envelope` vectors (via
`record_payload_inclusion_list_satisfaction`), but only against an empty store;
`process_inclusion_list` and the discriminating reads have no vector, so the pinned alpha.11 spec is
the oracle. Each helper mirrors the Python branch-for-branch; the build-enforced `#guard`s /
`native_decide`
pins below fix the load-bearing `process_inclusion_list` branches and the
`get_inclusion_list_transactions` equivocator / timeliness / dedup filters to values worked
out by hand from the comprehensions. `get_inclusion_list_transactions` needs a `BeaconState`
for its committee key, impractical to build for a pin, so the pins drive its inner
comprehension (`collectInclusionListTransactions`) on a hand-built store directly, the same
state-free factoring `Focil.cyclicSample` uses.
-/

set_option autoImplicit false

open EthCLLib.Spec
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

/-- `InclusionListStore` (`consensus-specs/specs/heze/inclusion-list.md:28-38`): the
fork-choice node's view of the inclusion lists it has seen. `inclusionLists` files each
stored `InclusionList` under its committee root then its own hash-tree root
(`DefaultDict[Root, Dict[Root, InclusionList]]`); `inclusionListTimeliness` records, per
stored-list root, whether it arrived before `INCLUSION_LIST_DUE_BPS`; `equivocators` is the
per-committee set of validator indices caught publishing two different lists. A `forkstruct`
rather than a bare `structure`, so a later fork can `inherit` it, and so it carries the auto
`[Preset]` / `[HasherTag]` uniformly with the containers it nests. -/
forkstruct InclusionListStore (map : MapKind) [HasherTag] where
  inclusionLists          : map Root (map Root InclusionList)
  inclusionListTimeliness : map Root Bool
  equivocators            : map Root (Array ValidatorIndex)

section

variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- The empty `InclusionListStore`: no stored lists, no timeliness, no equivocators. The seed
`get_forkchoice_store` plants (`consensus-specs/specs/heze/fork-choice.md:165`) and the base
every pin builds from, so the all-empty literal lives in one place. -/
def InclusionListStore.empty : InclusionListStore map :=
  { inclusionLists := FcMap.empty, inclusionListTimeliness := FcMap.empty, equivocators := FcMap.empty }

/-- The inner comprehension of `get_inclusion_list_transactions`
(`consensus-specs/specs/heze/inclusion-list.md:105-114`): over the inclusion lists stored for
one committee key, keep those from non-equivocating validators (and, when `onlyTimely`, only
the timely ones), gather their transactions, and deduplicate. Factored out of the accessor so
the equivocator / timeliness / dedup logic is unit-checkable without building a `BeaconState`
for the committee key (the `cyclicSample` pattern). One pass with `FcMap.fold` over the stored
map, which hands each `(ilRoot, il)` straight to the step (no second `lookup`, no dead `none`
branch). `timeliness[ilRoot]` is a plain dict read in the spec (every stored list has a
timeliness entry, written together in `process_inclusion_list`); the structurally-present key
reads through `.getD false`, the default never reached on the spec path. The dedup is the house
`arrayUnion #[] …` first-occurrence union: the spec's `list(set(transactions))` keeps each
transaction once and calls the order irrelevant, so a deterministic first-occurrence
representative lets the result be pinned by `#guard`. -/
private def collectInclusionListTransactions (inclusionLists : map Root InclusionList)
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool) (onlyTimely : Bool) :
    Array Transaction :=
  let collected : Array Transaction :=
    FcMap.fold (fun acc ilRoot il =>
      let timely := FcMap.lookupD timeliness ilRoot
      if !equivocators.contains il.validatorIndex && (!onlyTimely || timely) then
        acc ++ il.transactions.toArray
      else acc) #[] inclusionLists
  arrayUnion #[] collected

/-- `process_inclusion_list(store, inclusion_list, is_timely)`
(`consensus-specs/specs/heze/inclusion-list.md:57-82`): file a newly-received inclusion list,
or record an equivocation. Pure here (returns the updated `InclusionListStore`); the spec
mutates in place. The three branches mirror the Python:

* (A) the list is from a known equivocator for this committee (`validator_index in
  store.equivocators[key]`) → ignore it, return the store unchanged.
* (B) we already hold a list from this validator for this committee → if the new list differs
  from the stored one, add the validator to `equivocators[key]`; either way we have processed
  it, so return (storing nothing new). At most one stored list per validator exists (a list is
  filed only on branch (C), reached only when none matches), so the single `find?` match is
  exactly the Python loop's first-and-only hit. The equivocator `push` is guarded by branch
  (A) above, so it never duplicates.
* (C) otherwise → store the list under its `hash_tree_root` and record its timeliness.

`key` is the list's `inclusion_list_committee_root` (a field, no rehash). -/
forkdef processInclusionList (store : InclusionListStore map) (inclusionList : InclusionList)
    (isTimely : Bool) : InclusionListStore map :=
  let key := inclusionList.inclusionListCommitteeRoot
  let equivs := FcMap.lookupD store.equivocators key
  -- (A) ignore inclusion lists from known equivocators for this committee
  if equivs.contains inclusionList.validatorIndex then store
  else
    let stored := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
    match (FcMap.values stored).find? (fun il => il.validatorIndex == inclusionList.validatorIndex) with
    -- (B) already hold a list from this validator: equivocate iff it differs, then stop
    | some existing =>
      if existing == inclusionList then store
      else
        { store with
            equivocators := FcMap.insert store.equivocators key (equivs.push inclusionList.validatorIndex) }
    -- (C) first list from this validator: store it and its timeliness
    | none =>
      let inclusionListRoot := htr inclusionList
      let stored' := FcMap.insert stored inclusionListRoot inclusionList
      { store with
          inclusionLists := FcMap.insert store.inclusionLists key stored',
          inclusionListTimeliness := FcMap.insert store.inclusionListTimeliness inclusionListRoot isTimely }

/-- `get_inclusion_list_transactions(store, state, slot, only_timely=True)`
(`consensus-specs/specs/heze/inclusion-list.md:95-114`): the unique transactions from every
valid, non-equivocating inclusion list whose committee root matches the one `state`/`slot`
compute, optionally restricted to lists received before `INCLUSION_LIST_DUE_BPS`. Mirrors the
Python: derive the committee, key it by `hash_tree_root`, read the `defaultdict` entries for
that key, then run the comprehension (here `collectInclusionListTransactions`). Returns an
`Array` for the spec's `Sequence[Transaction]`; the dedup leaves order unspecified, as the
spec notes. -/
forkdef getInclusionListTransactions (store : InclusionListStore map) (state : State)
    (slot : Slot) (onlyTimely : Bool := true) : Array Transaction :=
  let committee := getInclusionListCommittee state slot
  let key := htr committee
  let inclusionLists := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
  let equivocators := FcMap.lookupD store.equivocators key
  collectInclusionListTransactions inclusionLists equivocators store.inclusionListTimeliness onlyTimely

end

/-! ### Build-enforced pins (vectorless)

FOCIL has no conformance vector, so these pin `process_inclusion_list`'s three branches and
`get_inclusion_list_transactions`'s comprehension to hand-derived outcomes. They build a small
`InclusionListStore treeMap` (deterministic key order) under the minimal preset and the FFI
hasher. The branch-(A)/(B) pins and every `collectInclusionListTransactions` pin are
hash-free, so kernel `#guard`; the branch-(C) pin computes `htr` (FFI `Sha256`), so it is a
`native_decide` `example` (`Lean.ofReduceBool`), per the project's hash-tactic rule. -/

private def pinKey : Root := Vector.replicate 32 7
private def pinDummyRoot : Root := Vector.replicate 32 1
private def pinAltRoot : Root := Vector.replicate 32 2

/-- A transaction holding the single byte `b` (enough to make two transactions compare
unequal for the dedup pins). -/
private def pinTx (b : UInt8) : Transaction := sszOfArray #[b]

/-- An inclusion list from validator `v` over committee `pinKey`, carrying `txs`. The `letI`
fixes the preset so the anonymous constructor can synthesize it (a return-type annotation alone
does not flow into instance resolution for `{ … }`). -/
private def pinIL (v : ValidatorIndex) (txs : Array Transaction) : @InclusionList minimal :=
  letI : Preset := minimal
  { slot := 0, validatorIndex := v, inclusionListCommitteeRoot := pinKey, transactions := sszOfArray txs }

/-- Number of inclusion lists stored under `pinKey`. The `letI`s supply the store's preset /
hasher for the field projection (Lean re-synthesizes them rather than reading the argument's
fixed type). -/
private def pinNumStored (s : @InclusionListStore minimal treeMap fastHasherTag) : Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  ((FcMap.lookup s.inclusionLists pinKey).getD FcMap.empty |> FcMap.keys).length
/-- The equivocator set recorded under `pinKey`. -/
private def pinEquivs (s : @InclusionListStore minimal treeMap fastHasherTag) : Array ValidatorIndex :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  FcMap.lookupD s.equivocators pinKey

/-- A store already holding one inclusion list from validator 5, filed under an arbitrary root
(branch (B) never rehashes the stored list, so the key is free). Shared by the two branch-(B)
pins. -/
private def pinStoreB : @InclusionListStore minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { inclusionLists := FcMap.insert FcMap.empty pinKey (FcMap.insert FcMap.empty pinDummyRoot (pinIL 5 #[pinTx 0xAA])),
    inclusionListTimeliness := FcMap.insert FcMap.empty pinDummyRoot true,
    equivocators := FcMap.empty }

-- Branch (A): a list from a validator already in `equivocators[key]` is ignored; nothing is
-- stored and the equivocator set is untouched. Hash-free, so kernel `#guard`. Returns
-- (stored count, equivocator count); expected (0, 1).
private def pinResA : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store : InclusionListStore treeMap :=
    { InclusionListStore.empty with equivocators := FcMap.insert FcMap.empty pinKey #[5] }
  let after := processInclusionList store (pinIL 5 #[pinTx 0xAA]) true
  (pinNumStored after, (pinEquivs after).size)
#guard pinResA = (0, 1)

-- Branch (B), conflict: a second, differing list from validator 5 adds 5 to `equivocators[key]`
-- and stores nothing new. Returns (equivocators, stored count); expected (#[5], 1).
private def pinResBConflict : Array ValidatorIndex × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinIL 5 #[pinTx 0xBB]) true
  (pinEquivs after, pinNumStored after)
#guard pinResBConflict = (#[5], 1)

-- Branch (B), match: re-receiving the *same* list is a no-op. Returns (equivocator count,
-- stored count); expected (0, 1).
private def pinResBMatch : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinIL 5 #[pinTx 0xAA]) true
  ((pinEquivs after).size, pinNumStored after)
#guard pinResBMatch = (0, 1)

-- Branch (C): the first list from a validator is stored (one entry under `key`) with its
-- timeliness recorded under `htr inclusion_list`. Reads the bit back at the actual `htr il` key
-- (not just its presence), so a flipped `insert … (!isTimely)` fails; the stored-count half pins
-- that branch (C) filed exactly one list. Computes `htr` (FFI `Sha256`), so `native_decide`
-- `example`s. Returns (stored count, timeliness at `htr il`); expected (1, some isTimely).
private def pinResC (isTimely : Bool) : Nat × Option Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store : InclusionListStore treeMap := InclusionListStore.empty
  let il := pinIL 5 #[pinTx 0xAA]
  let after := processInclusionList store il isTimely
  (pinNumStored after, FcMap.lookup after.inclusionListTimeliness (htr il))
example : pinResC true = (1, some true) := by native_decide
example : pinResC false = (1, some false) := by native_decide

-- `collectInclusionListTransactions` (the `get_inclusion_list_transactions` comprehension).
-- Two stored lists: validator 5 → [0xAA], validator 6 → [0xAA, 0xBB], timeliness 5=true /
-- 6=false. Pins worked out by hand from the comprehension. All hash-free, kernel `#guard`.
private def pinLists : treeMap Root (@InclusionList minimal) :=
  FcMap.insert (FcMap.insert FcMap.empty pinDummyRoot (pinIL 5 #[pinTx 0xAA]))
    pinAltRoot (pinIL 6 #[pinTx 0xAA, pinTx 0xBB])
private def pinTimeliness : treeMap Root Bool :=
  FcMap.insert (FcMap.insert FcMap.empty pinDummyRoot true) pinAltRoot false

/-- Run the comprehension over `pinLists` / `pinTimeliness` under the minimal preset, so the
hash-free `#guard`s below need no ambient instance. -/
private def pinCollect (equiv : Array ValidatorIndex) (onlyTimely : Bool) : Array Transaction :=
  letI : Preset := minimal
  collectInclusionListTransactions pinLists equiv pinTimeliness onlyTimely

-- No equivocators, timeliness ignored: union of {0xAA} and {0xAA, 0xBB}, deduped to two.
#guard (pinCollect #[] false).size = 2
#guard (pinCollect #[] false).contains (pinTx 0xAA)
#guard (pinCollect #[] false).contains (pinTx 0xBB)
-- only_timely drops validator 6's untimely list, leaving just {0xAA}.
#guard (pinCollect #[] true).size = 1
#guard (pinCollect #[] true).contains (pinTx 0xAA)
-- Equivocator 6 is filtered out regardless of timeliness, leaving just {0xAA}.
#guard (pinCollect #[6] false).size = 1
#guard (pinCollect #[6] false).contains (pinTx 0xAA)

end EthCLSpecs.Heze
