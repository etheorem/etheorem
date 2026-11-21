import EthCLSpecs.Proofs.Heze.JustifiedPath

/-!
# `EthCLSpecs.Proofs.Heze.TipCheckpoint`: the checkpoint block of the carrier tip

The finalized test of `filter_node_tree` reads `get_checkpoint_block` of a leaf at the finalized
epoch. For the leaves below the tip `T` of the carrier chain `H`, that walk follows the blocks of
`H`: the ancestor path of `T` is the prefix of `H` to `T` (`CarrierWindow.tipStore`). So the
checkpoint block of `T` at an epoch is the checkpoint root of `H` there
(`tip_cb_eq_chainRoot`), and an honest target on `H` names it (`fcase_core_root`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs (ForkChoiceStoreRun pureState LawfulFcMap)
open EthCLLib.Spec
open EthCLSpecs.Heze (Preset Config Store BeaconState BeaconBlock Root Epoch getCheckpointBlock)
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos)

section
variable {map : MapKind} [Preset] [HasherTag] [Config] [CryptoBackend] [FcMap map]
  [LawfulFcMap map Root]

/-- The blocks of a run up to a bound are those of a prefix whose remaining blocks come after the
bound. -/
theorem filter_blocksOf_prefix {steps p rest : List ChainStep} (h : steps = p ++ rest) {n : Nat}
    (hrest : ∀ b ∈ blocksOf rest, n < b.slot.toNat) :
    (blocksOf steps).filter (fun b => b.slot.toNat ≤ n) =
      (blocksOf p).filter (fun b => b.slot.toNat ≤ n) := by
  rw [h, blocksOf_append, List.filter_append]
  have : (blocksOf rest).filter (fun b => b.slot.toNat ≤ n) = [] :=
    List.filter_eq_nil_iff.mpr fun b hb => by simpa using hrest b hb
  rw [this, List.append_nil]

/-- **The checkpoint block of the tip is the checkpoint root of the chain.** The ancestor path
of `T` has the blocks of a prefix `pT` of `steps`, and `w₁` is another prefix. The blocks of
`steps` after each prefix come after the first slot of `E`. Then `get_checkpoint_block` from `T`
returns the root after the path blocks up to that slot (`AncestorPath.checkpointBlock`), which is
the root of `w₁` at that slot (`rootAtSlot_eq_lastRootOf`). -/
theorem tip_cb_eq_chainRoot {a : BeaconBlock} {store : Store map} (hinv : SlotInv a store)
    (ha : FcMap.lookup store.blocks (htr a) = some a) {E : Epoch}
    (hfit : E.toNat * slotsPerEpoch < 2 ^ 64) (haE : a.slot ≤ E * UInt64.ofNat slotsPerEpoch)
    {T : Root} {preT : List ChainStep} (hpathT : AncestorPath a store T (blocksOf preT))
    {A : BeaconState} (hanc : htr (filledHeader A) = htr a)
    (hT : A.latestBlockHeader.slot.toNat ≤ E.toNat * slotsPerEpoch) (h1 : 1 ≤ E.toNat)
    {steps pT rest w₁ w₂ : List ChainStep} (hpre : steps = pT ++ rest)
    (hbl : blocksOf preT = blocksOf pT) (hw : steps = w₁ ++ w₂)
    (hrest : ∀ b ∈ blocksOf rest, E.toNat * slotsPerEpoch < b.slot.toNat)
    (hw₂ : ∀ b ∈ blocksOf w₂, E.toNat * slotsPerEpoch < b.slot.toNat) (t : Store map) :
    (getCheckpointBlock (StoreTransition := ForkChoiceStoreRun (Store map)) store T E).run t =
      .ok (chainRoot A w₁ E.toNat, t) := by
  rw [hpathT.checkpointBlock hinv ha hfit haE t, chainRoot_pos _ _ h1,
    rootAtSlot_eq_lastRootOf hanc _ hT]
  have hSv : (E * UInt64.ofNat slotsPerEpoch).toNat = E.toNat * slotsPerEpoch := by
    have hn : (UInt64.ofNat slotsPerEpoch).toNat = slotsPerEpoch :=
      UInt64.toNat_ofNat_of_lt EthCLSpecs.Heze.Const.slotsPerEpochLt
    rw [UInt64.toNat_mul, hn, Nat.mod_eq_of_lt hfit]
  -- The UInt64 bound of the walk is the Nat bound of the chain root.
  have hf : (blocksOf preT).filter (fun b => b.slot ≤ E * UInt64.ofNat slotsPerEpoch) =
      (blocksOf preT).filter (fun b => b.slot.toNat ≤ E.toNat * slotsPerEpoch) :=
    List.filter_congr fun b _ => by
      rw [← hSv]
      exact decide_eq_decide.mpr UInt64.le_iff_toNat_le
  rw [hf, hbl, ← filter_blocksOf_prefix hpre hrest, filter_blocksOf_prefix hw hw₂]

end

end EthCLSpecs.Proofs.Heze
