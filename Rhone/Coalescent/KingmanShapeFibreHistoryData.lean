/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryCardCast
public import Rhone.Coalescent.KingmanShapeFibreTransport
public import Rhone.Coalescent.KingmanShapePrerootRelation
/-!
# Recovered daughter histories reconstruct the chronological ranked-shape relation

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rootHistoryFibreHistoryData (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) (h : Combinatorics.RankedLabelledHistory n)
    (hk : (firstMergerRoot n hn h).card = k.val) :
    ((Combinatorics.RankedLabelledHistory k.val × Combinatorics.RankedLabelledHistory (n - k.val)) ×
      Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) := by
  let A := firstMergerRoot n hn h
  let p := firstRootHistoryDecomposition n hn h
  have hB : (univ \ A).card = n - k.val := by
    have hc := rootPartition_card A
    dsimp only [A] at hc ⊢
    omega
  exact ⟨⟨Equiv.cast (congrArg Combinatorics.RankedLabelledHistory hk) p.1.1,
    Equiv.cast (congrArg Combinatorics.RankedLabelledHistory hB) p.1.2⟩,
    Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving (congrArg (fun a => a - 1) hk)
      (congrArg (fun a => a - 1) hB)) p.2⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
private theorem forestEmbed_sumCongr_labels {L M P Q : Type*}
    [DecidableEq L] [DecidableEq M] [DecidableEq P] [DecidableEq Q]
    (e : L ≃ P) (f : M ≃ Q)
    (F : Finset (Finset L)) (G : Finset (Finset M)) :
    forestEmbed (Equiv.sumCongr e f).toEmbedding
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr G) =
    forestEmbed Function.Embedding.inl (forestEmbed e.toEmbedding F) ∪
      forestEmbed Function.Embedding.inr (forestEmbed f.toEmbedding G) := by
  rw [forestEmbed_union, forestEmbed_comp, forestEmbed_comp,
    forestEmbed_comp, forestEmbed_comp]
  have hl : Function.Embedding.inl.trans (Equiv.sumCongr e f).toEmbedding =
      e.toEmbedding.trans Function.Embedding.inl := Function.Embedding.ext (fun _ => rfl)
  have hr : Function.Embedding.inr.trans (Equiv.sumCongr e f).toEmbedding =
      f.toEmbedding.trans Function.Embedding.inr := Function.Embedding.ext (fun _ => rfl)
  rw [hl, hr]
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
private theorem forestEmbed_labels_trans {L M N : Type*}
    [DecidableEq L] [DecidableEq M] [DecidableEq N]
    (u : L ≃ M) (e : L ≃ N) (v : N ≃ M) (F : Finset (Finset L)) :
    forestEmbed (u.symm.trans (e.trans v)).toEmbedding (forestEmbed u.toEmbedding F) =
      forestEmbed v.toEmbedding (forestEmbed e.toEmbedding F) := by
  rw [forestEmbed_comp, forestEmbed_comp]
  congr 1
  apply Function.Embedding.ext
  intro x
  change v (e (u.symm (u x))) = v (e x)
  rw [u.symm_apply_apply]
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryFibreHistoryData_reconstruct (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) (h : Combinatorics.RankedLabelledHistory n)
    (hk : (firstMergerRoot n hn h).card = k.val) :
    let p := rootHistoryFibreHistoryData n hn k h hk
    Combinatorics.RankedShapeRel n h (firstRootHistoryAssemble n hn k p.1.1 p.1.2 p.2) := by
  let A := firstMergerRoot n hn h
  have hB : (univ \ A).card = n - k.val := by
    have hc := rootPartition_card A
    dsimp only [A] at hc ⊢
    omega
  let p := firstRootHistoryDecomposition n hn h
  let u := rootPartitionEquiv A
  let v := firstRootAssemblyLabels n k
  let e := Equiv.sumCongr (finCongr hk) (finCongr hB)
  let q := u.symm.trans (e.trans v)
  apply rankedShapeRel_of_preroot n (by omega) _ _ q
  intro r hr
  rw [historyAt_firstRootHistoryAssemble _ _ _ _ _ _ r hr]
  dsimp only [rootHistoryFibreHistoryData]
  rw [interleavingLeft_castFirst, interleavingRight_castFirst,
    historyAt_castCard, historyAt_castCard]
  · change forestEmbed q.toEmbedding _ = forestEmbed v.toEmbedding
      (forestEmbed Function.Embedding.inl
        (forestEmbed (finCongr hk).toEmbedding
            (Combinatorics.historyAt _ _ p.1.1 (Combinatorics.interleavingLeft p.2.1 r))) ∪
        forestEmbed Function.Embedding.inr
        (forestEmbed (finCongr hB).toEmbedding
            (Combinatorics.historyAt _ _ p.1.2 (Combinatorics.interleavingRight p.2.1 r))))
    rw [← forestEmbed_sumCongr_labels, ← forestEmbed_labels_trans u e v]
    congr 1
    symm
    have hs := (binary_hierarchy_root_pair_at _
        (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h)
      (by simpa using (show 2 ≤ n by omega)) A (firstMergerRoot_spec n hn h).1).2.2
    exact historyAt_rootHistoryDecomposition n (by omega) h A hs r hr
  all_goals dsimp only [A] at hB; omega

/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryFibreData_eq_historyData (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) (h : Combinatorics.RankedLabelledHistory n)
    (hk : (firstMergerRoot n hn h).card = k.val) :
    rootHistoryFibreData n hn k h hk =
      let p := rootHistoryFibreHistoryData n hn k h hk
      ((Quotient.mk (Combinatorics.rankedShapeSetoid k.val) p.1.1,
        Quotient.mk (Combinatorics.rankedShapeSetoid (n - k.val)) p.1.2), p.2) := by
  dsimp only [rootHistoryFibreData, rootHistoryFibreHistoryData]
  rw [quotient_mk_castCard, quotient_mk_castCard]
  all_goals
    first
    | rfl
    | exact hk
    | have hc := rootPartition_card (firstMergerRoot n hn h); omega
end Rhone.Coalescent
