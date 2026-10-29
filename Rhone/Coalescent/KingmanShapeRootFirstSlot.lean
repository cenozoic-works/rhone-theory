/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootDecomposition
public import Rhone.Coalescent.KingmanShapeFirstRoot
public import Rhone.Coalescent.KingmanShapeRootPairAt
public import Rhone.Combinatorics.KingmanShapeFirstInterleaving
/-!
# Canonical root daughter recovery retains the first chronological merger slot

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_first_slot (n : ℕ) (hn : 3 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) (hA : Combinatorics.firstMergerClade n (by omega) h ⊆ A) :
    0 ∈ (rootHistoryDecomposition n (by omega) h A hs).2.1.image Fin.val := by
  classical
  let p := rootHistoryDecomposition n (by omega) h A hs
  by_contra hz
  have hl : Combinatorics.interleavingLeft p.2 1 = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi, hit⟩ := mem_filter.mp hi
    have hiv : i.val = 0 := by omega
    exact hz (mem_image.mpr ⟨i, hi, hiv⟩)
  have he := historyAt_rootHistoryDecomposition n (by omega) h A hs 1 (by omega)
  change forestEmbed (rootPartitionEquiv A).toEmbedding
    (forestEmbed Function.Embedding.inl
        (Combinatorics.historyAt _ _ p.1.1 (Combinatorics.interleavingLeft p.2 1)) ∪
      forestEmbed Function.Embedding.inr
          (Combinatorics.historyAt _ _ p.1.2 (Combinatorics.interleavingRight p.2 1))) = _ at he
  rw [hl, Combinatorics.historyAt_zero] at he
  have hm : Combinatorics.firstMergerClade n
      (by omega) h ∈ Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h 1 := by
    rw [(Combinatorics.firstMergerClade_spec n (by omega) h).2]
    exact mem_insert_self _ _
  rw [← he] at hm
  obtain ⟨D, hD, hDe⟩ := mem_image.mp hm
  rcases mem_union.mp hD with hL | hR
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hL
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    have hc := congrArg Finset.card hDe
    simp only [card_map, card_singleton] at hc
    have hh := (Combinatorics.firstMergerClade_spec n (by omega) h).1
    omega
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hR
    have hsub : Combinatorics.firstMergerClade n (by omega) h ⊆ univ \ A := by
      rw [← hDe]
      exact (map_subset_map.mpr (map_subset_map.mpr (subset_univ C))).trans_eq
        (rootPartitionRange_right A)
    have hnon : (Combinatorics.firstMergerClade n (by omega) h).Nonempty := by
      apply card_pos.mp
      rw [(Combinatorics.firstMergerClade_spec n (by omega) h).1]
      omega
    obtain ⟨x, hx⟩ := hnon
    exact (mem_sdiff.mp (hsub hx)).2 (hA hx)
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def firstRootHistoryDecomposition (n : ℕ) (hn : 3 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) :
    (Combinatorics.RankedLabelledHistory (firstMergerRoot n hn h).card ×
      Combinatorics.RankedLabelledHistory (univ \ firstMergerRoot n hn h).card) ×
      Combinatorics.FirstHistoryInterleaving ((firstMergerRoot n hn h).card - 1)
        ((univ \ firstMergerRoot n hn h).card - 1) := by
  let A := firstMergerRoot n hn h
  have hs := (binary_hierarchy_root_pair_at _
      (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h)
    (by simpa using hn.trans' (by omega : 2 ≤ 3)) A (firstMergerRoot_spec n hn h).1).2.2
  let p := rootHistoryDecomposition n (by omega) h A hs
  exact ⟨p.1, ⟨p.2, rootHistoryDecomposition_first_slot n hn h A hs
    (firstMergerRoot_spec n hn h).2⟩⟩
end Rhone.Coalescent
