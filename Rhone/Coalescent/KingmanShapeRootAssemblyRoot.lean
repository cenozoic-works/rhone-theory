/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootAssembly
/-!
# Identify the first-root daughter of an assembled chronological history

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def firstRootAssemblyLabels (n : ℕ)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n}) : Fin k.val ⊕ Fin (n - k.val) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by have hk := (mem_Ico.mp k.property).2; omega))
theorem historyAt_firstRootHistoryAssemble (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (r : ℕ) (hr : r ≤ n - 2) :
    Combinatorics.historyAt (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s) r =
    forestEmbed (firstRootAssemblyLabels n k).toEmbedding
      (forestEmbed Function.Embedding.inl
        (Combinatorics.historyAt _ (k.val - 1) h (Combinatorics.interleavingLeft s.1 r)) ∪
       forestEmbed Function.Embedding.inr
        (Combinatorics.historyAt _ (n - k.val - 1) g (Combinatorics.interleavingRight s.1 r))) := by
  unfold firstRootHistoryAssemble
  rw [Combinatorics.historyAt_castLength, historyAt_historyLabelsEquiv,
      Combinatorics.historyAt_historyAppend,
    historyAt_historyInterleave]
  · rfl
  all_goals have hk := mem_Ico.mp k.property; omega
theorem historyEnd_firstRootHistoryAssemble (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :
    Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s) =
    forestEmbed (firstRootAssemblyLabels n k).toEmbedding
      (binaryHierarchyJoin (Combinatorics.historyEnd _ (k.val - 1) h)
        (Combinatorics.historyEnd _ (n - k.val - 1) g)) := by
  unfold firstRootHistoryAssemble
  rw [Combinatorics.historyEnd_castLength, ← historyAt_terminal, historyAt_historyLabelsEquiv,
    historyAt_terminal, Combinatorics.historyEnd_historyAppend]
  · rfl
  · have hk := mem_Ico.mp k.property; omega
theorem firstMergerRoot_firstRootHistoryAssemble (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :
    firstMergerRoot n hn (firstRootHistoryAssemble n hn k h g s) =
      ((univ : Finset (Fin k.val)).map Function.Embedding.inl).map
        (firstRootAssemblyLabels n k).toEmbedding := by
  have hk := mem_Ico.mp k.property
  let e := firstRootAssemblyLabels n k
  let G := Combinatorics.historyEnd (ADR11.singletonForest k.val) (k.val - 1) h
  let J := Combinatorics.historyEnd (ADR11.singletonForest (n - k.val)) (n - k.val - 1) g
  let W := forestEmbed Function.Embedding.inl G ∪ forestEmbed Function.Embedding.inr J
  have hL := Combinatorics.historyEnd_isBinaryHierarchy k.val (by omega) h
  have hR := Combinatorics.historyEnd_isBinaryHierarchy (n - k.val) (by omega) g
  have hnot : (univ : Finset (Fin k.val ⊕ Fin (n - k.val))) ∉ W := by
    intro hu
    rcases mem_union.mp hu with hu | hu
    · obtain ⟨C, _, hC⟩ := mem_image.mp hu
      have hx : Sum.inr (⟨0, by omega⟩ : Fin (n - k.val)) ∈ C.map Function.Embedding.inl :=
        hC.symm ▸ mem_univ _
      obtain ⟨x, _, he⟩ := mem_map.mp hx
      cases he
    · obtain ⟨C, _, hC⟩ := mem_image.mp hu
      have hx : Sum.inl (⟨0, by omega⟩ : Fin k.val) ∈ C.map Function.Embedding.inr :=
        hC.symm ▸ mem_univ _
      obtain ⟨x, _, he⟩ := mem_map.mp hx
      cases he
  have herase : (Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ = forestEmbed e.toEmbedding W := by
    rw [historyEnd_firstRootHistoryAssemble]
    change (forestEmbed e.toEmbedding (insert univ W)).erase univ = _
    rw [← clade_map_equiv_univ e, ← forestEmbed_erase, erase_insert hnot]
  apply firstMergerRoot_unique
  · rw [herase, roots_forestEmbed]
    exact mem_image.mpr ⟨univ.map Function.Embedding.inl,
      history_sum_full_left_root G J hL.1.2.2 hL.1.1, rfl⟩
  · let q := firstRootHistoryAssemble n hn k h g s
    let D := Combinatorics.firstMergerClade n (by omega) q
    have hD : D ∈ Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) q 1 := by
      rw [(Combinatorics.firstMergerClade_spec n (by omega) q).2]
      exact mem_insert_self _ _
    rw [historyAt_firstRootHistoryAssemble n hn k h g s 1 (by omega)] at hD
    obtain ⟨C, hC, hCD⟩ := mem_image.mp hD
    have hzero : Combinatorics.interleavingRight s.1 1 = 0 := by
      have hz := Combinatorics.interleaving_counts_zero s.1
      let z : Fin (k.val - 1 + (n - k.val - 1)) := ⟨0, by omega⟩
      have hm : z ∈ s.1.1 := by
        obtain ⟨i, hi, he⟩ := mem_image.mp s.2
        have hiz : i = z := Fin.ext he
        exact hiz ▸ hi
      have hc := Combinatorics.interleaving_counts_succ s.1 z
      rw [ite_eq_left hm] at hc
      simpa only [z, hz.2] using hc.2
    rcases mem_union.mp hC with hC | hC
    · obtain ⟨B, _, rfl⟩ := mem_image.mp hC
      change D ⊆ _
      rw [← hCD]
      exact map_subset_map.mpr (map_subset_map.mpr (subset_univ B))
    · rw [hzero, Combinatorics.historyAt_zero] at hC
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hC
      obtain ⟨x, _, rfl⟩ := mem_image.mp hB
      have hc := (Combinatorics.firstMergerClade_spec n (by omega) q).1
      change D.card = 2 at hc
      rw [← hCD, card_map, card_map, card_singleton] at hc
      omega
theorem firstMergerRoot_card_firstRootHistoryAssemble (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :
    (firstMergerRoot n hn (firstRootHistoryAssemble n hn k h g s)).card = k.val := by
  rw [firstMergerRoot_firstRootHistoryAssemble, card_map, card_map, card_univ,
    Fintype.card_fin]
end Rhone.Coalescent
