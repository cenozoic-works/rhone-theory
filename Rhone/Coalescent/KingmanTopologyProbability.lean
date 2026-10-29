/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanTopologySubtree
public import Rhone.Coalescent.KingmanTopologyCladeProduct
public import Rhone.Coalescent.KingmanSubtreeTopology

/-!
# Kingman topology probability from the per-clade factors

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem kingman_topology_probability_of_clade_factors (n : ℕ) (hn : 1 ≤ n)
    (T : LabelledTopology n) :
    topologyWeight n T =
      (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * (coalescentTopologyCladeProduct T : ℝ)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      exact kingman_topology_probability_of_clade_factors_one T
    have hn2 : 2 ≤ n := by omega
    obtain ⟨A, hA, hB, hs⟩ := binary_hierarchy_root_pair T.1 T.2 (by simpa using hn2)
    let B : Finset (Fin n) := univ \ A
    have ha : 1 ≤ A.card := card_pos.mpr hA
    have hb : 1 ≤ B.card := card_pos.mpr hB
    have hsum : n = A.card + B.card := by
      dsimp only [B]
      rw [card_sdiff_of_subset (subset_univ A), card_univ, Fintype.card_fin]
      have hc := card_le_univ A
      simp only [Fintype.card_fin] at hc
      omega
    have han : A.card < n := by omega
    have hbn : B.card < n := by omega
    have hAm : A ∈ T.1 := (mem_erase.mp (ADR11.roots_subset _
      (hs ▸ mem_insert_self A {univ \ A}))).2
    have hBm : B ∈ T.1 := (mem_erase.mp (ADR11.roots_subset _
      (hs ▸ mem_insert_of_mem (mem_singleton_self (univ \ A))))).2
    let Ta : LabelledTopology A.card := ⟨forestPreimage (cladeLabelEmbedding A)
      (T.1.filter (fun C => C ⊆ A)), isBinaryHierarchy_subtree_preimage T.1 T.2
        (cladeLabelEmbedding A) A hAm (cladeLabelEmbedding_range A)⟩
    let Tb : LabelledTopology B.card := ⟨forestPreimage (cladeLabelEmbedding B)
      (T.1.filter (fun C => C ⊆ B)), isBinaryHierarchy_subtree_preimage T.1 T.2
        (cladeLabelEmbedding B) B hBm (cladeLabelEmbedding_range B)⟩
    have hwa : Combinatorics.historyPayoff ((ADR11.singletonForest n).filter (fun C => C ⊆ A))
        (A.card - 1) (fun G => if G = T.1.filter (fun C => C ⊆ A) then 1 else 0) =
        topologyWeight A.card Ta :=
      topology_subtree_payoff n A.card T.1 A (cladeLabelEmbedding A)
        (cladeLabelEmbedding_range A)
    have hwb : Combinatorics.historyPayoff ((ADR11.singletonForest n).filter (fun C => C ⊆ B))
        (B.card - 1) (fun G => if G = T.1.filter (fun C => C ⊆ B) then 1 else 0) =
        topologyWeight B.card Tb :=
      topology_subtree_payoff n B.card T.1 B (cladeLabelEmbedding B)
        (cladeLabelEmbedding_range B)
    have hback (C : Finset (Fin n)) : forestEmbed (cladeLabelEmbedding C)
        (forestPreimage (cladeLabelEmbedding C) (T.1.filter (fun D => D ⊆ C))) =
        T.1.filter (fun D => D ⊆ C) := by
      apply forestEmbed_forestPreimage
      intro D hD
      rw [cladeLabelEmbedding_range]
      exact (mem_filter.mp hD).2
    have hpa : (∏ C ∈ (T.1.filter (fun C => C ⊆ A)).filter (fun C => 2 ≤ C.card),
        (C.card - 1)) = coalescentTopologyCladeProduct Ta := by
      rw [← hback A, clade_product_forestEmbed]
      rfl
    have hpb : (∏ C ∈ (T.1.filter (fun C => C ⊆ B)).filter (fun C => 2 ≤ C.card),
        (C.card - 1)) = coalescentTopologyCladeProduct Tb := by
      rw [← hback B, clade_product_forestEmbed]
      rfl
    have hprod := coalescent_topology_clade_product_split n hn2 T A hA hB hs
    change coalescentTopologyCladeProduct T = (n - 1) * _ *
      (∏ C ∈ (T.1.filter (fun C => C ⊆ B)).filter (fun C => 2 ≤ C.card),
        (C.card - 1)) at hprod
    rw [hpa, hpb] at hprod
    rw [topologyWeight_root_split n hn2 T A hA hB hs, hwa, hwb,
      ih A.card han ha Ta, ih B.card hbn hb Tb, hprod]
    simp only [hsum]
    exact topology_clade_factor_arithmetic A.card B.card _ _ ha hb
      (coalescentTopologyCladeProduct_ne_zero Ta) (coalescentTopologyCladeProduct_ne_zero Tb)
end Rhone.Coalescent
