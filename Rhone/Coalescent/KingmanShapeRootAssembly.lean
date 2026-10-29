/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootFirstSlot
public import Rhone.Combinatorics.KingmanShapeHistoryAppend
public import Rhone.Coalescent.KingmanShapeJoin
/-!
# Assemble first-root histories from daughter histories and chronological slots

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem history_sum_full_left_root {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hU : univ ∈ F) :
    (univ : Finset L).map (Function.Embedding.inl : L ↪ L ⊕ M) ∈ ADR11.roots
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) := by
  apply ADR11.mem_roots.mpr
  refine ⟨mem_union_left _ (mem_image.mpr ⟨univ, hU, rfl⟩), ?_⟩
  intro D hD hBD
  rcases mem_union.mp hD with hD | hD
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact congrArg (fun X => X.map Function.Embedding.inl)
      (subset_antisymm (subset_univ C) (map_subset_map.mp hBD))
  · obtain ⟨C, _, rfl⟩ := mem_image.mp hD
    obtain ⟨b, hb⟩ := hF.1 univ hU
    have hin := hBD (mem_map.mpr ⟨b, hb, rfl⟩)
    obtain ⟨c, _, he⟩ := mem_map.mp hin
    cases he
theorem history_sum_full_right_root {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hH : ADR11.IsForest H) (hU : univ ∈ H) :
    (univ : Finset M).map (Function.Embedding.inr : M ↪ L ⊕ M) ∈ ADR11.roots
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) := by
  apply ADR11.mem_roots.mpr
  refine ⟨mem_union_right _ (mem_image.mpr ⟨univ, hU, rfl⟩), ?_⟩
  intro D hD hBD
  rcases mem_union.mp hD with hD | hD
  · obtain ⟨C, _, rfl⟩ := mem_image.mp hD
    obtain ⟨b, hb⟩ := hH.1 univ hU
    have hin := hBD (mem_map.mpr ⟨b, hb, rfl⟩)
    obtain ⟨c, _, he⟩ := mem_map.mp hin
    cases he
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact congrArg (fun X => X.map Function.Embedding.inr)
      (subset_antisymm (subset_univ C) (map_subset_map.mp hBD))
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def firstRootHistoryAssemble (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :
        Combinatorics.RankedLabelledHistory n := by
  have hk := mem_Ico.mp k.property
  have hL := Combinatorics.historyEnd_isBinaryHierarchy k.val (by omega) h
  have hR := Combinatorics.historyEnd_isBinaryHierarchy (n - k.val) (by omega) g
  let F := ADR11.singletonForest k.val
  let H := ADR11.singletonForest (n - k.val)
  let W := forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H
  let t := k.val - 1 + (n - k.val - 1)
  let p := historyInterleave F H (ADR11.isForest_singletonForest _)
    (ADR11.isForest_singletonForest _) _ _ h g s.1
  let G := Combinatorics.historyEnd F (k.val - 1) h
  let J := Combinatorics.historyEnd H (n - k.val - 1) g
  have hm : binaryHierarchyJoin G J ∈ ADR11.merges (Combinatorics.historyEnd W t p) := by
    rw [historyEnd_historyInterleave]
    apply ADR11.mem_merges.mpr
    refine ⟨univ.map Function.Embedding.inl, history_sum_full_left_root G J hL.1.2.2 hL.1.1,
      univ.map Function.Embedding.inr, history_sum_full_right_root G J hR.1.2.2 hR.1.1, ?_, ?_⟩
    · intro he
      obtain ⟨x, hx⟩ := hL.1.2.2.1 univ hL.1.1
      have hin := he ▸ (mem_map.mpr ⟨x, hx, rfl⟩ :
        Sum.inl x ∈ (univ : Finset (Fin k.val)).map Function.Embedding.inl)
      obtain ⟨y, _, hy⟩ := mem_map.mp hin
      cases hy
    · have hu : (univ : Finset (Fin k.val)).map Function.Embedding.inl ∪
          (univ : Finset (Fin (n - k.val))).map Function.Embedding.inr = univ := by
        ext x
        cases x <;> simp
      rw [hu]
      rfl
  let e : Fin k.val ⊕ Fin (n - k.val) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  let q := Combinatorics.historyAppend W t p (binaryHierarchyJoin G J) hm
  let r := historyLabelsEquiv e W (ADR11.singletonForest n)
    (singletonForest_sum_embed _ _ _ e) (t + 1) q
  exact Equiv.cast (congrArg (Combinatorics.RankedForestHistory (ADR11.singletonForest n))
    (show t + 1 = n - 1 by dsimp [t]; omega)) r
end Rhone.Coalescent
