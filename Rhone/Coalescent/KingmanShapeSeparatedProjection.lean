/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedHistory
/-! # Projection of a separated forest onto its two subtree forests -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sumForest_isForest {L M : Type*} [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) :
    ADR11.IsForest (forestEmbed (Function.Embedding.inl : L ↪ L ⊕ M) F ∪
      forestEmbed (Function.Embedding.inr : M ↪ L ⊕ M) H) := by
  apply ((isForest_forestEmbed_iff (Function.Embedding.inl : L ↪ L ⊕ M) F).mpr hF).union
    ((isForest_forestEmbed_iff (Function.Embedding.inr : M ↪ L ⊕ M) H).mpr hH)
  intro A hA B hB
  obtain ⟨D, _, rfl⟩ := mem_image.mp hA
  obtain ⟨E, _, rfl⟩ := mem_image.mp hB
  apply Or.inr
  apply Or.inr
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨d, _, rfl⟩ := mem_map.mp hx
  obtain ⟨e, _, he⟩ := mem_map.mp hy
  cases he
theorem sumLeftForest_embed {L M : Type*} [Fintype L] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) :
    forestEmbed Function.Embedding.inl (sumLeftForest W) =
      W.filter (fun C => C ⊆ (univ : Finset L).map Function.Embedding.inl) :=
  forestEmbed_forestPreimage _ _ (fun _ hC => (mem_filter.mp hC).2)
theorem sumRightForest_embed {L M : Type*} [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) :
    forestEmbed Function.Embedding.inr (sumRightForest W) =
      W.filter (fun C => C ⊆ (univ : Finset M).map Function.Embedding.inr) :=
  forestEmbed_forestPreimage _ _ (fun _ hC => (mem_filter.mp hC).2)
theorem sumPureForest_decomposition {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (W : Finset (Finset (L ⊕ M)))
    (hpure : SumPureForest W) :
    forestEmbed Function.Embedding.inl (sumLeftForest W) ∪
      forestEmbed Function.Embedding.inr (sumRightForest W) = W := by
  rw [sumLeftForest_embed, sumRightForest_embed]
  ext C
  simp only [mem_union, mem_filter]
  constructor
  · rintro (⟨hC, _⟩ | ⟨hC, _⟩) <;> exact hC
  · intro hC
    rcases hpure C hC with hl | hr
    · exact Or.inl ⟨hC, hl⟩
    · exact Or.inr ⟨hC, hr⟩
theorem sumLeftForest_isForest {L M : Type*} [Fintype L] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (hW : ADR11.IsForest W) :
    ADR11.IsForest (sumLeftForest W) := by
  apply (isForest_forestEmbed_iff (Function.Embedding.inl : L ↪ L ⊕ M) _).mp
  rw [sumLeftForest_embed]
  exact ⟨fun C hC => hW.1 C (mem_filter.mp hC).1,
    fun C hC D hD => hW.2 C (mem_filter.mp hC).1 D (mem_filter.mp hD).1⟩
theorem sumRightForest_isForest {L M : Type*} [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (hW : ADR11.IsForest W) :
    ADR11.IsForest (sumRightForest W) := by
  apply (isForest_forestEmbed_iff (Function.Embedding.inr : M ↪ L ⊕ M) _).mp
  rw [sumRightForest_embed]
  exact ⟨fun C hC => hW.1 C (mem_filter.mp hC).1,
    fun C hC D hD => hW.2 C (mem_filter.mp hC).1 D (mem_filter.mp hD).1⟩
theorem sumLeftForest_mem {L M : Type*} [Fintype L] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (D : Finset L) (hD : D ∈ sumLeftForest W) :
    D.map Function.Embedding.inl ∈ W := by
  have hm : D.map (Function.Embedding.inl : L ↪ L ⊕ M) ∈
      forestEmbed (Function.Embedding.inl : L ↪ L ⊕ M) (sumLeftForest W) :=
    mem_image.mpr ⟨D, hD, rfl⟩
  rw [sumLeftForest_embed] at hm
  exact (mem_filter.mp hm).1
theorem sumRightForest_mem {L M : Type*} [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (D : Finset M) (hD : D ∈ sumRightForest W) :
    D.map Function.Embedding.inr ∈ W := by
  have hm : D.map (Function.Embedding.inr : M ↪ L ⊕ M) ∈
      forestEmbed (Function.Embedding.inr : M ↪ L ⊕ M) (sumRightForest W) :=
    mem_image.mpr ⟨D, hD, rfl⟩
  rw [sumRightForest_embed] at hm
  exact (mem_filter.mp hm).1
theorem sumLeftForest_root {L M : Type*} [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (A : Finset (L ⊕ M)) (hA : A ∈ ADR11.roots W)
    (hAL : A ⊆ (univ : Finset L).map Function.Embedding.inl) :
    ∃ B ∈ ADR11.roots (sumLeftForest W), B.map Function.Embedding.inl = A := by
  have hm : A ∈ forestEmbed Function.Embedding.inl (sumLeftForest W) := by
    rw [sumLeftForest_embed]
    exact mem_filter.mpr ⟨ADR11.roots_subset W hA, hAL⟩
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hm
  refine ⟨B, ADR11.mem_roots.mpr ⟨hB, ?_⟩, rfl⟩
  intro D hD hBD
  apply map_injective Function.Embedding.inl
  exact (ADR11.mem_roots.mp hA).2 _ (sumLeftForest_mem W D hD) (map_subset_map.mpr hBD)
theorem sumRightForest_root {L M : Type*} [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (A : Finset (L ⊕ M)) (hA : A ∈ ADR11.roots W)
    (hAR : A ⊆ (univ : Finset M).map Function.Embedding.inr) :
    ∃ B ∈ ADR11.roots (sumRightForest W), B.map Function.Embedding.inr = A := by
  have hm : A ∈ forestEmbed Function.Embedding.inr (sumRightForest W) := by
    rw [sumRightForest_embed]
    exact mem_filter.mpr ⟨ADR11.roots_subset W hA, hAR⟩
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hm
  refine ⟨B, ADR11.mem_roots.mpr ⟨hB, ?_⟩, rfl⟩
  intro D hD hBD
  apply map_injective Function.Embedding.inr
  exact (ADR11.mem_roots.mp hA).2 _ (sumRightForest_mem W D hD) (map_subset_map.mpr hBD)
end Rhone.Coalescent
