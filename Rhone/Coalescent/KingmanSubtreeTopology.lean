/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanForestPreimage
public import Rhone.Combinatorics.KingmanHistoryTopology
/-! # Retained subtree hierarchies on their own finite leaf sets -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem isBinaryHierarchy_subtree_preimage {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (G : Finset (Finset M)) (hG : ADR11.IsBinaryHierarchy G)
    (e : L ↪ M) (C : Finset M) (hC : C ∈ G) (he : (univ : Finset L).map e = C) :
    ADR11.IsBinaryHierarchy (forestPreimage e (G.filter (fun D => D ⊆ C))) := by
  classical
  let H := G.filter (fun D => D ⊆ C)
  have hH : ADR11.IsForest H :=
    ⟨fun D hD => hG.1.2.2.1 D (mem_filter.mp hD).1,
      fun D hD E hE => hG.1.2.2.2 D (mem_filter.mp hD).1 E (mem_filter.mp hE).1⟩
  have hrange : ∀ D ∈ H, D ⊆ (univ : Finset L).map e := by
    intro D hD
    rw [he]
    exact (mem_filter.mp hD).2
  have hback := forestEmbed_forestPreimage e H hrange
  have hPull : ADR11.IsForest (forestPreimage e H) := by
    apply (isForest_forestEmbed_iff e (forestPreimage e H)).mp
    rw [hback]
    exact hH
  have hpreC : C.preimage e e.injective.injOn = univ := by
    rw [← he]
    exact preimage_map e univ
  refine ⟨⟨?_, ?_, hPull⟩, ?_⟩
  · exact mem_image.mpr ⟨C, mem_filter.mpr ⟨hC, subset_rfl⟩, hpreC⟩
  · intro x
    have hxC : e x ∈ C := by rw [← he]; exact mem_map.mpr ⟨x, mem_univ _, rfl⟩
    have hpre : ({e x} : Finset M).preimage e e.injective.injOn = {x} := by
      have hmap : ({x} : Finset L).map e = {e x} := map_singleton e x
      rw [← hmap]
      exact preimage_map e {x}
    exact mem_image.mpr ⟨{e x}, mem_filter.mpr
      ⟨hG.1.2.1 (e x), singleton_subset_iff.mpr hxC⟩, hpre⟩
  · intro D hD hDc
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hD
    obtain ⟨hEG, hEC⟩ := mem_filter.mp hE
    have hEmap : (E.preimage e e.injective.injOn).map e = E := by
      ext z
      constructor
      · intro hz
        obtain ⟨y, hy, rfl⟩ := mem_map.mp hz
        exact mem_preimage.mp hy
      · intro hz
        have hzC : z ∈ (univ : Finset L).map e := by rw [he]; exact hEC hz
        obtain ⟨y, _, rfl⟩ := mem_map.mp hzC
        exact mem_map.mpr ⟨y, mem_preimage.mpr hz, rfl⟩
    have hec : E.card = (E.preimage e e.injective.injOn).card := by
      calc
        E.card = ((E.preimage e e.injective.injOn).map e).card := congrArg Finset.card hEmap.symm
        _ = (E.preimage e e.injective.injOn).card := card_map e
    obtain ⟨B₁, hB₁, B₂, hB₂, hd, hu⟩ := hG.2 E hEG (by rw [hec]; exact hDc)
    have hB₁C : B₁ ⊆ C := (show B₁ ⊆ E by rw [← hu]; exact subset_union_left).trans hEC
    have hB₂C : B₂ ⊆ C := (show B₂ ⊆ E by rw [← hu]; exact subset_union_right).trans hEC
    refine ⟨B₁.preimage e e.injective.injOn,
      mem_image.mpr ⟨B₁, mem_filter.mpr ⟨hB₁, hB₁C⟩, rfl⟩,
      B₂.preimage e e.injective.injOn,
      mem_image.mpr ⟨B₂, mem_filter.mpr ⟨hB₂, hB₂C⟩, rfl⟩, ?_, ?_⟩
    · apply disjoint_left.mpr
      intro x hx₁ hx₂
      exact disjoint_left.mp hd (mem_preimage.mp hx₁) (mem_preimage.mp hx₂)
    · ext x
      simp only [mem_union, mem_preimage]
      rw [← hu, mem_union]
end Rhone.Coalescent
