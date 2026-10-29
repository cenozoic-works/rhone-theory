/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootDaughter
public import Rhone.Coalescent.KingmanRootReconstruction
/-!
# Daughter leaf equivalences reconstruct a global endpoint relabelling

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem binaryHierarchy_daughter_reconstruction (n : ℕ) (G : Combinatorics.BinaryHierarchy n)
    (A : Finset (Fin n))
    (hs : ADR11.roots (G.1.erase univ) = {A, univ \ A}) :
    G.1 = insert univ
      (forestEmbed (cladeLabelEmbedding A)
        (forestPreimage (cladeLabelEmbedding A) (G.1.filter (fun C => C ⊆ A))) ∪
      forestEmbed (cladeLabelEmbedding (univ \ A))
        (forestPreimage (cladeLabelEmbedding (univ \ A))
          (G.1.filter (fun C => C ⊆ univ \ A)))) := by
  have ha : forestEmbed (cladeLabelEmbedding A)
      (forestPreimage (cladeLabelEmbedding A) (G.1.filter (fun C => C ⊆ A))) =
      G.1.filter (fun C => C ⊆ A) := by
    apply forestEmbed_forestPreimage
    intro C hc
    rw [cladeLabelEmbedding_range]
    exact (mem_filter.mp hc).2
  have hb : forestEmbed (cladeLabelEmbedding (univ \ A))
      (forestPreimage (cladeLabelEmbedding (univ \ A))
        (G.1.filter (fun C => C ⊆ univ \ A))) =
      G.1.filter (fun C => C ⊆ univ \ A) := by
    apply forestEmbed_forestPreimage
    intro C hc
    rw [cladeLabelEmbedding_range]
    exact (mem_filter.mp hc).2
  rw [ha, hb]
  ext C
  constructor
  · intro hC
    rcases Combinatorics.root_split_clade_purity G.1 A hs C hC with rfl | hCA | hCB
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hC, hCA⟩))
    · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hC, hCB⟩))
  · intro hc
    rcases mem_insert.mp hc with rfl | hc
    · exact G.2.1.1
    · rcases mem_union.mp hc with hc | hc <;> exact (mem_filter.mp hc).1
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchy_rel_of_daughter_maps (n : ℕ) (G H : Combinatorics.BinaryHierarchy n)
    (A B : Finset (Fin n))
    (hs : ADR11.roots (G.1.erase univ) = {A, univ \ A})
    (ht : ADR11.roots (H.1.erase univ) = {B, univ \ B})
    (f : Fin A.card ≃ Fin B.card)
    (g : Fin (univ \ A).card ≃ Fin (univ \ B).card)
    (hf : forestEmbed f.toEmbedding
      (forestPreimage (cladeLabelEmbedding A) (G.1.filter (fun C => C ⊆ A))) =
      forestPreimage (cladeLabelEmbedding B) (H.1.filter (fun C => C ⊆ B)))
    (hg : forestEmbed g.toEmbedding
      (forestPreimage (cladeLabelEmbedding (univ \ A))
        (G.1.filter (fun C => C ⊆ univ \ A))) =
      forestPreimage (cladeLabelEmbedding (univ \ B))
        (H.1.filter (fun C => C ⊆ univ \ B))) :
    Combinatorics.BinaryHierarchyShapeRel n G H := by
  let e : Equiv.Perm (Fin n) :=
    (rootPartitionEquiv A).symm.trans ((Equiv.sumCongr f g).trans (rootPartitionEquiv B))
  have hl : (cladeLabelEmbedding A).trans e.toEmbedding =
      f.toEmbedding.trans (cladeLabelEmbedding B) := by
    apply Function.Embedding.ext
    intro x
    change e (cladeLabelEmbedding A x) = cladeLabelEmbedding B (f x)
    rw [← rootPartitionEquiv_inl A x]
    change rootPartitionEquiv B ((Equiv.sumCongr f g)
      ((rootPartitionEquiv A).symm (rootPartitionEquiv A (Sum.inl x)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hr : (cladeLabelEmbedding (univ \ A)).trans e.toEmbedding =
      g.toEmbedding.trans (cladeLabelEmbedding (univ \ B)) := by
    apply Function.Embedding.ext
    intro x
    change e (cladeLabelEmbedding (univ \ A) x) = cladeLabelEmbedding (univ \ B) (g x)
    rw [← rootPartitionEquiv_inr A x]
    change rootPartitionEquiv B ((Equiv.sumCongr f g)
      ((rootPartitionEquiv A).symm (rootPartitionEquiv A (Sum.inr x)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  refine ⟨e, ?_⟩
  change forestEmbed e.toEmbedding G.1 = H.1
  rw [binaryHierarchy_daughter_reconstruction n G A hs,
    forestEmbed_insert, forestEmbed_union, clade_map_equiv_univ,
    forestEmbed_comp, hl, ← forestEmbed_comp, hf,
    forestEmbed_comp, hr, ← forestEmbed_comp, hg]
  exact (binaryHierarchy_daughter_reconstruction n H B ht).symm
end Rhone.Coalescent
