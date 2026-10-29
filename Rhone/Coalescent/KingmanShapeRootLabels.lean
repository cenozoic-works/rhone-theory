/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanTopologySubtree
/-!
# Tagged partition of the leaf labels into the two root daughter label sets

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem shape_clade_embedding_mem {n : ℕ} (A : Finset (Fin n)) (x : Fin A.card) :
    cladeLabelEmbedding A x ∈ A := by
  exact (A.equivFin.symm x).2
noncomputable def rootPartitionEquiv {n : ℕ} (A : Finset (Fin n)) :
    Fin A.card ⊕ Fin (univ \ A).card ≃ Fin n := by
  apply Equiv.ofBijective (Sum.elim (cladeLabelEmbedding A) (cladeLabelEmbedding (univ \ A)))
  constructor
  · intro x y he
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl ((cladeLabelEmbedding A).injective he)
    · have he' : cladeLabelEmbedding A x = cladeLabelEmbedding (univ \ A) y := he
      have hx := shape_clade_embedding_mem A x
      have hy := (mem_sdiff.mp (shape_clade_embedding_mem (univ \ A) y)).2
      exact False.elim (hy (he' ▸ hx))
    · have he' : cladeLabelEmbedding (univ \ A) x = cladeLabelEmbedding A y := he
      have hx := (mem_sdiff.mp (shape_clade_embedding_mem (univ \ A) x)).2
      have hy := shape_clade_embedding_mem A y
      exact False.elim (hx (he'.symm ▸ hy))
    · exact congrArg Sum.inr ((cladeLabelEmbedding (univ \ A)).injective he)
  · intro x
    by_cases hx : x ∈ A
    · rw [← cladeLabelEmbedding_range A] at hx
      obtain ⟨y, _, he⟩ := mem_map.mp hx
      exact ⟨Sum.inl y, he⟩
    · have hc : x ∈ univ \ A := mem_sdiff.mpr ⟨mem_univ _, hx⟩
      rw [← cladeLabelEmbedding_range (univ \ A)] at hc
      obtain ⟨y, _, he⟩ := mem_map.mp hc
      exact ⟨Sum.inr y, he⟩
theorem rootPartitionEquiv_inl {n : ℕ} (A : Finset (Fin n)) (x : Fin A.card) :
    rootPartitionEquiv A (Sum.inl x) = cladeLabelEmbedding A x := rfl
theorem rootPartitionEquiv_inr {n : ℕ} (A : Finset (Fin n)) (x : Fin (univ \ A).card) :
    rootPartitionEquiv A (Sum.inr x) = cladeLabelEmbedding (univ \ A) x := rfl
end Rhone.Coalescent
