/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanHistoryPayoff
/-! # Reconstruction of endpoints from their retained root subtrees -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem root_split_endpoint_reconstruction {L : Type*} [Fintype L] [DecidableEq L]
    (G T : Finset (Finset L)) (A : Finset L) (hG : univ ∈ G) (hT : univ ∈ T)
    (hsG : ADR11.roots (G.erase univ) = {A, univ \ A})
    (hsT : ADR11.roots (T.erase univ) = {A, univ \ A})
    (ha : G.filter (fun C => C ⊆ A) = T.filter (fun C => C ⊆ A))
    (hb : G.filter (fun C => C ⊆ univ \ A) = T.filter (fun C => C ⊆ univ \ A)) : G = T := by
  have forward : ∀ C ∈ G, C ∈ T := by
    intro C hC
    rcases Combinatorics.root_split_clade_purity G A hsG C hC with rfl | hCA | hCB
    · exact hT
    · have hm : C ∈ G.filter (fun D => D ⊆ A) := mem_filter.mpr ⟨hC, hCA⟩
      rw [ha] at hm
      exact (mem_filter.mp hm).1
    · have hm : C ∈ G.filter (fun D => D ⊆ univ \ A) := mem_filter.mpr ⟨hC, hCB⟩
      rw [hb] at hm
      exact (mem_filter.mp hm).1
  have backward : ∀ C ∈ T, C ∈ G := by
    intro C hC
    rcases Combinatorics.root_split_clade_purity T A hsT C hC with rfl | hCA | hCB
    · exact hG
    · have hm : C ∈ T.filter (fun D => D ⊆ A) := mem_filter.mpr ⟨hC, hCA⟩
      rw [← ha] at hm
      exact (mem_filter.mp hm).1
    · have hm : C ∈ T.filter (fun D => D ⊆ univ \ A) := mem_filter.mpr ⟨hC, hCB⟩
      rw [← hb] at hm
      exact (mem_filter.mp hm).1
  exact subset_antisymm forward backward
end Rhone.Coalescent
