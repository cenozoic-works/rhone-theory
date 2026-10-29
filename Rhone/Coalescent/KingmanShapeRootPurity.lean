/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFinalRoot
public import Rhone.Coalescent.KingmanShapeHistoryInclusion
public import Rhone.Coalescent.KingmanRootPair
/-!
# Before the final merger every clade lies within one root daughter

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem historyAt_root_split_pure (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) (k : ℕ) (hk : k ≤ n - 2) :
    ∀ C ∈ Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k, C ⊆ A ∨ C ⊆ univ \ A := by
  intro C hC
  have hp := historyAt_subset _ (ADR11.isForest_singletonForest n) (n - 1) h
    k (n - 2) hk (by omega)
  rw [historyAt_penultimate_eq_erase n hn h] at hp
  obtain ⟨hCu, hCE⟩ := mem_erase.mp (hp hC)
  rcases Combinatorics.root_split_clade_purity _ A hs C hCE with he | hleft | hright
  · exact False.elim (hCu he)
  · exact Or.inl hleft
  · exact Or.inr hright
end Rhone.Coalescent
