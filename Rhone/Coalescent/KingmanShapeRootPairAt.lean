/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootPair
/-!
# The root pair of a binary hierarchy, indexed by the root clade

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem binary_hierarchy_root_pair_at {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G) (hL : 2 ≤ Fintype.card L)
    (A : Finset L) (hA : A ∈ ADR11.roots (G.erase univ)) :
    A.Nonempty ∧ (univ \ A).Nonempty ∧ ADR11.roots (G.erase univ) = {A, univ \ A} := by
  obtain ⟨B, hB, hBc, hs⟩ := binary_hierarchy_root_pair G hG hL
  rw [hs] at hA
  rcases mem_insert.mp hA with rfl | hA
  · exact ⟨hB, hBc, hs⟩
  · obtain rfl := mem_singleton.mp hA
    have hc : univ \ (univ \ B) = B := by ext x; simp
    refine ⟨hBc, ?_, ?_⟩
    · rw [hc]
      exact hB
    · rw [hc, pair_comm]
      exact hs
end Rhone.Coalescent
