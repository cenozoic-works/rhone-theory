/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryProjection
public import Rhone.Combinatorics.KingmanHistoryTopology
/-!
# The full root clade appears precisely at the final merger

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem historyAt_full_iff_terminal (n : ℕ) (hn : 1 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (k : ℕ) (hk : k ≤ n - 1) :
    univ ∈ Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k ↔ k = n - 1 := by
  constructor
  · intro hu
    have hr : ADR11.roots (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
        {univ} := by
      ext A
      constructor
      · intro hA
        exact mem_singleton.mpr ((ADR11.mem_roots.mp hA).2 univ hu (subset_univ A)).symm
      · intro hA
        obtain rfl := mem_singleton.mp hA
        apply ADR11.mem_roots.mpr
        refine ⟨hu, ?_⟩
        intro B _ hUB
        exact subset_antisymm (subset_univ B) hUB
    have hc := historyAt_root_count _ (ADR11.isForest_singletonForest n) (n - 1) h k hk
    rw [hr, card_singleton, ADR11.card_roots_singletonForest] at hc
    omega
  · rintro rfl
    rw [historyAt_terminal]
    exact (Combinatorics.historyEnd_isBinaryHierarchy n hn h).1.1
theorem historyAt_penultimate_eq_erase (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) :
    Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h (n - 2) =
      (Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ := by
  have hnext := Combinatorics.historyAt_next_merge (ADR11.singletonForest n) (n - 1) h (n - 2)
      (by omega)
  have hnum : n - 2+1 = n - 1 := by omega
  rw [hnum, historyAt_terminal] at hnext
  have hnot : univ ∉ Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h (n - 2) := by
    rw [historyAt_full_iff_terminal n (by omega) h (n - 2) (by omega)]
    omega
  obtain ⟨B, _, C, _, _, he⟩ := ADR11.mem_merges.mp hnext
  have hroot := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.1
  rw [he] at hroot
  have hBC : B ∪ C = univ := ((mem_insert.mp hroot).resolve_right hnot).symm
  rw [he, hBC, erase_insert hnot]
end Rhone.Coalescent
