/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeHistoryTrace
/-!
# The first merger of a ranked history adds exactly one two-leaf clade

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem firstMergerClade_exists (n : ℕ) (hn : 2 ≤ n) (h : RankedLabelledHistory n) :
    ∃ D : Finset (Fin n), D.card = 2 ∧
      historyAt (ADR11.singletonForest n) (n - 1) h 1 = insert D (ADR11.singletonForest n) := by
  have hm := historyAt_next_merge (ADR11.singletonForest n) (n - 1) h 0 (by omega)
  rw [historyAt_zero] at hm
  obtain ⟨B, hB, C, hC, hBC, he⟩ := ADR11.mem_merges.mp hm
  rw [ADR11.roots_singletonForest] at hB hC
  obtain ⟨x, _, rfl⟩ := mem_image.mp hB
  obtain ⟨y, _, rfl⟩ := mem_image.mp hC
  have hxy : x ≠ y := fun hxy => hBC (congrArg singleton hxy)
  exact ⟨{x, y}, card_pair hxy, by simpa only [singleton_union] using he⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def firstMergerClade (n : ℕ) (hn : 2 ≤ n)
    (h : RankedLabelledHistory n) : Finset (Fin n) :=
  Classical.choose (firstMergerClade_exists n hn h)
theorem firstMergerClade_spec (n : ℕ) (hn : 2 ≤ n)
    (h : RankedLabelledHistory n) :
    (firstMergerClade n hn h).card = 2 ∧
    historyAt (ADR11.singletonForest n) (n - 1) h 1 =
      insert (firstMergerClade n hn h) (ADR11.singletonForest n) :=
  Classical.choose_spec (firstMergerClade_exists n hn h)
theorem two_leaf_clade_not_singletonForest (n : ℕ) (D : Finset (Fin n)) (hD : D.card = 2) :
    D ∉ ADR11.singletonForest n := by
  intro hm
  obtain ⟨x, _, rfl⟩ := mem_image.mp hm
  rw [card_singleton] at hD
  omega
theorem firstMergerClade_insert_unique (n : ℕ) (D E : Finset (Fin n))
    (hD : D.card = 2) (_hE : E.card = 2)
    (he : insert D (ADR11.singletonForest n) = insert E (ADR11.singletonForest n)) : D = E := by
  have hm : D ∈ insert E (ADR11.singletonForest n) := he ▸ mem_insert_self D _
  exact (mem_insert.mp hm).resolve_right (two_leaf_clade_not_singletonForest n D hD)
end Rhone.Combinatorics
