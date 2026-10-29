/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeFirstMerger
public import Rhone.Coalescent.KingmanShapeRootPurity
/-!
# The first chronological merger canonically selects one root daughter

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem firstMergerRoot_exists (n : ℕ) (hn : 3 ≤ n) (h : Combinatorics.RankedLabelledHistory n) :
    ∃ A : Finset (Fin n), A ∈ ADR11.roots
      ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) ∧
      Combinatorics.firstMergerClade n (by omega) h ⊆ A := by
  obtain ⟨A, _, _, hs⟩ := binary_hierarchy_root_pair _
    (Combinatorics.historyEnd_isBinaryHierarchy n
        (by omega) h) (by simpa using (show 2 ≤ n by omega))
  have hD : Combinatorics.firstMergerClade n (by omega) h ∈
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h 1 := by
    rw [(Combinatorics.firstMergerClade_spec n (by omega) h).2]
    exact mem_insert_self _ _
  rcases historyAt_root_split_pure n (by omega) h A hs 1 (by omega) _ hD with hL | hR
  · exact ⟨A, by rw [hs]; exact mem_insert_self _ _, hL⟩
  · exact ⟨univ \ A, by rw [hs]; exact mem_insert_of_mem (mem_singleton_self _), hR⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def firstMergerRoot (n : ℕ) (hn : 3 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) : Finset (Fin n) :=
  Classical.choose (firstMergerRoot_exists n hn h)
theorem firstMergerRoot_spec (n : ℕ) (hn : 3 ≤ n) (h : Combinatorics.RankedLabelledHistory n) :
    firstMergerRoot n hn h ∈ ADR11.roots
      ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) ∧
    Combinatorics.firstMergerClade n (by omega) h ⊆ firstMergerRoot n hn h :=
  Classical.choose_spec (firstMergerRoot_exists n hn h)
theorem firstMergerRoot_unique (n : ℕ) (hn : 3 ≤ n) (h : Combinatorics.RankedLabelledHistory n)
    (A : Finset (Fin n))
    (hA : A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ))
    (hD : Combinatorics.firstMergerClade n (by omega) h ⊆ A) : firstMergerRoot n hn h = A := by
  have he := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.2.2
  have hf : ADR11.IsForest
      ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) :=
    ⟨fun C hC => he.1 C (mem_erase.mp hC).2,
      fun C hC D hD => he.2 C (mem_erase.mp hC).2 D (mem_erase.mp hD).2⟩
  have hp := firstMergerRoot_spec n hn h
  have hne : (Combinatorics.firstMergerClade n (by omega) h).Nonempty := by
    rw [← card_pos, (Combinatorics.firstMergerClade_spec n (by omega) h).1]
    omega
  obtain ⟨x, hx⟩ := hne
  exact hf.eq_of_mem_roots_of_mem hp.1 hA (hp.2 hx) (hD hx)
theorem firstMergerRoot_card (n : ℕ) (hn : 3 ≤ n) (h : Combinatorics.RankedLabelledHistory n) :
    2 ≤ (firstMergerRoot n hn h).card := by
  have hc := card_le_card (firstMergerRoot_spec n hn h).2
  rwa [(Combinatorics.firstMergerClade_spec n (by omega) h).1] at hc
end Rhone.Coalescent
