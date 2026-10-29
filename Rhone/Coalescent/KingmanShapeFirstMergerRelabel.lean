/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFirstRoot
public import Rhone.Coalescent.KingmanShapeHistoryRelabel
public import Rhone.Coalescent.KingmanShapeForestEmbedLaws
/-!
# The first-merger root orientation is invariant under chronological relabelling

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem firstMergerClade_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (e : Equiv.Perm (Fin n))
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k) :
    (Combinatorics.firstMergerClade n hn h).map e.toEmbedding = Combinatorics.firstMergerClade n hn
        h' := by
  have hfirst := he 1 (by omega)
  change forestEmbed e.toEmbedding (Combinatorics.historyAt _ (n - 1) h 1) = Combinatorics.historyAt
      _ (n - 1) h' 1 at hfirst
  rw [(Combinatorics.firstMergerClade_spec n hn h).2, forestEmbed_insert,
    forestEmbed_singletonForest_perm, (Combinatorics.firstMergerClade_spec n hn h').2] at hfirst
  apply Combinatorics.firstMergerClade_insert_unique n _ _ _
      (Combinatorics.firstMergerClade_spec n hn h').1 hfirst
  rw [card_map, (Combinatorics.firstMergerClade_spec n hn h).1]
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem firstMergerRoot_map (n : ℕ) (hn : 3 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (e : Equiv.Perm (Fin n))
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k) :
    (firstMergerRoot n hn h).map e.toEmbedding = firstMergerRoot n hn h' := by
  have hend := he (n - 1) le_rfl
  rw [historyAt_terminal, historyAt_terminal] at hend
  change forestEmbed e.toEmbedding (Combinatorics.historyEnd _ (n - 1) h) = Combinatorics.historyEnd
      _ (n - 1) h' at hend
  have hp := firstMergerRoot_spec n hn h
  have hproper : forestEmbed e.toEmbedding ((Combinatorics.historyEnd _ (n - 1) h).erase univ) =
      (Combinatorics.historyEnd _ (n - 1) h').erase univ := by
    rw [forestEmbed_erase, hend, clade_map_equiv_univ]
  have hr : (firstMergerRoot n hn h).map e.toEmbedding ∈
      ADR11.roots ((Combinatorics.historyEnd _ (n - 1) h').erase univ) := by
    rw [← hproper, roots_forestEmbed]
    exact mem_image.mpr ⟨_, hp.1, rfl⟩
  apply (firstMergerRoot_unique n hn h' _ hr ?_).symm
  rw [← firstMergerClade_map n (by omega) h h' e he]
  exact map_subset_map.mpr hp.2
end Rhone.Coalescent
