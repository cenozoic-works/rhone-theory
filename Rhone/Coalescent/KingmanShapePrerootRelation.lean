/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootAssemblyRoot
/-!
# Extend chronological relabelling through the final root merger

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem rankedShapeRel_of_preroot (n : ℕ) (hn : 2 ≤ n)
    (h g : Combinatorics.RankedLabelledHistory n) (e : Equiv.Perm (Fin n))
    (he : ∀ r ≤ n - 2, Combinatorics.forestRelabel e
      (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h r) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) g r) : Combinatorics.RankedShapeRel
          n h g := by
  refine ⟨e, ?_⟩
  intro r hr
  by_cases hpr : r ≤ n - 2
  · exact he r hpr
  · have hrt : r = n - 1 := by omega
    subst r
    rw [historyAt_terminal, historyAt_terminal]
    have hp := he (n - 2) le_rfl
    rw [historyAt_penultimate_eq_erase n hn h, historyAt_penultimate_eq_erase n hn g] at hp
    have hfull := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.1
    have gfull := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) g).1.1
    change forestEmbed e.toEmbedding _ = _ at hp ⊢
    have hu := clade_map_equiv_univ e
    calc
      forestEmbed e.toEmbedding (Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h) =
          forestEmbed e.toEmbedding (insert univ
            ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ)) := by
              rw [insert_erase hfull]
      _ = insert univ ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) g).erase univ) :=
          by
        rw [forestEmbed_insert, hu, hp]
      _ = Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) g := insert_erase gfull
end Rhone.Coalescent
