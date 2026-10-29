/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootDescent
/-!
# Recovered daughter shape classes descend under the ranked relation

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem rankedShape_sigma_eq_of_forest_map (m n : ℕ) (hmn : m = n)
    (h : Combinatorics.RankedLabelledHistory m) (g : Combinatorics.RankedLabelledHistory n)
    (e : Fin m ≃ Fin n)
    (he : ∀ j ≤ m - 1, forestEmbed e.toEmbedding
      (Combinatorics.historyAt (ADR11.singletonForest m) (m - 1) h j) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) g j) :
    (⟨m, Quotient.mk (Combinatorics.rankedShapeSetoid m) h⟩ : Σ k, Combinatorics.RankedShape k) =
      ⟨n, Quotient.mk (Combinatorics.rankedShapeSetoid n) g⟩ := by
  subst n
  apply congrArg (Sigma.mk m)
  apply Quotient.sound
  exact ⟨e, he⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_left_shape_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k) :
    (⟨A.card, Quotient.mk (Combinatorics.rankedShapeSetoid A.card)
      (rootHistoryDecomposition n hn h A hs).1.1⟩ : Σ k, Combinatorics.RankedShape k) =
    ⟨B.card, Quotient.mk (Combinatorics.rankedShapeSetoid B.card)
      (rootHistoryDecomposition n hn h' B hs').1.1⟩ := by
  apply rankedShape_sigma_eq_of_forest_map _ _ (cladeRelabel_card n e A B hAB)
    _ _ (cladeRelabelEquiv n e A B hAB)
  exact rootHistoryDecomposition_left_rank_map n hn h h' A B hs hs' e hAB he
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_right_shape_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k) :
    (⟨(univ \ A).card, Quotient.mk (Combinatorics.rankedShapeSetoid (univ \ A).card)
      (rootHistoryDecomposition n hn h A hs).1.2⟩ : Σ k, Combinatorics.RankedShape k) =
    ⟨(univ \ B).card, Quotient.mk (Combinatorics.rankedShapeSetoid (univ \ B).card)
      (rootHistoryDecomposition n hn h' B hs').1.2⟩ := by
  apply rankedShape_sigma_eq_of_forest_map _ _ (cladeRelabel_card n e (univ \ A) (univ \ B)
    (by rw [Finset.map_sdiff, clade_map_equiv_univ, hAB]))
    _ _ (cladeRelabelEquiv n e (univ \ A) (univ \ B)
      (by rw [Finset.map_sdiff, clade_map_equiv_univ, hAB]))
  exact rootHistoryDecomposition_right_rank_map n hn h h' A B hs hs' e hAB he
end Rhone.Coalescent
