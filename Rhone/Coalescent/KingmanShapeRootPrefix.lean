/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSumSingletons
public import Rhone.Coalescent.KingmanShapeHistoryLabels
public import Rhone.Coalescent.KingmanShapeHistoryTake
public import Rhone.Coalescent.KingmanShapeFinalRoot
/-!
# Retain the pre-root chronology on the daughter label partition

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
abbrev rootSumForest {n : ℕ} (A : Finset (Fin n)) :
    Finset (Finset (Fin A.card ⊕ Fin (univ \ A).card)) :=
  forestEmbed Function.Embedding.inl (ADR11.singletonForest A.card) ∪
    forestEmbed Function.Embedding.inr (ADR11.singletonForest (univ \ A).card)
noncomputable def rootPartitionPrefix (n : ℕ) (_hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n)) :
    Combinatorics.RankedForestHistory (rootSumForest A) (n - 2) :=
  (historyLabelsEquiv (rootPartitionEquiv A) (rootSumForest A) (ADR11.singletonForest n)
    (singletonForest_sum_embed _ _ n (rootPartitionEquiv A)) (n - 2)).symm
    (historyTake (ADR11.singletonForest n) (n - 1) h (n - 2) (by omega))
theorem historyAt_rootPartitionPrefix (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n)) (k : ℕ) (hk : k ≤ n - 2) :
    forestEmbed (rootPartitionEquiv A).toEmbedding
      (Combinatorics.historyAt (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A) k) =
        Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k := by
  have he := historyAt_historyLabelsEquiv_symm (rootPartitionEquiv A) (rootSumForest A)
    (ADR11.singletonForest n) (singletonForest_sum_embed _ _ n (rootPartitionEquiv A))
    (n - 2) (historyTake (ADR11.singletonForest n) (n - 1) h (n - 2) (by omega)) k
  rwa [historyAt_historyTake _ _ _ _ _ k hk] at he
theorem historyEnd_rootPartitionPrefix (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n)) :
    forestEmbed (rootPartitionEquiv A).toEmbedding
        (Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A)) =
      (Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ := by
  rw [← historyAt_terminal, historyAt_rootPartitionPrefix _ _ _ _ _ le_rfl,
    historyAt_penultimate_eq_erase n hn h]
end Rhone.Coalescent
