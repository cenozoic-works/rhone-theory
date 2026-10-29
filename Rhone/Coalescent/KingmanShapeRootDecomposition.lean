/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootSeparatedHistory
public import Rhone.Coalescent.KingmanShapeInterleaveEquiv
/-!
# Daughter histories and slots recovered from complete root histories

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rootHistoryDecomposition (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) :
    (Combinatorics.RankedLabelledHistory A.card × Combinatorics.RankedLabelledHistory
        (univ \ A).card) ×
      Combinatorics.HistoryInterleaving (A.card - 1) ((univ \ A).card - 1) :=
  (historyInterleaveEquiv _ _ (ADR11.isForest_singletonForest _)
    (ADR11.isForest_singletonForest _) _ _).symm (rootSeparatedHistory n hn h A hs)
theorem rootHistoryDecomposition_reconstruct (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) :
    let p := rootHistoryDecomposition n hn h A hs
    historyInterleave _ _ (ADR11.isForest_singletonForest _)
      (ADR11.isForest_singletonForest _) _ _ p.1.1 p.1.2 p.2 =
        (rootSeparatedHistory n hn h A hs).1 := by
  exact congrArg Subtype.val ((historyInterleaveEquiv _ _
    (ADR11.isForest_singletonForest _) (ADR11.isForest_singletonForest _) _ _).apply_symm_apply
      (rootSeparatedHistory n hn h A hs))
theorem historyAt_rootHistoryDecomposition (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) (k : ℕ) (hk : k ≤ n - 2) :
    let p := rootHistoryDecomposition n hn h A hs
    forestEmbed (rootPartitionEquiv A).toEmbedding
      (forestEmbed Function.Embedding.inl
        (Combinatorics.historyAt _ (A.card - 1) p.1.1 (Combinatorics.interleavingLeft p.2 k)) ∪
       forestEmbed Function.Embedding.inr
        (Combinatorics.historyAt _ ((univ \ A).card - 1) p.1.2
            (Combinatorics.interleavingRight p.2 k))) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k := by
  dsimp only
  let p := rootHistoryDecomposition n hn h A hs
  have he := rootHistoryDecomposition_reconstruct n hn h A hs
  have hlen : A.card - 1 + ((univ \ A).card - 1) = n - 2 := by
    have hG := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.2.2
    have hAr : A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_self _ _
    have hBr : univ \ A ∈
        ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) :=
            by
      rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
    have hAc := (hG.1 A (mem_erase.mp (ADR11.roots_subset _ hAr)).2).card_pos
    have hBc := (hG.1 (univ \ A) (mem_erase.mp (ADR11.roots_subset _ hBr)).2).card_pos
    have hc := rootPartition_card A
    omega
  rw [← historyAt_historyInterleave _ _ (ADR11.isForest_singletonForest _)
    (ADR11.isForest_singletonForest _) _ _ p.1.1 p.1.2 p.2 k (by omega), he]
  dsimp only [rootSeparatedHistory]
  rw [Combinatorics.historyAt_castLength]
  · exact historyAt_rootPartitionPrefix n hn h A k hk
  · exact hlen.symm
theorem rootHistoryDecomposition_unique (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (p : (Combinatorics.RankedLabelledHistory A.card × Combinatorics.RankedLabelledHistory
        (univ \ A).card) ×
      Combinatorics.HistoryInterleaving (A.card - 1) ((univ \ A).card - 1))
    (hp : historyInterleave _ _ (ADR11.isForest_singletonForest _)
      (ADR11.isForest_singletonForest _) _ _ p.1.1 p.1.2 p.2 =
        (rootSeparatedHistory n hn h A hs).1) :
    p = rootHistoryDecomposition n hn h A hs := by
  apply historyInterleave_injective _ _ (ADR11.isForest_singletonForest _)
    (ADR11.isForest_singletonForest _) _ _
  exact hp.trans (rootHistoryDecomposition_reconstruct n hn h A hs).symm
end Rhone.Coalescent
