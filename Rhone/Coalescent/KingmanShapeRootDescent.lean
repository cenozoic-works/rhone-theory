/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootRetained
/-!
# Leaf relabellings preserve the recovered daughter chronology

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem rootHistoryDecomposition_left_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k)
    (k : ℕ) (hk : k ≤ n - 2) :
    let p := rootHistoryDecomposition n hn h A hs
    let q := rootHistoryDecomposition n hn h' B hs'
    forestEmbed (cladeRelabelEquiv n e A B hAB).toEmbedding
      (Combinatorics.historyAt _ (A.card - 1) p.1.1 (Combinatorics.interleavingLeft p.2 k)) =
      Combinatorics.historyAt _ (B.card - 1) q.1.1 (Combinatorics.interleavingLeft q.2 k) := by
  dsimp only
  rw [← rootHistoryDecomposition_left_retained n hn h A hs k hk,
    ← retainedSubtree_relabel n e A B hAB]
  have hek := he k (by omega)
  change forestEmbed e.toEmbedding _ = _ at hek
  rw [hek,
    rootHistoryDecomposition_left_retained n hn h' B hs' k hk]
theorem rootHistoryDecomposition_left_counter_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k)
    (k : ℕ) (hk : k ≤ n - 2) :
    Combinatorics.interleavingLeft (rootHistoryDecomposition n hn h A hs).2 k =
      Combinatorics.interleavingLeft (rootHistoryDecomposition n hn h' B hs').2 k := by
  let p := rootHistoryDecomposition n hn h A hs
  let q := rootHistoryDecomposition n hn h' B hs'
  have hf := rootHistoryDecomposition_left_map n hn h h' A B hs hs' e hAB he k hk
  have hc := congrArg (fun W => (ADR11.roots W).card) hf
  rw [card_roots_forestEmbed] at hc
  have hp := historyAt_root_count _ (ADR11.isForest_singletonForest A.card)
    (A.card - 1) p.1.1 _ (Combinatorics.interleavingLeft_le p.2 k)
  have hq := historyAt_root_count _ (ADR11.isForest_singletonForest B.card)
    (B.card - 1) q.1.1 _ (Combinatorics.interleavingLeft_le q.2 k)
  rw [ADR11.card_roots_singletonForest] at hp hq
  have hcard := cladeRelabel_card n e A B hAB
  dsimp only [p, q] at hp hq
  omega
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_left_rank_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k)
    (j : ℕ) (hj : j ≤ A.card - 1) :
    forestEmbed (cladeRelabelEquiv n e A B hAB).toEmbedding
      (Combinatorics.historyAt _ (A.card - 1) (rootHistoryDecomposition n hn h A hs).1.1 j) =
      Combinatorics.historyAt _ (B.card - 1) (rootHistoryDecomposition n hn h' B hs').1.1 j := by
  let p := rootHistoryDecomposition n hn h A hs
  obtain ⟨k, hk, hkj⟩ := Combinatorics.interleavingLeft_range p.2 j hj
  have hlen : A.card - 1 + ((univ \ A).card - 1) = n - 2 := by
    have hG := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.2.2
    have hAr : A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_self _ _
    have hBr : univ \ A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
    have hAc := (hG.1 A (mem_erase.mp (ADR11.roots_subset _ hAr)).2).card_pos
    have hBc := (hG.1 (univ \ A) (mem_erase.mp (ADR11.roots_subset _ hBr)).2).card_pos
    have hc := rootPartition_card A
    omega
  have hk' : k ≤ n - 2 := by omega
  have hf := rootHistoryDecomposition_left_map n hn h h' A B hs hs' e hAB he k hk'
  have hc := rootHistoryDecomposition_left_counter_map n hn h h' A B hs hs' e hAB he k hk'
  dsimp only [p] at hkj
  dsimp only at hf
  rw [← hc, hkj] at hf
  exact hf
theorem rootHistoryDecomposition_right_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k)
    (k : ℕ) (hk : k ≤ n - 2) :
    let p := rootHistoryDecomposition n hn h A hs
    let q := rootHistoryDecomposition n hn h' B hs'
    forestEmbed (cladeRelabelEquiv n e (univ \ A) (univ \ B)
      (by rw [Finset.map_sdiff, clade_map_equiv_univ, hAB])).toEmbedding
      (Combinatorics.historyAt _ ((univ \ A).card - 1) p.1.2
          (Combinatorics.interleavingRight p.2 k)) =
      Combinatorics.historyAt _ ((univ \ B).card - 1) q.1.2
          (Combinatorics.interleavingRight q.2 k) := by
  dsimp only
  rw [← rootHistoryDecomposition_right_retained n hn h A hs k hk,
    ← retainedSubtree_relabel n e (univ \ A) (univ \ B)
      (by rw [Finset.map_sdiff, clade_map_equiv_univ, hAB])]
  have hek := he k (by omega)
  change forestEmbed e.toEmbedding _ = _ at hek
  rw [hek,
    rootHistoryDecomposition_right_retained n hn h' B hs' k hk]
theorem rootHistoryDecomposition_right_counter_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k)
    (k : ℕ) (hk : k ≤ n - 2) :
    Combinatorics.interleavingRight (rootHistoryDecomposition n hn h A hs).2 k =
      Combinatorics.interleavingRight (rootHistoryDecomposition n hn h' B hs').2 k := by
  let p := rootHistoryDecomposition n hn h A hs
  let q := rootHistoryDecomposition n hn h' B hs'
  have hf := rootHistoryDecomposition_right_map n hn h h' A B hs hs' e hAB he k hk
  have hc := congrArg (fun W => (ADR11.roots W).card) hf
  rw [card_roots_forestEmbed] at hc
  have hp := historyAt_root_count _ (ADR11.isForest_singletonForest (univ \ A).card)
    ((univ \ A).card - 1) p.1.2 _ (Combinatorics.interleavingRight_le p.2 k)
  have hq := historyAt_root_count _ (ADR11.isForest_singletonForest (univ \ B).card)
    ((univ \ B).card - 1) q.1.2 _ (Combinatorics.interleavingRight_le q.2 k)
  rw [ADR11.card_roots_singletonForest] at hp hq
  have hcard := cladeRelabel_card n e (univ \ A) (univ \ B)
    (by rw [Finset.map_sdiff, clade_map_equiv_univ, hAB])
  dsimp only [p, q] at hp hq
  omega
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_right_rank_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k)
    (j : ℕ) (hj : j ≤ (univ \ A).card - 1) :
    forestEmbed (cladeRelabelEquiv n e (univ \ A) (univ \ B)
      (by rw [Finset.map_sdiff, clade_map_equiv_univ, hAB])).toEmbedding
      (Combinatorics.historyAt _ ((univ \ A).card - 1) (rootHistoryDecomposition n hn h A hs).1.2
          j) =
      Combinatorics.historyAt _ ((univ \ B).card - 1) (rootHistoryDecomposition n hn h' B hs').1.2
          j := by
  let p := rootHistoryDecomposition n hn h A hs
  obtain ⟨k, hk, hkj⟩ := Combinatorics.interleavingRight_range p.2 j hj
  have hlen : A.card - 1 + ((univ \ A).card - 1) = n - 2 := by
    have hG := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.2.2
    have hAr : A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_self _ _
    have hBr : univ \ A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
    have hAc := (hG.1 A (mem_erase.mp (ADR11.roots_subset _ hAr)).2).card_pos
    have hBc := (hG.1 (univ \ A) (mem_erase.mp (ADR11.roots_subset _ hBr)).2).card_pos
    have hc := rootPartition_card A
    omega
  have hk' : k ≤ n - 2 := by omega
  have hf := rootHistoryDecomposition_right_map n hn h h' A B hs hs' e hAB he k hk'
  have hc := rootHistoryDecomposition_right_counter_map n hn h h' A B hs hs' e hAB he k hk'
  dsimp only [p] at hkj
  dsimp only at hf
  rw [← hc, hkj] at hf
  exact hf
end Rhone.Coalescent
