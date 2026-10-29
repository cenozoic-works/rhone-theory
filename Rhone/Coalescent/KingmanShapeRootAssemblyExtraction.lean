/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootAssemblyRoot
public import Rhone.Coalescent.KingmanShapeRootRetained
public import Rhone.Coalescent.KingmanShapeRootQuotientDescent
public import Rhone.Coalescent.KingmanShapeSlotImage
/-!
# Recover daughter shape classes and slots from assembled histories

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def cladeEmbeddingEquiv {a n : ℕ} (f : Fin a ↪ Fin n)
    (A : Finset (Fin n)) (hf : univ.map f = A) : Fin a ≃ Fin A.card := by
  let q : Fin a ≃ A := Equiv.ofBijective (fun x => ⟨f x, by
    rw [← hf]; exact mem_map.mpr ⟨x, mem_univ _, rfl⟩⟩) ⟨by
      intro x y he
      exact f.injective (congrArg Subtype.val he), by
      intro x
      have hx : x.val ∈ univ.map f := by simpa only [hf] using x.property
      obtain ⟨y, _, hy⟩ := mem_map.mp hx
      exact ⟨y, Subtype.ext hy⟩⟩
  exact q.trans A.equivFin
theorem cladeEmbeddingEquiv_embedding {a n : ℕ} (f : Fin a ↪ Fin n)
    (A : Finset (Fin n)) (hf : univ.map f = A) (x : Fin a) :
    cladeLabelEmbedding A (cladeEmbeddingEquiv f A hf x) = f x := by
  unfold cladeEmbeddingEquiv
  change (A.equivFin.symm (A.equivFin _)).val = _
  rw [Equiv.symm_apply_apply]
  rfl
theorem rootHistoryDecomposition_assembly_left (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hA : ((univ : Finset (Fin k.val)).map Function.Embedding.inl).map
      (firstRootAssemblyLabels n k).toEmbedding = A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
    (r : ℕ) (hr : r ≤ n - 2) :
    let p := rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs
    forestEmbed (cladeLabelEmbedding A)
      (Combinatorics.historyAt _ (A.card - 1) p.1.1 (Combinatorics.interleavingLeft p.2 r)) =
    forestEmbed ((Function.Embedding.inl : Fin k.val ↪ Fin k.val ⊕ Fin (n - k.val)).trans
      (firstRootAssemblyLabels n k).toEmbedding)
      (Combinatorics.historyAt _ (k.val - 1) h (Combinatorics.interleavingLeft s.1 r)) := by
  dsimp only
  rw [← rootHistoryDecomposition_left_retained n (by omega) _ A hs r hr]
  rw [forestEmbed_forestPreimage _ _ (by
    intro C hC
    rw [cladeLabelEmbedding_range]
    exact (mem_filter.mp hC).2)]
  rw [historyAt_firstRootHistoryAssemble n hn k h g s r hr,
    ← forestEmbed_filter_clade _ _ A hA]
  rw [← forestEmbed_comp]
  congr 1
  have hproj := history_sum_left_projection
    (Combinatorics.historyAt _ (k.val - 1) h (Combinatorics.interleavingLeft s.1 r))
    (Combinatorics.historyAt _ (n - k.val - 1) g (Combinatorics.interleavingRight s.1 r))
    (historyAt_isForest _ (ADR11.isForest_singletonForest _) _ g _)
  have he := congrArg
    (forestEmbed (Function.Embedding.inl : Fin k.val ↪ Fin k.val ⊕ Fin (n - k.val))) hproj
  rw [forestEmbed_forestPreimage _ _ (by intro C hC; exact (mem_filter.mp hC).2)] at he
  exact he
theorem rootHistoryDecomposition_assembly_left_counter (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hA : ((univ : Finset (Fin k.val)).map Function.Embedding.inl).map
      (firstRootAssemblyLabels n k).toEmbedding = A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
    (r : ℕ) (hr : r ≤ n - 2) :
    let p := rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs
    Combinatorics.interleavingLeft p.2 r = Combinatorics.interleavingLeft s.1 r := by
  dsimp only
  have he := rootHistoryDecomposition_assembly_left n hn k h g s A hA hs r hr
  have hc := congrArg (fun W => (ADR11.roots W).card) he
  rw [card_roots_forestEmbed, card_roots_forestEmbed] at hc
  have hp := historyAt_root_count _ (ADR11.isForest_singletonForest A.card) _
    (rootHistoryDecomposition n (by omega) (firstRootHistoryAssemble n hn k h g s) A hs).1.1
    _ (Combinatorics.interleavingLeft_le (rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs).2 r)
  have hh := historyAt_root_count _ (ADR11.isForest_singletonForest k.val) _ h
    _ (Combinatorics.interleavingLeft_le s.1 r)
  rw [ADR11.card_roots_singletonForest] at hp hh
  have hcard : A.card = k.val := by
    rw [← hA, card_map, card_map, card_univ, Fintype.card_fin]
  omega
theorem rootHistoryDecomposition_assembly_right (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hB : ((univ : Finset (Fin (n - k.val))).map Function.Embedding.inr).map
      (firstRootAssemblyLabels n k).toEmbedding = univ \ A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
    (r : ℕ) (hr : r ≤ n - 2) :
    let p := rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs
    forestEmbed (cladeLabelEmbedding (univ \ A))
      (Combinatorics.historyAt _ ((univ \ A).card - 1) p.1.2
          (Combinatorics.interleavingRight p.2 r)) =
    forestEmbed ((Function.Embedding.inr : Fin (n - k.val) ↪ Fin k.val ⊕ Fin (n - k.val)).trans
      (firstRootAssemblyLabels n k).toEmbedding)
      (Combinatorics.historyAt _ (n - k.val - 1) g (Combinatorics.interleavingRight s.1 r)) := by
  dsimp only
  rw [← rootHistoryDecomposition_right_retained n (by omega) _ A hs r hr]
  rw [forestEmbed_forestPreimage _ _ (by
    intro C hC
    rw [cladeLabelEmbedding_range]
    exact (mem_filter.mp hC).2)]
  rw [historyAt_firstRootHistoryAssemble n hn k h g s r hr,
    ← forestEmbed_filter_clade _ _ (univ \ A) hB]
  rw [← forestEmbed_comp]
  congr 1
  have hproj := history_sum_right_projection
    (Combinatorics.historyAt _ (k.val - 1) h (Combinatorics.interleavingLeft s.1 r))
    (Combinatorics.historyAt _ (n - k.val - 1) g (Combinatorics.interleavingRight s.1 r))
    (historyAt_isForest _ (ADR11.isForest_singletonForest _) _ h _)
  have he := congrArg
    (forestEmbed (Function.Embedding.inr : Fin (n - k.val) ↪ Fin k.val ⊕ Fin (n - k.val))) hproj
  rw [forestEmbed_forestPreimage _ _ (by intro C hC; exact (mem_filter.mp hC).2)] at he
  exact he
theorem rootHistoryDecomposition_assembly_left_shape (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hA : ((univ : Finset (Fin k.val)).map Function.Embedding.inl).map
      (firstRootAssemblyLabels n k).toEmbedding = A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
 :
    (⟨A.card, Quotient.mk (Combinatorics.rankedShapeSetoid A.card)
      (rootHistoryDecomposition n (by omega)
        (firstRootHistoryAssemble n hn k h g s) A hs).1.1⟩ : Σ a, Combinatorics.RankedShape a) =
      ⟨k.val, Quotient.mk (Combinatorics.rankedShapeSetoid k.val) h⟩ := by
  let f : Fin k.val ↪ Fin n := Function.Embedding.inl.trans
    (firstRootAssemblyLabels n k).toEmbedding
  have hf : univ.map f = A := by rw [← map_map]; exact hA
  let e := cladeEmbeddingEquiv f A hf
  have hem : e.toEmbedding.trans (cladeLabelEmbedding A) = f :=
    Function.Embedding.ext (cladeEmbeddingEquiv_embedding f A hf)
  symm
  apply rankedShape_sigma_eq_of_forest_map k.val A.card (by
    rw [← hf, card_map, card_univ, Fintype.card_fin]) h _ e
  intro j hj
  obtain ⟨r, hr, hrj⟩ := Combinatorics.interleavingLeft_range s.1 j hj
  have hnr : r ≤ n - 2 := by have hk := mem_Ico.mp k.property; omega
  have he := rootHistoryDecomposition_assembly_left n hn k h g s A hA hs r hnr
  have hc := rootHistoryDecomposition_assembly_left_counter n hn k h g s A hA hs r hnr
  dsimp only at he hc
  rw [hc, hrj] at he
  apply forestEmbed_injective (cladeLabelEmbedding A)
  rw [forestEmbed_comp, hem]
  exact he.symm
theorem rootHistoryDecomposition_assembly_right_counter (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hB : ((univ : Finset (Fin (n - k.val))).map Function.Embedding.inr).map
      (firstRootAssemblyLabels n k).toEmbedding = univ \ A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
    (r : ℕ) (hr : r ≤ n - 2) :
    let p := rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs
    Combinatorics.interleavingRight p.2 r = Combinatorics.interleavingRight s.1 r := by
  dsimp only
  have he := rootHistoryDecomposition_assembly_right n hn k h g s A hB hs r hr
  have hc := congrArg (fun W => (ADR11.roots W).card) he
  rw [card_roots_forestEmbed, card_roots_forestEmbed] at hc
  have hp := historyAt_root_count _ (ADR11.isForest_singletonForest (univ \ A).card) _
    (rootHistoryDecomposition n (by omega) (firstRootHistoryAssemble n hn k h g s) A hs).1.2
    _ (Combinatorics.interleavingRight_le (rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs).2 r)
  have hh := historyAt_root_count _ (ADR11.isForest_singletonForest (n - k.val)) _ g
    _ (Combinatorics.interleavingRight_le s.1 r)
  rw [ADR11.card_roots_singletonForest] at hp hh
  have hcard : (univ \ A).card = n - k.val := by
    rw [← hB, card_map, card_map, card_univ, Fintype.card_fin]
  omega
theorem rootHistoryDecomposition_assembly_right_shape (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hB : ((univ : Finset (Fin (n - k.val))).map Function.Embedding.inr).map
      (firstRootAssemblyLabels n k).toEmbedding = univ \ A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
 :
    (⟨(univ \ A).card, Quotient.mk (Combinatorics.rankedShapeSetoid (univ \ A).card)
      (rootHistoryDecomposition n (by omega)
        (firstRootHistoryAssemble n hn k h g s) A hs).1.2⟩ : Σ a, Combinatorics.RankedShape a) =
      ⟨n - k.val, Quotient.mk (Combinatorics.rankedShapeSetoid (n - k.val)) g⟩ := by
  let f : Fin (n - k.val) ↪ Fin n := Function.Embedding.inr.trans
    (firstRootAssemblyLabels n k).toEmbedding
  have hf : univ.map f = univ \ A := by rw [← map_map]; exact hB
  let e := cladeEmbeddingEquiv f (univ \ A) hf
  have hem : e.toEmbedding.trans (cladeLabelEmbedding (univ \ A)) = f :=
    Function.Embedding.ext (cladeEmbeddingEquiv_embedding f (univ \ A) hf)
  symm
  apply rankedShape_sigma_eq_of_forest_map (n - k.val) (univ \ A).card (by
    rw [← hf, card_map, card_univ, Fintype.card_fin]) g _ e
  intro j hj
  obtain ⟨r, hr, hrj⟩ := Combinatorics.interleavingRight_range s.1 j hj
  have hnr : r ≤ n - 2 := by have hk := mem_Ico.mp k.property; omega
  have he := rootHistoryDecomposition_assembly_right n hn k h g s A hB hs r hnr
  have hc := rootHistoryDecomposition_assembly_right_counter n hn k h g s A hB hs r hnr
  dsimp only at he hc
  rw [hc, hrj] at he
  apply forestEmbed_injective (cladeLabelEmbedding (univ \ A))
  rw [forestEmbed_comp, hem]
  exact he.symm
theorem rootHistoryDecomposition_assembly_slots (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Finset.Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))
    (A : Finset (Fin n))
    (hA : ((univ : Finset (Fin k.val)).map Function.Embedding.inl).map
      (firstRootAssemblyLabels n k).toEmbedding = A)
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1)
      (firstRootHistoryAssemble n hn k h g s)).erase univ) = {A, univ \ A})
 :
    (rootHistoryDecomposition n (by omega)
      (firstRootHistoryAssemble n hn k h g s) A hs).2.1.image Fin.val =
      s.1.1.image Fin.val := by
  have hcard : A.card = k.val := by
    rw [← hA, card_map, card_map, card_univ, Fintype.card_fin]
  have hB : (univ \ A).card = n - k.val := by
    have hc := rootPartition_card A
    omega
  apply interleaving_image_eq_of_left_counts _ _ (by rw [hcard, hB])
  intro r hr
  apply rootHistoryDecomposition_assembly_left_counter n hn k h g s A hA hs r
  rw [hcard, hB] at hr
  have hk := mem_Ico.mp k.property
  omega
end Rhone.Coalescent
