/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootPair
public import Rhone.Coalescent.KingmanShapeRootAssemblyExtraction
public import Rhone.Coalescent.KingmanShapeJoin
/-!
# Binary endpoint joins realize unordered root pairs of daughter shapes

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
theorem isBinaryHierarchy_equiv_embed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ≃ M)
    (G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G) :
    ADR11.IsBinaryHierarchy (forestEmbed e.toEmbedding G) := by
  refine ⟨⟨?_, ?_, (isForest_forestEmbed_iff e.toEmbedding G).mpr hG.1.2.2⟩, ?_⟩
  · exact mem_image.mpr ⟨univ, hG.1.1, clade_map_equiv_univ e⟩
  · intro x
    exact mem_image.mpr ⟨{e.symm x}, hG.1.2.1 _, by
      rw [map_singleton]; simp⟩
  · intro A hA hAc
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
    obtain ⟨C, hC, D, hD, hd, hu⟩ := hG.2 B hB (by simpa only [card_map] using hAc)
    refine ⟨C.map e.toEmbedding, mem_image.mpr ⟨C, hC, rfl⟩,
      D.map e.toEmbedding, mem_image.mpr ⟨D, hD, rfl⟩, (disjoint_map e.toEmbedding).mpr hd, ?_⟩
    rw [← map_union, hu]
theorem binaryHierarchyJoin_left_filter {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (G : Finset (Finset L)) (H : Finset (Finset M))
    (hG : ADR11.IsBinaryHierarchy G) (hH : ADR11.IsBinaryHierarchy H) :
    (binaryHierarchyJoin G H).filter
      (fun C => C ⊆ (univ : Finset L).map Function.Embedding.inl) =
      forestEmbed Function.Embedding.inl G := by
  have _hU := hG.1.1
  have hnot : ¬ (univ : Finset (L ⊕ M)) ⊆ univ.map Function.Embedding.inl := by
    intro hu
    obtain ⟨x, _⟩ := hH.1.2.2.1 univ hH.1.1
    have hx := hu (mem_univ (Sum.inr x))
    obtain ⟨y, _, he⟩ := mem_map.mp hx
    cases he
  unfold binaryHierarchyJoin
  rw [filter_insert, ite_eq_right hnot]
  have hp := history_sum_left_projection G H hH.1.2.2
  have he := congrArg (forestEmbed (Function.Embedding.inl : L ↪ L ⊕ M)) hp
  rw [forestEmbed_forestPreimage _ _ (by intro C hC; exact (mem_filter.mp hC).2)] at he
  exact he
theorem binaryHierarchyJoin_right_filter {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (G : Finset (Finset L)) (H : Finset (Finset M))
    (hG : ADR11.IsBinaryHierarchy G) (hH : ADR11.IsBinaryHierarchy H) :
    (binaryHierarchyJoin G H).filter
      (fun C => C ⊆ (univ : Finset M).map Function.Embedding.inr) =
      forestEmbed Function.Embedding.inr H := by
  have _hU := hH.1.1
  have hnot : ¬ (univ : Finset (L ⊕ M)) ⊆ univ.map Function.Embedding.inr := by
    intro hu
    obtain ⟨x, _⟩ := hG.1.2.2.1 univ hG.1.1
    have hx := hu (mem_univ (Sum.inl x))
    obtain ⟨y, _, he⟩ := mem_map.mp hx
    cases he
  unfold binaryHierarchyJoin
  rw [filter_insert, ite_eq_right hnot]
  have hp := history_sum_right_projection G H hG.1.2.2
  have he := congrArg (forestEmbed (Function.Embedding.inr : M ↪ L ⊕ M)) hp
  rw [forestEmbed_forestPreimage _ _ (by intro C hC; exact (mem_filter.mp hC).2)] at he
  exact he
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyShapeRootPair_surjective_pair (n m l : ℕ)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hl : 1 ≤ l) (hml : m + l = n)
    (G : Combinatorics.BinaryHierarchy m) (H : Combinatorics.BinaryHierarchy l) :
    ∃ F : Combinatorics.BinaryHierarchy n,
      binaryHierarchyShapeRootPair n hn
        (Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid n) F) =
      s((⟨m, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid m) G⟩ : Σ k,
          Combinatorics.BinaryHierarchyShape k),
        (⟨l, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid l) H⟩ : Σ k,
            Combinatorics.BinaryHierarchyShape k)) := by
  let e : Fin m ⊕ Fin l ≃ Fin n := finSumFinEquiv.trans (finCongr hml)
  let W := forestEmbed Function.Embedding.inl G.1 ∪ forestEmbed Function.Embedding.inr H.1
  let F : Combinatorics.BinaryHierarchy n :=
      ⟨forestEmbed e.toEmbedding (binaryHierarchyJoin G.1 H.1),
    isBinaryHierarchy_equiv_embed e _ (isBinaryHierarchy_join G.1 H.1 G.2 H.2)⟩
  let A := ((univ : Finset (Fin m)).map Function.Embedding.inl).map e.toEmbedding
  have hnot : (univ : Finset (Fin m ⊕ Fin l)) ∉ W := by
    intro hu
    rcases mem_union.mp hu with hu | hu
    · obtain ⟨C, _, hC⟩ := mem_image.mp hu
      have hx : Sum.inr (⟨0, by omega⟩ : Fin l) ∈ C.map Function.Embedding.inl :=
        hC.symm ▸ mem_univ _
      obtain ⟨x, _, he⟩ := mem_map.mp hx
      cases he
    · obtain ⟨C, _, hC⟩ := mem_image.mp hu
      have hx : Sum.inl (⟨0, by omega⟩ : Fin m) ∈ C.map Function.Embedding.inr :=
        hC.symm ▸ mem_univ _
      obtain ⟨x, _, he⟩ := mem_map.mp hx
      cases he
  have herase : F.1.erase univ = forestEmbed e.toEmbedding W := by
    change (forestEmbed e.toEmbedding (insert univ W)).erase univ = _
    rw [← clade_map_equiv_univ e, ← forestEmbed_erase, erase_insert hnot]
  have hAr : A ∈ ADR11.roots (F.1.erase univ) := by
    rw [herase, roots_forestEmbed]
    exact mem_image.mpr ⟨univ.map Function.Embedding.inl,
      history_sum_full_left_root G.1 H.1 G.2.1.2.2 G.2.1.1, rfl⟩
  have hs := (binary_hierarchy_root_pair_at F.1 F.2 (by simpa using hn) A hAr).2.2
  have hA : A ∈ F.1 := mem_of_mem_erase (ADR11.roots_subset _ hAr)
  have hBr : univ \ A ∈ ADR11.roots (F.1.erase univ) := by
    rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
  have hB : univ \ A ∈ F.1 := mem_of_mem_erase (ADR11.roots_subset _ hBr)
  have hright : ((univ : Finset (Fin l)).map Function.Embedding.inr).map e.toEmbedding =
      univ \ A := by
    have hr : (univ : Finset (Fin l)).map Function.Embedding.inr =
        (univ : Finset (Fin m ⊕ Fin l)) \ univ.map Function.Embedding.inl := by
      ext x
      cases x <;> simp
    rw [hr, Finset.map_sdiff, clade_map_equiv_univ]
  have recover (a : ℕ) (Q : Combinatorics.BinaryHierarchy a) (B : Finset (Fin n)) (hBF : B ∈ F.1)
      (f : Fin a ↪ Fin n) (hf : univ.map f = B)
      (hfilter : F.1.filter (fun C => C ⊆ B) = forestEmbed f Q.1) :
      binaryHierarchyDaughterShape n F B hBF =
        (⟨a, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid a) Q⟩ : Σ k,
            Combinatorics.BinaryHierarchyShape k) := by
    let q := cladeEmbeddingEquiv f B hf
    have hq : q.toEmbedding.trans (cladeLabelEmbedding B) = f :=
      Function.Embedding.ext (cladeEmbeddingEquiv_embedding f B hf)
    symm
    apply binaryHierarchyShape_sigma_eq_of_map a B.card (by
      rw [← hf, card_map, card_univ, Fintype.card_fin]) Q _ q
    apply forestEmbed_injective (cladeLabelEmbedding B)
    rw [forestEmbed_comp, hq]
    change forestEmbed f Q.1 = forestEmbed (cladeLabelEmbedding B)
      (forestPreimage (cladeLabelEmbedding B) (F.1.filter (fun C => C ⊆ B)))
    rw [forestEmbed_forestPreimage _ _ (by
      intro C hC
      rw [cladeLabelEmbedding_range]
      exact (mem_filter.mp hC).2), hfilter]
  refine ⟨F, ?_⟩
  rw [binaryHierarchyShapeRootPair_mk n hn F A hs]
  unfold binaryHierarchyRootDaughterPair
  congr 1
  · apply recover m G A _ (Function.Embedding.inl.trans e.toEmbedding)
    · rw [← map_map]
    · change (forestEmbed e.toEmbedding (binaryHierarchyJoin G.1 H.1)).filter _ = _
      rw [← forestEmbed_filter_clade e.toEmbedding _ A rfl,
        binaryHierarchyJoin_left_filter _ _ G.2 H.2, forestEmbed_comp]
  · apply recover l H (univ \ A) _ (Function.Embedding.inr.trans e.toEmbedding)
    · rw [← map_map]; exact hright
    · change (forestEmbed e.toEmbedding (binaryHierarchyJoin G.1 H.1)).filter _ = _
      rw [← forestEmbed_filter_clade e.toEmbedding _ (univ \ A) hright,
        binaryHierarchyJoin_right_filter _ _ G.2 H.2, forestEmbed_comp]
end Rhone.Coalescent
