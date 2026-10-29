/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeEndpointQuotient
public import Rhone.Coalescent.KingmanShapeCladeFilterRelabel
public import Rhone.Coalescent.KingmanSubtreeTopology
public import Rhone.Coalescent.KingmanShapeRootPairAt
/-!
# Binary endpoint daughters descend under the leaf relabelling relation

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def binaryHierarchyDaughter (n : ℕ) (G : Combinatorics.BinaryHierarchy n)
    (A : Finset (Fin n)) (hA : A ∈ G.1) : Combinatorics.BinaryHierarchy A.card :=
  ⟨forestPreimage (cladeLabelEmbedding A) (G.1.filter (fun C => C ⊆ A)),
    isBinaryHierarchy_subtree_preimage G.1 G.2 (cladeLabelEmbedding A) A hA
      (cladeLabelEmbedding_range A)⟩
theorem binaryHierarchyShape_sigma_eq_of_map (m n : ℕ) (hmn : m = n)
    (G : Combinatorics.BinaryHierarchy m) (H : Combinatorics.BinaryHierarchy n) (e : Fin m ≃ Fin n)
    (he : forestEmbed e.toEmbedding G.1 = H.1) :
    (⟨m, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid m) G⟩ : Σ k,
        Combinatorics.BinaryHierarchyShape k) =
      ⟨n, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid n) H⟩ := by
  subst n
  apply congrArg (Sigma.mk m)
  exact Quotient.sound ⟨e, he⟩
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyDaughter_shape_map (n : ℕ) (G H : Combinatorics.BinaryHierarchy n)
    (A B : Finset (Fin n)) (hA : A ∈ G.1) (hB : B ∈ H.1)
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : Combinatorics.forestRelabel e G.1 = H.1) :
    (⟨A.card, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid A.card)
      (binaryHierarchyDaughter n G A hA)⟩ : Σ k, Combinatorics.BinaryHierarchyShape k) =
    ⟨B.card, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid B.card)
      (binaryHierarchyDaughter n H B hB)⟩ := by
  apply binaryHierarchyShape_sigma_eq_of_map _ _ (cladeRelabel_card n e A B hAB)
    _ _ (cladeRelabelEquiv n e A B hAB)
  change forestEmbed _ (forestPreimage _ _) = forestPreimage _ _
  rw [← retainedSubtree_relabel n e A B hAB]
  change forestEmbed e.toEmbedding G.1 = H.1 at he
  rw [he]
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchy_root_map_cases (n : ℕ) (G H : Combinatorics.BinaryHierarchy n)
    (A B : Finset (Fin n))
    (hA : A ∈ ADR11.roots (G.1.erase univ))
    (hB : ADR11.roots (H.1.erase univ) = {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (he : Combinatorics.forestRelabel e G.1 = H.1) :
    A.map e.toEmbedding = B ∨ A.map e.toEmbedding = univ \ B := by
  have hp : forestEmbed e.toEmbedding (G.1.erase univ) = H.1.erase univ := by
    rw [forestEmbed_erase, clade_map_equiv_univ]
    change forestEmbed e.toEmbedding G.1 = H.1 at he
    rw [he]
  have hr : A.map e.toEmbedding ∈ ADR11.roots (H.1.erase univ) := by
    rw [← hp, roots_forestEmbed]
    exact mem_image.mpr ⟨A, hA, rfl⟩
  simpa only [hB, mem_insert, mem_singleton] using hr
end Rhone.Coalescent
