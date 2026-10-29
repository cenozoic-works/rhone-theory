/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFibreTransport
public import Rhone.Coalescent.KingmanShapeRootAssemblyExtraction
/-!
# Ranked root-fibre inverse identities from chronological daughter recovery

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryFibreData_assembly (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :
    rootHistoryFibreData n hn k (firstRootHistoryAssemble n hn k h g s)
      (firstMergerRoot_card_firstRootHistoryAssemble n hn k h g s) =
      ((Quotient.mk (Combinatorics.rankedShapeSetoid k.val) h,
        Quotient.mk (Combinatorics.rankedShapeSetoid (n - k.val)) g), s) := by
  let q := firstRootHistoryAssemble n hn k h g s
  let A := firstMergerRoot n hn q
  have hA : ((univ : Finset (Fin k.val)).map Function.Embedding.inl).map
      (firstRootAssemblyLabels n k).toEmbedding = A :=
    (firstMergerRoot_firstRootHistoryAssemble n hn k h g s).symm
  have hsplit : (univ : Finset (Fin k.val ⊕ Fin (n - k.val))) \
      (univ : Finset (Fin k.val)).map Function.Embedding.inl =
      (univ : Finset (Fin (n - k.val))).map Function.Embedding.inr := by
    ext x
    cases x <;> simp
  have hB : ((univ : Finset (Fin (n - k.val))).map Function.Embedding.inr).map
      (firstRootAssemblyLabels n k).toEmbedding = univ \ A := by
    rw [← hsplit, Finset.map_sdiff, clade_map_equiv_univ, hA]
  have hs := (binary_hierarchy_root_pair_at _
      (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) q)
    (by simpa using (show 2 ≤ n by omega)) A (firstMergerRoot_spec n hn q).1).2.2
  have hcard : A.card = k.val := by rw [← hA, card_map, card_map, card_univ, Fintype.card_fin]
  have hcardB : (univ \ A).card = n - k.val := by
    rw [← hB, card_map, card_map, card_univ, Fintype.card_fin]
  dsimp only [A, q] at hcard hcardB
  dsimp only [rootHistoryFibreData]
  apply Prod.ext
  · apply Prod.ext
    · exact cast_shape_eq_of_sigma_eq _ (Quotient.mk (Combinatorics.rankedShapeSetoid k.val) h)
        hcard rfl (rootHistoryDecomposition_assembly_left_shape n hn k h g s A hA hs)
    · exact cast_shape_eq_of_sigma_eq _
        (Quotient.mk (Combinatorics.rankedShapeSetoid (n - k.val)) g)
        hcardB rfl (rootHistoryDecomposition_assembly_right_shape n hn k h g s A hB hs)
  · exact cast_first_interleaving_eq_of_image_eq _ s
      (congrArg (fun a => a - 1) hcard) (congrArg (fun a => a - 1) hcardB) rfl rfl
      (rootHistoryDecomposition_assembly_slots n hn k h g s A hA hs)
end Rhone.Coalescent
