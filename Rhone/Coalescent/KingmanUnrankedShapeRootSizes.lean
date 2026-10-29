/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootPair
/-!
# The root pair of an unranked shape consists of two daughters of positive sizes

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyShapeRootPair_sizes (n : ℕ) (hn : 2 ≤ n)
    (q : Combinatorics.BinaryHierarchyShape n) :
    ∃ m l : ℕ, 1 ≤ m ∧ 1 ≤ l ∧ m + l = n ∧
      ∃ G : Combinatorics.BinaryHierarchyShape m, ∃ H : Combinatorics.BinaryHierarchyShape l,
        binaryHierarchyShapeRootPair n hn q =
          s((⟨m,G⟩ : Σ k, Combinatorics.BinaryHierarchyShape k),
            (⟨l,H⟩ : Σ k, Combinatorics.BinaryHierarchyShape k)) := by
  induction q using Quotient.inductionOn with
  | h F =>
    obtain ⟨A,ha,hb,hs⟩ := binary_hierarchy_root_pair F.1 F.2
      (by simpa using hn : 2 ≤ Fintype.card (Fin n))
    have hml : A.card + (univ \ A).card = n := by
      have hc := card_sdiff_of_subset (subset_univ A)
      have hA : A.card ≤ n := by simpa using card_le_card (subset_univ A)
      rw [card_univ, Fintype.card_fin] at hc
      omega
    refine ⟨A.card,(univ \ A).card,card_pos.mpr ha,card_pos.mpr hb,hml,?_,?_,?_⟩
    · exact Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid A.card)
        (binaryHierarchyDaughter n F A
          (mem_of_mem_erase (ADR11.roots_subset _ (hs ▸ mem_insert_self _ _))))
    · exact Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid (univ \ A).card)
        (binaryHierarchyDaughter n F (univ \ A)
          (mem_of_mem_erase (ADR11.roots_subset _
            (hs ▸ mem_insert_of_mem (mem_singleton_self _)))))
    · exact binaryHierarchyShapeRootPair_mk n hn F A hs

end Rhone.Coalescent
