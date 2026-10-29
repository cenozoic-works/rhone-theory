/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanHistoryTopology
/-! # A binary hierarchy not yet reached has a missing clade that merges retained roots -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem binaryHierarchy_missing_merge {L : Type*} [Fintype L] [DecidableEq L]
    (F G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G) (hFG : F ⊆ G)
    (hne : F ≠ G) (hsingle : ∀ x : L, {x} ∈ F)
    (hdown : ∀ A ∈ F, ∀ B ∈ G, B ⊆ A → B ∈ F) :
    ∃ A ∈ G, A ∉ F ∧ (∀ B ∈ G, B ⊂ A → B ∈ F) ∧
      insert A F ∈ ADR11.merges F := by
  classical
  have hdiff : (G \ F).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hGF
    exact hne (Subset.antisymm hFG hGF)
  obtain ⟨A, hAm, hmin⟩ := (G \ F).exists_min_image card hdiff
  obtain ⟨hAG, hAF⟩ := mem_sdiff.mp hAm
  have hproper : ∀ B ∈ G, B ⊂ A → B ∈ F := by
    intro B hBG hBA
    by_contra hBF
    have := hmin B (mem_sdiff.mpr ⟨hBG, hBF⟩)
    have := card_lt_card hBA
    omega
  have hAc : 2 ≤ A.card := by
    have hp := (hG.1.2.2.1 A hAG).card_pos
    by_contra hn
    have h1 : A.card = 1 := by omega
    obtain ⟨x, rfl⟩ := card_eq_one.mp h1
    exact hAF (hsingle x)
  obtain ⟨B, hBG, C, hCG, hBC, hBCA⟩ := hG.2 A hAG hAc
  have hBne := hG.1.2.2.1 B hBG
  have hCne := hG.1.2.2.1 C hCG
  have proper_child (X Y : Finset L) (hY : Y.Nonempty)
      (hXY : Disjoint X Y) (hu : X ∪ Y = A) : X ⊂ A := by
    apply ssubset_of_subset_not_subset (hu ▸ subset_union_left)
    intro hAX
    obtain ⟨y, hy⟩ := hY
    exact disjoint_left.mp hXY (hAX (hu ▸ mem_union_right X hy)) hy
  have hBA := proper_child B C hCne hBC hBCA
  have hCA := proper_child C B hBne hBC.symm (by rw [union_comm]; exact hBCA)
  have hBF := hproper B hBG hBA
  have hCF := hproper C hCG hCA
  have root_child (X Y : Finset L) (hXG : X ∈ G) (hYG : Y ∈ G)
      (hXne : X.Nonempty) (hXY : Disjoint X Y) (hu : X ∪ Y = A)
      (hXF : X ∈ F) : X ∈ ADR11.roots F := by
    apply ADR11.mem_roots.mpr
    refine ⟨hXF, ?_⟩
    intro D hDF hXD
    have hDG := hFG hDF
    rcases hG.1.2.2.2 A hAG D hDG with hAD | hDA | hdisj
    · exact False.elim (hAF (hdown D hDF A hAG hAD))
    · rcases ADR11.counts_subset_union_cases hG.1 hXG hYG hXY hDG (hu ▸ hDA)
        with hD | hDX | hDY
      · exact False.elim (hAF (hD.trans hu ▸ hDF))
      · exact Subset.antisymm hDX hXD
      · obtain ⟨x, hx⟩ := hXne
        exact False.elim (disjoint_left.mp hXY hx (hDY (hXD hx)))
    · obtain ⟨x, hx⟩ := hXne
      exact False.elim (disjoint_left.mp hdisj (hu ▸ mem_union_left Y hx) (hXD hx))
  have hBr := root_child B C hBG hCG hBne hBC hBCA hBF
  have hCr := root_child C B hCG hBG hCne hBC.symm (by rw [union_comm]; exact hBCA) hCF
  have hBneC : B ≠ C := by
    intro he
    obtain ⟨b, hb⟩ := hBne
    exact disjoint_left.mp hBC hb (he ▸ hb)
  refine ⟨A, hAG, hAF, hproper, ADR11.mem_merges.mpr ⟨B, hBr, C, hCr, hBneC, ?_⟩⟩
  rw [hBCA]
end Rhone.Combinatorics
