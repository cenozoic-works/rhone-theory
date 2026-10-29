/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFirstMergerRelabel
/-!
# The first-merger daughter size descends to ranked shape quotients

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem firstMergerRoot_card_lt (n : ℕ) (hn : 3 ≤ n) (h : Combinatorics.RankedLabelledHistory n) :
    (firstMergerRoot n hn h).card < n := by
  have hm := ADR11.roots_subset _ (firstMergerRoot_spec n hn h).1
  have hne := (mem_erase.mp hm).1
  have hc := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hne⟩)
  simpa only [card_univ, Fintype.card_fin] using hc
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rankedShapeRootSize (n : ℕ) (hn : 3 ≤ n) :
    Combinatorics.RankedShape n → {k : ℕ // k ∈ Ico 2 n} := by
  refine Quotient.lift (fun h : Combinatorics.RankedLabelledHistory n =>
    (⟨(firstMergerRoot n hn h).card,
      mem_Ico.mpr ⟨firstMergerRoot_card n hn h, firstMergerRoot_card_lt n hn h⟩⟩ :
      {k : ℕ // k ∈ Ico 2 n})) ?_
  intro h h' he
  obtain ⟨e, he⟩ := he
  apply Subtype.ext
  have hc := congrArg Finset.card (firstMergerRoot_map n hn h h' e he)
  simpa only [card_map] using hc
theorem rankedShapeRootSize_mk (n : ℕ) (hn : 3 ≤ n) (h : Combinatorics.RankedLabelledHistory n) :
    (rankedShapeRootSize n hn (Quotient.mk (Combinatorics.rankedShapeSetoid n) h)).val =
      (firstMergerRoot n hn h).card := rfl
end Rhone.Coalescent
