/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapes
/-! # Cardinalities of the ranked and unranked Kingman shape quotients for `n = 1, 2` -/
@[expose] public section
noncomputable section
namespace Rhone.Combinatorics
private theorem shape_card_quotient_one {α : Type*} [Fintype α] (s : Setoid α)
    [Fintype (Quotient s)] (hcard : Fintype.card α = 1) :
    Fintype.card (Quotient s) = 1 := by
  have hle := Fintype.card_le_of_surjective (Quotient.mk s) Quotient.mk_surjective
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
  have hpos : 0 < Fintype.card (Quotient s) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk s a⟩
  omega
private theorem shape_history_one : Fintype.card (RankedLabelledHistory 1) = 1 := by
  rw [card_ranked_labelled_history 1 (by decide)]
  norm_num
private theorem shape_history_two : Fintype.card (RankedLabelledHistory 2) = 1 := by
  rw [card_ranked_labelled_history 2 (by decide)]
  norm_num
theorem card_ranked_shape_one : Fintype.card (RankedShape 1) = 1 :=
  @shape_card_quotient_one _ _ (rankedShapeSetoid 1)
    (inferInstanceAs (Fintype (RankedShape 1))) shape_history_one
theorem card_ranked_shape_two : Fintype.card (RankedShape 2) = 1 :=
  @shape_card_quotient_one _ _ (rankedShapeSetoid 2)
    (inferInstanceAs (Fintype (RankedShape 2))) shape_history_two
theorem card_unranked_shape_one : Fintype.card (UnrankedShape 1) = 1 :=
  @shape_card_quotient_one _ _ (unrankedShapeSetoid 1)
    (inferInstanceAs (Fintype (UnrankedShape 1))) shape_history_one
theorem card_unranked_shape_two : Fintype.card (UnrankedShape 2) = 1 :=
  @shape_card_quotient_one _ _ (unrankedShapeSetoid 2)
    (inferInstanceAs (Fintype (UnrankedShape 2))) shape_history_two
end Rhone.Combinatorics
