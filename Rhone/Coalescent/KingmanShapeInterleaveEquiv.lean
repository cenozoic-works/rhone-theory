/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeInterleaveFibre
/-!
# Chronological subtree histories and slots exactly parametrize their fibre

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def historyInterleaveEquiv {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ) :
    ((Combinatorics.RankedForestHistory F a × Combinatorics.RankedForestHistory H b) ×
        Combinatorics.HistoryInterleaving a b) ≃
      SeparatedForestHistory F H a b := by
  apply Equiv.ofBijective (separatedHistoryInterleave F H hF hH a b)
  constructor
  · intro p q he
    exact historyInterleave_injective F H hF hH a b (congrArg Subtype.val he)
  · intro h
    obtain ⟨p, hp⟩ := historyInterleave_surjective_separated F H hF hH a b h
    exact ⟨p, Subtype.ext hp⟩
end Rhone.Coalescent
