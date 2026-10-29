/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.SelectedMeiosis
public import Rhone.Dynamics.TwoLocusSelection

/-!
# Agreement of selected-parent meiosis with the viability recursion

Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/

@[expose] public section
namespace Rhone.Dynamics.SelectedMeiosis

/-- Source: burger2013_migration_selection, sec. 7.2, eq. 7.10. -/
theorem selected_meiosis_eq_viability_step
    (W : Fin 4 → Fin 4 → ℝ) (r : ℝ) (g : Gametes ℝ)
    (hsym : ∀ i j, W i j = W j i) (hpos : W 0 3 = W 1 2) :
    selectedOffspring (TwoLocusSelection.vector g) W r =
      TwoLocusSelection.step W r g := by
  have hmass : selectionMass (TwoLocusSelection.vector g) W =
      multiMeanFit W (TwoLocusSelection.vector g) :=
    (multiMeanFit_eq_sum W (TwoLocusSelection.vector g)).symm
  have hs10 := hsym 1 0
  have hs20 := hsym 2 0
  have hs30 := hsym 3 0
  have hs21 := hsym 2 1
  have hs31 := hsym 3 1
  have hs32 := hsym 3 2
  unfold selectedOffspring selectedExpectation
  rw [hmass]
  norm_num [TwoLocusSelection.step, TwoLocusSelection.fromVector,
    TwoLocusSelection.sign, TwoLocusSelection.vector, transmission, jointTransmission,
    firstAllele, secondAllele, marginalFit, Fin.sum_univ_four, Gametes.D]
  simp only [hs10, hs20, hs30, hs21, hs31, hs32, ← hpos, div_eq_mul_inv]
  repeat' constructor
  all_goals ring_nf

end Rhone.Dynamics.SelectedMeiosis
