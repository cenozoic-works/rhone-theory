/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHOCRescaling

/-!
# Symmetry of the Gaussian house-of-cards law about the optimum

Source: turelli1984, pp. 150–151; barton_turelli1987, pp. 158, 163. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- Source: turelli1984, pp. 150–151; barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_mean_zero
    (u k S : ℝ) (T : ℝ≥0) (hu : 0 < u)
    (hk0 : 0 < k) (hk1 : k < 1) (hS : 0 < S) :
    (∫ z, z ∂gaussianHOCLaw u k S T) = 0 := by
  have hQ : Measurable (fun z => ENNReal.ofReal (gaussianHOCWeight u k S z)) :=
    ENNReal.measurable_ofReal.comp
      (gaussian_hoc_weight_continuous u k S hk0.le hk1 hS).measurable
  have hc : Continuous (fun z => gaussianHOCWeight u k S z*z) :=
    (gaussian_hoc_weight_continuous u k S hk0.le hk1 hS).mul continuous_id
  have hsym : (gaussianReal 0 T).map (fun z => -z) = gaussianReal 0 T := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := T))
  have hodd : (fun z => gaussianHOCWeight u k S (-z)*(-z)) =
      fun z => -(gaussianHOCWeight u k S z*z) := by
    ext z
    simp [gaussianHOCWeight, gaussianFitness]
  have hi : (∫ z, gaussianHOCWeight u k S z*z ∂gaussianReal 0 T) =
      -(∫ z, gaussianHOCWeight u k S z*z ∂gaussianReal 0 T) := by
    conv_lhs => rw [← hsym]
    rw [integral_map (by fun_prop) hc.aestronglyMeasurable, hodd, integral_neg]
  unfold gaussianHOCLaw
  rw [integral_withDensity_eq_integral_toReal_smul hQ
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal
    (gaussian_hoc_weight_bounds u k S hu.le hk0.le hk1 hS _).1, smul_eq_mul]
  linarith

end Rhone.MarkovChain.GaussianHouseOfCards
