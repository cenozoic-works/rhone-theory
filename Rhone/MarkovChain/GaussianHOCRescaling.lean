/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHOCApproximation

/-!
# Gaussian house-of-cards second moment expressed under standard Gaussian redraw

Source: turelli1984, eq. (3.5)–(3.6), p. 151; barton_turelli1987, pp. 158, 163. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- Source: turelli1984, eq. (3.5), p. 151. -/
theorem gaussian_hoc_variance_as_redraw_integral
    (u k S : ℝ) (T : ℝ≥0) (hu : 0 < u)
    (hk0 : 0 < k) (hk1 : k < 1) (hS : 0 < S) :
    gaussianHOCVariance u k S T =
      ∫ z, z^2*gaussianHOCWeight u k S z ∂ProbabilityTheory.gaussianReal 0 T := by
  have hQ : Measurable (fun z => ENNReal.ofReal (gaussianHOCWeight u k S z)) :=
    ENNReal.measurable_ofReal.comp
      (gaussian_hoc_weight_continuous u k S hk0.le hk1 hS).measurable
  unfold gaussianHOCVariance gaussianHOCLaw
  rw [integral_withDensity_eq_integral_toReal_smul hQ
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal
    (gaussian_hoc_weight_bounds u k S hu.le hk0.le hk1 hS _).1, smul_eq_mul]
  congr 1
  ext z
  ring

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_scaled_variance_as_standard_integral
    (u k S : ℝ) (T : ℝ≥0) (hu : 0 < u)
    (hk0 : 0 < k) (hk1 : k < 1) (hS : 0 < S) :
    gaussianHOCVariance u k S T/(2*S*u) =
      ∫ y, (Real.sqrt (T : ℝ)*y)^2*
        gaussianHOCWeight u k S (Real.sqrt (T : ℝ)*y)/(2*S*u)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun y => Real.sqrt (T : ℝ)*y) =
      gaussianReal 0 T := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt T.coe_nonneg]
  rw [gaussian_hoc_variance_as_redraw_integral u k S T hu hk0 hk1 hS,
    ← integral_div, ← hmap, integral_map (by fun_prop) (by
      exact ((continuous_id.pow 2).mul
        (gaussian_hoc_weight_continuous u k S hk0.le hk1 hS)).div_const
          (2*S*u) |>.aestronglyMeasurable)]

end Rhone.MarkovChain.GaussianHouseOfCards
