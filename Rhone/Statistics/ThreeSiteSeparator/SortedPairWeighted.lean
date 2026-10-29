/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedPairLaw
public import Rhone.Statistics.ThreeSiteSeparator.CDFJointWeighted

/-! # The weighted joint CDF of the sorted law equals its analytic expression -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma cdfJoint_unitSquare_integrable {F : ℝ → ℝ} (hF : Continuous F) (p q : ℕ) :
    Integrable (fun x : ℝ × ℝ => x.1^p*x.2^q*cdfJointFunction F x.1 x.2)
      unitSquareVolume := by
  have hc : Continuous (fun x : ℝ × ℝ => x.1^p*x.2^q*cdfJointFunction F x.1 x.2) :=
    ((continuous_fst.pow p).mul (continuous_snd.pow q)).mul (cdfJointFunction_continuous hF)
  unfold unitSquareVolume
  rw [Measure.prod_restrict]
  exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma sortedPair_weighted_CDF (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hF : Continuous (fun x => μ.real (Iic x))) (p q : ℕ) :
    weightedJointCDF p q (sortedPairLaw μ) =
      cdfJointWeightedIntegral p q (fun x => μ.real (Iic x)) := by
  unfold weightedJointCDF
  have he : (fun x : ℝ × ℝ => x.1^p*x.2^q*rectangleCDF (sortedPairLaw μ) x) =
      fun x => x.1^p*x.2^q*cdfJointFunction (fun z => μ.real (Iic z)) x.1 x.2 := by
    funext x
    rcases x with ⟨x, y⟩
    rw [sortedPairLaw_CDF]
  rw [he]
  unfold unitSquareVolume
  rw [integral_prod _ (cdfJoint_unitSquare_integrable hF p q)]
  unfold cdfJointWeightedIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

end Rhone.Statistics.ThreeSiteSeparator
