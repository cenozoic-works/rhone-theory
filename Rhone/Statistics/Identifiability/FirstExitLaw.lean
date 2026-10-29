/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IslandAbsorption
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Normalized first-exit measures -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open Filter Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem firstExit_density_nonneg {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin d)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ flowOutput Q i (exitRate Q) 0 t := by
  simp only [flowOutput, pow_zero, Matrix.one_mul]
  exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg Q hQ ht)
    (exitRate_nonneg Q hrow) i

theorem exitCDF_hasDerivAt {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (t : ℝ) :
    HasDerivAt (fun x => 1 - flowOutput Q i (fun _ => 1) 0 x)
      (flowOutput Q i (exitRate Q) 0 t) t := by
  simpa using (survival_hasDerivAt_exit Q i t).const_sub 1

theorem firstExit_integrable {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin d)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    IntegrableOn (flowOutput Q i (exitRate Q) 0) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (fun t _ => exitCDF_hasDerivAt Q i t)
    (fun t ht => firstExit_density_nonneg Q hQ hrow i ht.le)
  exact htail.const_sub 1

theorem firstExit_integral_one {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin d)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    (∫ t in Ioi 0, flowOutput Q i (exitRate Q) 0 t) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => exitCDF_hasDerivAt Q i t)
    (fun t ht => firstExit_density_nonneg Q hQ hrow i ht.le) (htail.const_sub 1)
  simpa using h

noncomputable def firstExitLaw {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (flowOutput Q i (exitRate Q) 0 t))

theorem firstExitLaw_probability {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin d)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    IsProbabilityMeasure (firstExitLaw Q i) := by
  constructor
  rw [firstExitLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (firstExit_integrable Q hQ hrow i htail)]
  · rw [firstExit_integral_one Q hQ hrow i htail, ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact firstExit_density_nonneg Q hQ hrow i ht.le

theorem island_firstExitLaw_probability (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) :
    IsProbabilityMeasure (firstExitLaw (MarkovChain.Identifiability.generator k c q r) 0) := by
  apply firstExitLaw_probability _ (generator_metzler k hc.le hq.le hr) _ 0
    (island_survival_tendsto_zero k hc hq hr)
  intro i
  rw [generator_row_sum]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Nat.cast_nonneg _)

end Rhone.Statistics.Identifiability
