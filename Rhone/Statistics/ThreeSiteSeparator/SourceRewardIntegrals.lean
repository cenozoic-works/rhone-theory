/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SourcePotentials
public import Rhone.Statistics.ThreeSiteSeparator.SourceProductLaw

/-! # Reward-potential check of the source Laplace integrals -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology
namespace Rhone.Statistics.ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability

lemma firstRate_column (j : Fin 2) :
    (fun i => IslandThreeTimes.firstRate 1 i j) =
      (![3*(if j = 0 then 1 else 0), if j = 1 then 1 else 0, 0] : Fin 3 → ℝ) := by
  fin_cases j
  · simpa using firstRate_basis_zero
  · simpa using firstRate_basis_one

lemma entry_discounted_integrable {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (j : Fin 2) :
    IntegrableOn (fun s => Real.exp (-a*s)*IslandThreeTimes.entryFlux 0 1 m j s) (Ioi 0) := by
  have hu := prePotential_equation hm ha
    (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
  rw [← firstRate_column j] at hu
  have hi := reward_integrable (threeGenerator 0 1 m - a • 1)
    (isMetzler_sub_scalar_identity (threeGenerator_metzler 0 1 hm.le) a) 0
    _ (fun i => IslandThreeTimes.firstRate 1 i j) hu
    (fun i => IslandThreeTimes.firstRate_nonneg (by norm_num) i j)
    (survival_sub_scalar_identity_tendsto_zero _ (threeGenerator_metzler 0 1 hm.le) ha 0
      (three_survival_tendsto_zero 0 (by norm_num) hm 0))
  convert! hi using 1
  funext t
  exact (flowOutput_sub_scalar_identity _ a 0
    (fun i => IslandThreeTimes.firstRate 1 i j) t).symm

lemma entry_discounted_integral {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (j : Fin 2) :
    (∫ s in Ioi 0, Real.exp (-a*s)*IslandThreeTimes.entryFlux 0 1 m j s) =
      (prePotential m a (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)) 0 := by
  have hu := prePotential_equation hm ha
    (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
  rw [← firstRate_column j] at hu
  have hi := reward_integral_eq_potential (threeGenerator 0 1 m - a • 1)
    (isMetzler_sub_scalar_identity (threeGenerator_metzler 0 1 hm.le) a) 0
    _ (fun i => IslandThreeTimes.firstRate 1 i j) hu
    (fun i => IslandThreeTimes.firstRate_nonneg (by norm_num) i j)
    (survival_sub_scalar_identity_tendsto_zero _ (threeGenerator_metzler 0 1 hm.le) ha 0
      (three_survival_tendsto_zero 0 (by norm_num) hm 0))
  simpa only [flowOutput_sub_scalar_identity, IslandThreeTimes.entryFlux] using hi

lemma entryMeasure_finite {m : ℝ} (hm : 0 < m) (j : Fin 2) :
    IsFiniteMeasure (entryMeasure m j) := by
  have hi := entry_discounted_integrable hm (le_refl (0 : ℝ)) j
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at hi
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

lemma entryMeasure_laplace {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (j : Fin 2) :
    (∫ s, Real.exp (-a*s) ∂entryMeasure m j) =
      (prePotential m a (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)) 0 := by
  unfold entryMeasure
  rw [TwoEventFluxLaw.integral_ofReal_density _ _ _
    (IslandThreeTimes.entryFlux_continuous 0 1 m j).measurable.aemeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact IslandThreeTimes.entryFlux_nonneg 0 (by norm_num) hm.le hs.le j)]
  simp_rw [mul_comm]
  simpa only [mul_comm] using entry_discounted_integral hm ha j

lemma postMeasure_laplace {m b : ℝ} (hm : 0 < m) (hb : 0 ≤ b) (j : Fin 2) :
    (∫ s, Real.exp (-b*s) ∂postMeasure m j) = pairLaplacePotential 0 1 m b j := by
  have hd := pairLaplaceDenominator_pos 0 (by norm_num : (0 : ℝ) < 1) hm hb
  have hi := reward_integral_eq_potential (pairGenerator 0 1 m - b • 1)
    (isMetzler_sub_scalar_identity (pairGenerator_metzler 0 hm.le) b) j
    (pairLaplacePotential 0 1 m b) (pairDensity 1)
    (pairLaplacePotential_equation 0 hd.ne')
    (by intro i; fin_cases i <;> norm_num [pairDensity])
    (survival_sub_scalar_identity_tendsto_zero _ (pairGenerator_metzler 0 hm.le) hb j
      (pair_survival_tendsto_zero 0 (by norm_num) hm j))
  unfold postMeasure firstExitLaw
  rw [TwoEventFluxLaw.integral_ofReal_density _ _ _
    (flowOutput_continuous _ _ _ _).measurable.aemeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact firstExit_density_nonneg _ (pairGenerator_metzler 0 hm.le)
        (pairGenerator_rows_nonpos 0 (by norm_num)) j hs.le)]
  rw [pair_exitRate]
  simp_rw [mul_comm]
  simpa only [flowOutput_sub_scalar_identity, mul_comm] using hi

end Rhone.Statistics.ThreeSiteSeparator
