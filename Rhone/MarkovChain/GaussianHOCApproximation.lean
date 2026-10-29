/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHOCExistence
public import Rhone.MarkovChain.HouseOfCardsMoments

/-!
# Bounds for the Gaussian house-of-cards weighted second moment

Source: turelli1984, eq. (3.10)–(3.14), pp. 151–152; barton_turelli1987, pp. 158, 163. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_scaled_second_moment_pointwise_bounds
    (u k S z : ℝ) (hu : 0 < u) (hk0 : 0 < k) (hk1 : k < 1) (hS : 0 < S) :
    z^2/(z^2+2*S*(1-k)) ≤ z^2*gaussianHOCWeight u k S z/(2*S*u) ∧
      z^2*gaussianHOCWeight u k S z/(2*S*u) ≤ (1+z^2/(2*S))/k := by
  have hw := gaussian_fitness_bounds S hS z
  have hd : 0 < 1-k*gaussianFitness S z := by nlinarith
  have hd2 : 0 < z^2+2*S*(1-k) := by positivity
  have ht : 1-z^2/(2*S) ≤ gaussianFitness S z := by
    simpa only [gaussianFitness, neg_div] using Real.one_sub_le_exp_neg (z^2/(2*S))
  have hkd : k*(1-gaussianFitness S z) ≤ 1-gaussianFitness S z :=
    mul_le_of_le_one_left (by linarith : 0 ≤ 1-gaussianFitness S z) hk1.le
  have hden : 2*S*(1-k*gaussianFitness S z) ≤ z^2+2*S*(1-k) := by
    have ht' := (le_div_iff₀ (by positivity : 0 < 2*S)).mp (by linarith :
      1-gaussianFitness S z ≤ z^2/(2*S))
    have := mul_le_mul_of_nonneg_left hkd (by positivity : 0 ≤ 2*S)
    nlinarith
  have hrewrite : z^2*gaussianHOCWeight u k S z/(2*S*u) =
      z^2/(2*S*(1-k*gaussianFitness S z)) := by
    unfold gaussianHOCWeight
    field_simp
  rw [hrewrite]
  constructor
  · exact div_le_div_of_nonneg_left (sq_nonneg z) (by positivity) hden
  · by_cases hz : z = 0
    · subst z
      simpa using (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hk0.le)
    · have hcost := (HouseOfCards.selection_cost_ratio_bounds z S hS hz).2
      have hc : 0 < 1-gaussianFitness S z := by
        apply sub_pos.mpr
        apply Real.exp_lt_one_iff.mpr
        exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero hz))
          (by positivity)
      have hden' : 2*S*k*(1-gaussianFitness S z) ≤
          2*S*(1-k*gaussianFitness S z) := by
        have hh := mul_nonneg (show 0 ≤ 2*S by positivity) (show 0 ≤ 1-k by linarith)
        nlinarith
      have hl := div_le_div_of_nonneg_left (sq_nonneg z) (by positivity) hden'
      apply hl.trans
      apply (div_le_iff₀ (by positivity : 0 < 2*S*k*(1-gaussianFitness S z))).mpr
      apply (div_le_iff₀ hc).mp at hcost
      have heq : (1+z^2/(2*S))/k*(2*S*k*(1-gaussianFitness S z)) =
          (2*S+z^2)*(1-gaussianFitness S z) := by
        field_simp
      rw [heq]
      exact hcost

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_second_moment_integrable
    (u k S : ℝ) (T : ℝ≥0) (hu : 0 < u)
    (hk0 : 0 < k) (hk1 : k < 1) (hS : 0 < S) :
    MeasureTheory.Integrable (fun z => z^2*gaussianHOCWeight u k S z)
      (ProbabilityTheory.gaussianReal 0 T) := by
  have hsq : Integrable (fun z : ℝ => z^2) (gaussianReal 0 T) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) 2
  have hcont : Continuous (fun z => z^2*gaussianHOCWeight u k S z) :=
    (continuous_id.pow 2).mul (gaussian_hoc_weight_continuous u k S hk0.le hk1 hS)
  apply (hsq.mul_const (u/(1-k))).mono_nonneg hcont.aestronglyMeasurable
  · exact Eventually.of_forall fun z =>
      mul_nonneg (sq_nonneg z) (gaussian_hoc_weight_bounds u k S hu.le hk0.le hk1 hS z).1
  · exact Eventually.of_forall fun z => mul_le_mul_of_nonneg_left
      (gaussian_hoc_weight_bounds u k S hu.le hk0.le hk1 hS z).2 (sq_nonneg z)

end Rhone.MarkovChain.GaussianHouseOfCards
