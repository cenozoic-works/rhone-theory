/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHouseOfCards

/-!
# The Gaussian house-of-cards normalizer is continuous and strictly increasing

Source: turelli1984, p. 150, eq. (3.2b), p. 151, eq. (3.7); barton_turelli1987, pp. 158, 163. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_mass_strict_mono (u S : ℝ) (T : ℝ≥0)
    (hu : 0 < u) (hS : 0 < S) :
    StrictMonoOn (fun k => gaussianHOCMass u k S T) (Set.Ico 0 1) := by
  intro k1 hk1 k2 hk2 hkk
  have hp (z : ℝ) : gaussianHOCWeight u k1 S z < gaussianHOCWeight u k2 S z := by
    have hw := gaussian_fitness_bounds S hS z
    have hd1 : 0 < 1-k1*gaussianFitness S z := by nlinarith [hk1.1, hk1.2]
    have hd2 : 0 < 1-k2*gaussianFitness S z := by nlinarith [hk2.1, hk2.2]
    unfold gaussianHOCWeight
    apply (div_lt_div_iff₀ hd1 hd2).mpr
    exact mul_lt_mul_of_pos_left
      (sub_lt_sub_left (mul_lt_mul_of_pos_right hkk hw.1) 1) hu
  have hq1 := gaussian_hoc_weight_integrable u k1 S T hu.le hk1.1 hk1.2 hS
  have hq2 := gaussian_hoc_weight_integrable u k2 S T hu.le hk2.1 hk2.2 hS
  have hsupp : Function.support (fun z => gaussianHOCWeight u k2 S z-
      gaussianHOCWeight u k1 S z) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (sub_pos.mpr (hp z))
  have hi : 0 < ∫ z, gaussianHOCWeight u k2 S z-gaussianHOCWeight u k1 S z
      ∂gaussianReal 0 T := by
    apply (integral_pos_iff_support_of_nonneg (fun z => (sub_pos.mpr (hp z)).le)
      (hq2.sub hq1)).mpr
    rw [hsupp, measure_univ]
    exact zero_lt_one
  rw [integral_sub hq2 hq1] at hi
  exact sub_pos.mp hi

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_mass_continuous_on (u S : ℝ) (T : ℝ≥0)
    (hu : 0 ≤ u) (hS : 0 < S) (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ContinuousOn (fun k => gaussianHOCMass u k S T) (Set.Icc 0 K) := by
  have _ := hK0
  unfold gaussianHOCMass
  apply continuousOn_of_dominated (bound := fun _ => u/(1-K))
  · intro k hk
    have hcont := gaussian_hoc_weight_continuous u k S hk.1
      (lt_of_le_of_lt hk.2 hK1) hS
    exact hcont.aestronglyMeasurable
  · intro k hk
    apply Filter.Eventually.of_forall
    intro z
    have hb := gaussian_hoc_weight_bounds u k S hu hk.1 (lt_of_le_of_lt hk.2 hK1) hS z
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    apply hb.2.trans
    apply div_le_div_of_nonneg_left hu (sub_pos.mpr hK1)
    linarith [hk.2]
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro z
    have hw := gaussian_fitness_bounds S hS z
    unfold gaussianHOCWeight
    apply continuousOn_const.div₀
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
    intro k hk
    change 1-k*gaussianFitness S z ≠ 0
    nlinarith [hk.1, lt_of_le_of_lt hk.2 hK1]

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_mass_left_endpoint_lt_one (u S : ℝ) (T : ℝ≥0)
    (hu0 : 0 < u) (hu1 : u < 1) (hS : 0 < S) (hT : 0 < T) :
    gaussianHOCMass u (1-u) S T < 1 := by
  let _ : NullSingletonClass (gaussianReal 0 T) :=
    nullSingletonClass_gaussianReal (ne_of_gt hT)
  have hk0 : 0 < 1-u := sub_pos.mpr hu1
  have hk1 : 1-u < 1 := by linarith
  have hq := gaussian_hoc_weight_integrable u (1-u) S T hu0.le hk0.le hk1 hS
  have hle (z : ℝ) : gaussianHOCWeight u (1-u) S z ≤ 1 := by
    simpa only [sub_sub_cancel, div_self (ne_of_gt hu0)] using
      (gaussian_hoc_weight_bounds u (1-u) S hu0.le hk0.le hk1 hS z).2
  have hlt (z : ℝ) (hz : z ≠ 0) : gaussianHOCWeight u (1-u) S z < 1 := by
    have hw : gaussianFitness S z < 1 := by
      apply Real.exp_lt_one_iff.mpr
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero hz)) (by positivity)
    have hden : u < 1-(1-u)*gaussianFitness S z := by nlinarith
    apply (div_lt_one (lt_trans hu0 hden)).mpr
    exact hden
  have hsupp : Function.support (fun z => 1-gaussianHOCWeight u (1-u) S z) =
      ({0} : Set ℝ)ᶜ := by
    ext z
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_singleton_iff]
    by_cases hz : z = 0
    · subst z
      simp [gaussianHOCWeight, gaussianFitness, sub_sub_cancel, div_self (ne_of_gt hu0)]
    · exact iff_of_true (ne_of_gt (sub_pos.mpr (hlt z hz))) hz
  have hi : 0 < ∫ z, 1-gaussianHOCWeight u (1-u) S z ∂gaussianReal 0 T := by
    apply (integral_pos_iff_support_of_nonneg (fun z => sub_nonneg.mpr (hle z))
      ((integrable_const (1 : ℝ)).sub hq)).mpr
    rw [hsupp, measure_compl (measurableSet_singleton (0 : ℝ)) (measure_ne_top _ _),
      measure_singleton, measure_univ, tsub_zero]
    exact zero_lt_one
  rw [integral_sub (integrable_const (1 : ℝ)) hq] at hi
  have hc : (∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 T) = 1 := by simp
  rw [hc] at hi
  exact sub_pos.mp hi

end Rhone.MarkovChain.GaussianHouseOfCards
