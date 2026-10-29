/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Continuous Gaussian-effect house-of-cards model and its normalized density

Source: kingman1978_selection, eq. (1.2), (3.9), pp. 2, 5; turelli1984, sec. 3, eq. (3.1)–(3.2), pp.
149–150. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory
open scoped ENNReal NNReal
/-- Source: turelli1984, eq. (2.9), p. 142. -/
def gaussianFitness (S : ℝ) (z : ℝ) : ℝ := Real.exp (-z^2/(2*S))
/-- Source: turelli1984, eq. (3.2a), p. 150. -/
def gaussianHOCWeight (u k S : ℝ) (z : ℝ) : ℝ :=
  u/(1-k*gaussianFitness S z)
/-- Source: turelli1984, eq. (3.2b), p. 150. -/
def gaussianHOCMass (u k S : ℝ) (T : ℝ≥0) : ℝ :=
  ∫ z, gaussianHOCWeight u k S z ∂ProbabilityTheory.gaussianReal 0 T
/-- Source: turelli1984, eq. (3.2a), p. 150. -/
def gaussianHOCLaw (u k S : ℝ) (T : ℝ≥0) : MeasureTheory.Measure ℝ :=
  (ProbabilityTheory.gaussianReal 0 T).withDensity
    (fun z => ENNReal.ofReal (gaussianHOCWeight u k S z))
/-- Source: kingman1978_selection, eq. (1.2)–(1.3), p. 2; turelli1984, eq. (3.1), p. 149. -/
def gaussianHOCUpdate (u S : ℝ) (T : ℝ≥0)
    (μ : MeasureTheory.Measure ℝ) : MeasureTheory.Measure ℝ :=
  ENNReal.ofReal (1-u) •
    ((ENNReal.ofReal (∫ z, gaussianFitness S z ∂μ))⁻¹ •
      μ.withDensity (fun z => ENNReal.ofReal (gaussianFitness S z))) +
    ENNReal.ofReal u • ProbabilityTheory.gaussianReal 0 T
/-- Source: turelli1984, eq. (3.5), (3.14), pp. 151–152. -/
def gaussianHOCVariance (u k S : ℝ) (T : ℝ≥0) : ℝ :=
  ∫ z, z^2 ∂gaussianHOCLaw u k S T

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_fitness_bounds (S : ℝ) (hS : 0 < S) (z : ℝ) :
    0 < gaussianFitness S z ∧ gaussianFitness S z ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg z)) (by positivity)

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_weight_bounds (u k S : ℝ) (hu : 0 ≤ u)
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hS : 0 < S) (z : ℝ) :
    0 ≤ gaussianHOCWeight u k S z ∧ gaussianHOCWeight u k S z ≤ u/(1-k) := by
  have hw := (gaussian_fitness_bounds S hS z).2
  have hden : 1-k ≤ 1-k*gaussianFitness S z := by nlinarith
  have hpos : 0 < 1-k := sub_pos.mpr hk1
  constructor
  · exact div_nonneg hu (le_trans hpos.le hden)
  · exact div_le_div_of_nonneg_left hu hpos hden

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_weight_continuous (u k S : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hS : 0 < S) :
    Continuous (gaussianHOCWeight u k S) := by
  have hden (z : ℝ) : 1-k*gaussianFitness S z ≠ 0 := by
    have hw := (gaussian_fitness_bounds S hS z).2
    have hp : 0 < 1-k := sub_pos.mpr hk1
    nlinarith
  have hw : Continuous (gaussianFitness S) := by unfold gaussianFitness; fun_prop
  exact continuous_const.div₀ (continuous_const.sub (continuous_const.mul hw)) hden

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_weight_integrable (u k S : ℝ) (T : ℝ≥0)
    (hu : 0 ≤ u) (hk0 : 0 ≤ k) (hk1 : k < 1) (hS : 0 < S) :
    MeasureTheory.Integrable (gaussianHOCWeight u k S) (ProbabilityTheory.gaussianReal 0 T) := by
  apply Integrable.of_bound
    (gaussian_hoc_weight_continuous u k S hk0 hk1 hS).aestronglyMeasurable (u/(1-k))
  apply Filter.Eventually.of_forall
  intro z
  have hb := gaussian_hoc_weight_bounds u k S hu hk0 hk1 hS z
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_weighted_fitness_integrable (u k S : ℝ) (T : ℝ≥0)
    (hu : 0 ≤ u) (hk0 : 0 ≤ k) (hk1 : k < 1) (hS : 0 < S) :
    MeasureTheory.Integrable (fun z => gaussianHOCWeight u k S z*gaussianFitness S z)
      (ProbabilityTheory.gaussianReal 0 T) := by
  have hw : Continuous (gaussianFitness S) := by unfold gaussianFitness; fun_prop
  apply Integrable.of_bound
    ((gaussian_hoc_weight_continuous u k S hk0 hk1 hS).mul hw).aestronglyMeasurable
    (u/(1-k))
  apply Filter.Eventually.of_forall
  intro z
  have hb := gaussian_hoc_weight_bounds u k S hu hk0 hk1 hS z
  have hf := gaussian_fitness_bounds S hS z
  change ‖gaussianHOCWeight u k S z*gaussianFitness S z‖ ≤ u/(1-k)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 hf.1.le)]
  nlinarith

/-- Source: turelli1984, p. 151. -/
theorem gaussian_hoc_normalized_mean_fitness (u k S : ℝ) (T : ℝ≥0)
    (hu : 0 ≤ u) (hk0 : 0 < k) (hk1 : k < 1) (hS : 0 < S)
    (hmass : gaussianHOCMass u k S T = 1) :
    (∫ z, gaussianHOCWeight u k S z*gaussianFitness S z
      ∂ProbabilityTheory.gaussianReal 0 T) = (1-u)/k := by
  have hbalance (z : ℝ) : gaussianHOCWeight u k S z-
      k*(gaussianHOCWeight u k S z*gaussianFitness S z) = u := by
    have hw := (gaussian_fitness_bounds S hS z).2
    have hden : 1-k*gaussianFitness S z ≠ 0 := by nlinarith
    unfold gaussianHOCWeight
    field_simp [hden]
  have hfun : (fun z => gaussianHOCWeight u k S z-
      k*(gaussianHOCWeight u k S z*gaussianFitness S z)) = fun _ => u := funext hbalance
  have hi := congrArg (fun f : ℝ → ℝ => ∫ z, f z ∂gaussianReal 0 T) hfun
  rw [integral_sub (gaussian_hoc_weight_integrable u k S T hu hk0.le hk1 hS)
    ((gaussian_hoc_weighted_fitness_integrable u k S T hu hk0.le hk1 hS).const_mul k),
    integral_const_mul] at hi
  have hc : (∫ _ : ℝ, u ∂gaussianReal 0 T) = u := by simp
  rw [hc] at hi
  change gaussianHOCMass u k S T-k*(∫ z, gaussianHOCWeight u k S z*gaussianFitness S z
    ∂gaussianReal 0 T) = u at hi
  rw [hmass] at hi
  apply (eq_div_iff (ne_of_gt hk0)).mpr
  linarith

/-- Source: turelli1984, eq. (3.1)–(3.2a), pp. 149–150; barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_pointwise_balance (u k S : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hS : 0 < S) (z : ℝ) :
    k*gaussianHOCWeight u k S z*gaussianFitness S z+u = gaussianHOCWeight u k S z := by
  have hw := (gaussian_fitness_bounds S hS z).2
  have hden : 1-k*gaussianFitness S z ≠ 0 := by nlinarith
  unfold gaussianHOCWeight
  field_simp [hden]
  ring

/-- Source: turelli1984, eq. (3.1)–(3.2b), pp. 149–150; barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_stationary_law
    (u k S : ℝ) (T : ℝ≥0) (hu0 : 0 < u) (hu1 : u < 1)
    (hS : 0 < S) (hT : 0 < T) (hk0 : 1 - u < k) (hk1 : k < 1)
    (hmass : gaussianHOCMass u k S T = 1) :
    MeasureTheory.IsProbabilityMeasure (gaussianHOCLaw u k S T) ∧
      gaussianHOCUpdate u S T (gaussianHOCLaw u k S T) = gaussianHOCLaw u k S T := by
  have _ := hT
  have hk : 0 < k := lt_trans (sub_pos.mpr hu1) hk0
  have hq := gaussian_hoc_weight_integrable u k S T hu0.le hk.le hk1 hS
  have hb := fun z => gaussian_hoc_weight_bounds u k S hu0.le hk.le hk1 hS z
  have hQ : Measurable (fun z => ENNReal.ofReal (gaussianHOCWeight u k S z)) :=
    ENNReal.measurable_ofReal.comp (gaussian_hoc_weight_continuous u k S hk.le hk1 hS).measurable
  have hw : Continuous (gaussianFitness S) := by unfold gaussianFitness; fun_prop
  have hW : Measurable (fun z => ENNReal.ofReal (gaussianFitness S z)) :=
    ENNReal.measurable_ofReal.comp hw.measurable
  constructor
  · constructor
    unfold gaussianHOCLaw
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hq (Filter.Eventually.of_forall fun z => (hb z).1)]
    change ENNReal.ofReal (gaussianHOCMass u k S T) = 1
    simp only [hmass, ENNReal.ofReal_one]
  · have hmean : (∫ z, gaussianFitness S z ∂gaussianHOCLaw u k S T) = (1-u)/k := by
      unfold gaussianHOCLaw
      rw [integral_withDensity_eq_integral_toReal_smul hQ
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (hb _).1, smul_eq_mul]
      exact gaussian_hoc_normalized_mean_fitness u k S T hu0.le hk hk1 hS hmass
    have hcoef : ENNReal.ofReal (1-u)*(ENNReal.ofReal ((1-u)/k))⁻¹ = ENNReal.ofReal k := by
      rw [← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos
        (div_pos (sub_pos.mpr hu1) hk)]
      congr 1
      field_simp [ne_of_gt (sub_pos.mpr hu1)]
    unfold gaussianHOCUpdate
    rw [hmean, smul_smul, hcoef]
    unfold gaussianHOCLaw
    rw [← withDensity_mul (gaussianReal 0 T) hQ hW,
      ← withDensity_smul _ (hQ.mul hW), ← withDensity_const,
      ← withDensity_add_left ((hQ.mul hW).const_smul (ENNReal.ofReal k))]
    apply withDensity_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (hb z).1, ← ENNReal.ofReal_mul hk.le,
      ← ENNReal.ofReal_add (mul_nonneg hk.le (mul_nonneg (hb z).1
        (gaussian_fitness_bounds S hS z).1.le)) hu0.le]
    simpa only [mul_assoc] using congrArg ENNReal.ofReal
      (gaussian_hoc_pointwise_balance u k S hk.le hk1 hS z)

end Rhone.MarkovChain.GaussianHouseOfCards
