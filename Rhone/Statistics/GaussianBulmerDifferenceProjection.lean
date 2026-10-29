/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.GaussianBulmerVariance
public import Rhone.Statistics.GaussianBulmerMaskLaplace
public import Mathlib.Probability.Independence.CharacteristicFunction
/-!
# Gaussian-source linear homologue-difference variance and characteristic function

Source: bulmer1974, p. 282; turelli2017_infinitesimal, §4, p. 48. -/
@[expose] public section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder Probability.DiploidMarginalSelection
open Finset
noncomputable def differenceLinearCLM (n : ℕ) (c : Fin n → ℝ) :
    GaussianParent n →L[ℝ] ℝ :=
  ∑ i, c i • (EuclideanSpace.proj i).comp (homologueDifferenceCLM n)
theorem differenceLinear_variance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (c : Fin n → ℝ) :
    variance (fun q => ∑ i, c i * homologueDifference q i)
      (gaussianParentLaw n G E) = ∑ i, ∑ j, c i * G i j * c j := by
  have hm (i : Fin n) : MemLp (fun q => c i * homologueDifference q i) 2
      (gaussianParentLaw n G E) := (difference_coordinate_memLp n G E i).const_mul (c i)
  have hsum : (fun q : GaussianParent n => ∑ i, c i * homologueDifference q i) =
      ∑ i, (fun q => c i * homologueDifference q i) := by
    funext q
    simp
  rw [hsum, ← covariance_self (by unfold homologueDifference; fun_prop),
    covariance_sum_sum hm hm]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, difference_covariance n G E hG]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring
theorem differenceLinear_charFun (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (c : Fin n → ℝ) (t : ℝ) :
    charFun ((gaussianParentLaw n G E).map
      (fun q => ∑ i, c i * homologueDifference q i)) t =
      Complex.ofReal (Real.exp (-(t ^ 2 / 2) * (∑ i, ∑ j, c i * G i j * c j))) := by
  have heval : (⇑(differenceLinearCLM n c) : GaussianParent n → ℝ) =
      fun q => ∑ i, c i * homologueDifference q i := by
    funext q
    simp [differenceLinearCLM, homologueDifferenceCLM, homologueDifference,
      homologueZeroCLM, homologueOneCLM]
  have hg := parentLinear_hasGaussianLaw n G E (differenceLinearCLM n c)
  rw [heval] at hg
  have hmean : (∫ q, (∑ i, c i * homologueDifference q i) ∂gaussianParentLaw n G E) = 0 := by
    rw [← heval]
    exact parentLinear_integral n G E (differenceLinearCLM n c)
  rw [hg.charFun_map_eq t]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [mul_comm _ t]
  change Complex.exp (Complex.ofReal (∫ q, t * (∑ i, c i * homologueDifference q i)
    ∂gaussianParentLaw n G E) * Complex.I -
    Complex.ofReal (variance (fun q => t * (∑ i, c i * homologueDifference q i))
      (gaussianParentLaw n G E)) / 2) = _
  rw [integral_const_mul, hmean, variance_const_mul, differenceLinear_variance n G E hG]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring
end Rhone.Statistics.GaussianBulmer
