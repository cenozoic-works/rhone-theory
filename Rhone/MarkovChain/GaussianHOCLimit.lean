/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHOCRescaling
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Joint rare-mutation and small-effect limit for the Gaussian stationary law

Source: turelli1984, eq. (3.8), (3.14), pp. 151–152; barton_turelli1987, pp. 158, 163. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- Source: turelli1984, eq. (3.8), (3.14), pp. 151–152; barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_joint_rare_mutation_small_effect_limit
    (S : ℝ) (hS : 0 < S) (u k : ℕ → ℝ) (T : ℕ → ℝ≥0)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1)
    (hT : ∀ n, 0 < T n) (hk0 : ∀ n, 1 - u n < k n) (hk1 : ∀ n, k n < 1)
    (hmass : ∀ n, gaussianHOCMass (u n) (k n) S (T n) = 1)
    (hsmall : Filter.Tendsto (fun n => (T n : ℝ) / S) Filter.atTop (nhds 0))
    (hrare : Filter.Tendsto (fun n => u n * S / (T n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => gaussianHOCVariance (u n) (k n) S (T n)/(2*S*u n))
      Filter.atTop (nhds 1) := by
  have _ := hmass
  have hkpos (n : ℕ) : 0 < k n := by linarith [hk0 n, hu1 n]
  have hTpos (n : ℕ) : 0 < (T n : ℝ) := NNReal.coe_pos.mpr (hT n)
  have hulim : Tendsto u atTop (nhds 0) := by
    have hm := hrare.mul hsmall
    simp only [mul_zero] at hm
    convert hm using 1
    ext n
    field_simp [ne_of_gt (hTpos n)]
  have hklim : Tendsto k atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => 1-u n) atTop (nhds 1) by
        simpa using tendsto_const_nhds.sub hulim) tendsto_const_nhds
    · exact fun n => (hk0 n).le
    · exact fun n => (hk1 n).le
  have hTlim : Tendsto (fun n => (T n : ℝ)) atTop (nhds 0) := by
    have hm := hsmall.mul_const S
    simp only [zero_mul] at hm
    convert hm using 1
    ext n
    field_simp
  have hdlim : Tendsto (fun n => (1-k n)*S/(T n : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero (fun n => div_nonneg
      (mul_nonneg (sub_nonneg.mpr (hk1 n).le) hS.le) (hTpos n).le) (fun n => ?_) hrare
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith [hk0 n]) hS.le) (hTpos n).le
  let F := fun n y => (Real.sqrt (T n : ℝ)*y)^2*
    gaussianHOCWeight (u n) (k n) S (Real.sqrt (T n : ℝ)*y)/(2*S*u n)
  have hFbounds (n : ℕ) (y : ℝ) :=
    gaussian_hoc_scaled_second_moment_pointwise_bounds (u n) (k n) S
      (Real.sqrt (T n : ℝ)*y) (hu0 n) (hkpos n) (hk1 n) hS
  have hFlim (y : ℝ) (hy : y ≠ 0) : Tendsto (fun n => F n y) atTop (nhds 1) := by
    have hlo : Tendsto (fun n => y^2/(y^2+2*((1-k n)*S/(T n : ℝ))))
        atTop (nhds 1) := by
      have hm := (tendsto_const_nhds (x := y^2) (f := atTop)).div
        (tendsto_const_nhds.add (hdlim.const_mul 2))
        (show y^2+2*0 ≠ 0 by simpa using pow_ne_zero 2 hy)
      change Tendsto (fun n => y^2/(y^2+2*((1-k n)*S/(T n : ℝ))))
        atTop (nhds (y^2/(y^2+2*0))) at hm
      simpa [pow_ne_zero 2 hy] using hm
    have hhi : Tendsto (fun n => (1+(T n : ℝ)*y^2/(2*S))/k n) atTop (nhds 1) := by
      have hm := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add
        ((hTlim.mul_const (y^2)).div_const (2*S))).div
        hklim (by norm_num : (1 : ℝ) ≠ 0)
      change Tendsto (fun n => (1+(T n : ℝ)*y^2/(2*S))/k n)
        atTop (nhds ((1+0*y^2/(2*S))/1)) at hm
      simpa using hm
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    · intro n
      have hb := (hFbounds n y).1
      dsimp [F]
      convert hb using 1
      rw [mul_pow, Real.sq_sqrt (hTpos n).le]
      have hd : y^2+2*((1-k n)*S/(T n : ℝ)) ≠ 0 := ne_of_gt (by
        have := hk1 n
        have := hTpos n
        positivity)
      have hd' : (T n : ℝ)*y^2+2*S*(1-k n) ≠ 0 := ne_of_gt (by
        have := hk1 n
        have := hTpos n
        positivity)
      field_simp [ne_of_gt (hTpos n), hd, hd']
    · intro n
      simpa only [F, mul_pow, Real.sq_sqrt (hTpos n).le] using (hFbounds n y).2
  have hsq : Integrable (fun y : ℝ => y^2) (gaussianReal 0 1) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) 2
  have hevent : ∀ᶠ n in atTop, (1/2 : ℝ) ≤ k n ∧ (T n : ℝ)/S ≤ 1 := by
    filter_upwards [hklim.eventually (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1)),
      hsmall.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hn'
    exact ⟨hn, hn'⟩
  have hbound : ∀ᶠ n in atTop, ∀ᵐ y ∂gaussianReal 0 1, ‖F n y‖ ≤ 2+y^2 := by
    filter_upwards [hevent] with n hn
    apply Eventually.of_forall
    intro y
    have hnonneg : 0 ≤ F n y := by
      dsimp [F]
      exact div_nonneg (mul_nonneg (sq_nonneg _)
        (gaussian_hoc_weight_bounds (u n) (k n) S (hu0 n).le
          (hkpos n).le (hk1 n) hS _).1)
          (mul_nonneg (mul_nonneg (by norm_num) hS.le) (hu0 n).le)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    apply (hFbounds n y).2.trans
    rw [mul_pow, Real.sq_sqrt (hTpos n).le]
    apply (div_le_iff₀ (hkpos n)).mpr
    have ht := (div_le_iff₀ hS).mp hn.2
    have hy := mul_le_mul_of_nonneg_right ht (sq_nonneg y)
    have hh := mul_le_mul_of_nonneg_right hn.1 (by positivity : 0 ≤ 2+y^2)
    have hh' := (div_le_iff₀ (by positivity : 0 < 2*S)).mpr
      (show (T n : ℝ)*y^2 ≤ y^2/2*(2*S) by nlinarith)
    nlinarith
  have hFmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) (gaussianReal 0 1) := by
    apply Eventually.of_forall
    intro n
    have hcont := gaussian_hoc_weight_continuous (u n) (k n) S (hkpos n).le (hk1 n) hS
    have : Continuous (F n) := by dsimp [F]; fun_prop
    exact this.aestronglyMeasurable
  have hnull : ∀ᵐ y ∂gaussianReal 0 1, y ≠ 0 := by
    have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    rw [ae_iff]
    simp
  have hlimit := tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => 2+y^2)
    hFmeas hbound ((integrable_const 2).add hsq)
    (hnull.mono fun y hy => hFlim y hy)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
    hlimit.congr' (Eventually.of_forall fun n =>
      (gaussian_hoc_scaled_variance_as_standard_integral (u n) (k n) S (T n)
        (hu0 n) (hkpos n) (hk1 n) hS).symm)

end Rhone.MarkovChain.GaussianHouseOfCards
