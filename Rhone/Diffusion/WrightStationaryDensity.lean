/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Diffusion.GeneratorC2
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Wright's stationary density for the generator with mutation

Source: ewens2004, eq. (5.70), p. 174, sec. 4.5, eq. (4.44)–(4.46), pp. 145–146; wright1937, p. 312,
eq. (11); crow_kimura1970, sec. 9.1, eq. (9.1.3), pp. 434–435, sec. 9.2, p. 441; wright1931, p. 123.
-/

@[expose] public section

namespace Rhone.Diffusion

open Set Filter Topology MeasureTheory Polynomial

noncomputable def wrightDensity (θ₁ θ₂ x : ℝ) : ℝ := x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1)

theorem flux_eq_rpow {θ₁ θ₂ x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x * (1 - x) * wrightDensity θ₁ θ₂ x = x ^ θ₁ * (1 - x) ^ θ₂ := by
  have h1 : (1 - x) ≠ 0 := by linarith
  unfold wrightDensity
  rw [Real.rpow_sub_one hx0.ne', Real.rpow_sub_one h1]
  field_simp

theorem hasDerivAt_wrightDensity_flux (θ₁ θ₂ : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => y * (1 - y) * wrightDensity θ₁ θ₂ y)
      ((θ₁ * (1 - x) - θ₂ * x) * wrightDensity θ₁ θ₂ x) x := by
  have h1 : (1 - x) ≠ 0 := by linarith
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id' x).const_sub 1
  have ha : HasDerivAt (fun y : ℝ => y ^ θ₁) (θ₁ * x ^ (θ₁ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
  have hb0 : HasDerivAt (fun y : ℝ => y ^ θ₂) (θ₂ * (1 - x) ^ (θ₂ - 1)) (1 - x) :=
    Real.hasDerivAt_rpow_const (Or.inl h1)
  have hb : HasDerivAt (fun y : ℝ => (1 - y) ^ θ₂) (θ₂ * (1 - x) ^ (θ₂ - 1) * -1) x :=
    hb0.comp x hs
  have hab := ha.mul hb
  have hev : (fun y : ℝ => y ^ θ₁ * (1 - y) ^ θ₂) =ᶠ[𝓝 x]
      fun y => y * (1 - y) * wrightDensity θ₁ θ₂ y := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
    exact (flux_eq_rpow hy.1 hy.2).symm
  refine (hab.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  unfold wrightDensity
  rw [Real.rpow_sub_one hx0.ne', Real.rpow_sub_one h1]
  field_simp
  ring

theorem wrightDensity_zero_flux (θ₁ θ₂ : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    1 / 2 * deriv (fun y => y * (1 - y) * wrightDensity θ₁ θ₂ y) x =
      1 / 2 * (θ₁ * (1 - x) - θ₂ * x) * wrightDensity θ₁ θ₂ x := by
  rw [(hasDerivAt_wrightDensity_flux θ₁ θ₂ hx0 hx1).deriv]
  ring

private theorem ofReal_wrightDensity {θ₁ θ₂ x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((wrightDensity θ₁ θ₂ x : ℝ) : ℂ) =
      (x : ℂ) ^ ((θ₁ : ℂ) - 1) * (1 - (x : ℂ)) ^ ((θ₂ : ℂ) - 1) := by
  have h1 : 0 ≤ 1 - x := by linarith
  have a := Complex.ofReal_cpow hx0 (θ₁ - 1)
  have b := Complex.ofReal_cpow h1 (θ₂ - 1)
  push_cast at a b
  unfold wrightDensity
  push_cast
  rw [a, b]

theorem intervalIntegrable_wrightDensity {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    IntervalIntegrable (wrightDensity θ₁ θ₂) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent (u := (θ₁ : ℂ)) (v := (θ₂ : ℂ))
    (by simpa using h₁) (by simpa using h₂)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hc ⊢
  have hre := hc.re
  refine hre.congr_fun (fun x hx => ?_) measurableSet_Ioc
  have e := ofReal_wrightDensity (θ₁ := θ₁) (θ₂ := θ₂) hx.1.le hx.2
  simp only [← e, RCLike.re_to_complex, Complex.ofReal_re]

theorem integrableOn_wrightDensity {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    IntegrableOn (wrightDensity θ₁ θ₂) (Ioo 0 1) := by
  have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegrable_wrightDensity h₁ h₂)
  exact this.mono_set Ioo_subset_Ioc_self

theorem integral_wrightDensity {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    ∫ x in (0 : ℝ)..1, wrightDensity θ₁ θ₂ x = ProbabilityTheory.beta θ₁ θ₂ := by
  rw [ProbabilityTheory.beta_eq_betaIntegralReal θ₁ θ₂ h₁ h₂, Complex.betaIntegral]
  have e : ∫ x in (0 : ℝ)..1, (x : ℂ) ^ ((θ₁ : ℂ) - 1) * (1 - (x : ℂ)) ^ ((θ₂ : ℂ) - 1) =
      ((∫ x in (0 : ℝ)..1, wrightDensity θ₁ θ₂ x : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le zero_le_one] at hx
    exact (ofReal_wrightDensity hx.1 hx.2).symm
  rw [e, Complex.ofReal_re]

theorem integral_wfGeneratorMut_polynomial_mul_wrightDensity {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁)
    (h₂ : 0 < θ₂) (p : ℝ[X]) :
    ∫ x in (0 : ℝ)..1,
      wfGeneratorMut θ₁ θ₂ (fun y => p.eval y) x * wrightDensity θ₁ θ₂ x = 0 := by
  set q : ℝ[X] := derivative p with hq
  set c : ℝ[X] := C (1 / 2) * (X * (1 - X) * derivative q +
    (C θ₁ * (1 - X) - C θ₂ * X) * q) with hc
  have hint : ∀ x, wfGeneratorMut θ₁ θ₂ (fun y => p.eval y) x * wrightDensity θ₁ θ₂ x =
      c.eval x * wrightDensity θ₁ θ₂ x := by
    intro x
    have hd : deriv (fun y => p.eval y) x = q.eval x := p.deriv
    rw [wfGeneratorMut, wfGenerator_eval, hd, hc]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_sub, eval_one]
    ring
  simp_rw [hint]
  set G : ℝ → ℝ := fun y => 1 / 2 * (y ^ θ₁ * (1 - y) ^ θ₂ * q.eval y) with hG
  have hGc : Continuous G := by
    have a := Real.continuous_rpow_const h₁.le
    have b : Continuous fun y : ℝ => (1 - y) ^ θ₂ :=
      (Real.continuous_rpow_const h₂.le).comp (continuous_const.sub continuous_id)
    have c' : Continuous fun y : ℝ => q.eval y := q.continuous
    exact continuous_const.mul ((a.mul b).mul c')
  have hG0 : G 0 = 0 := by simp [hG, Real.zero_rpow h₁.ne']
  have hG1 : G 1 = 0 := by simp [hG, Real.zero_rpow h₂.ne']
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (c.eval x * wrightDensity θ₁ θ₂ x) x := by
    intro x hx
    have hf := hasDerivAt_wrightDensity_flux θ₁ θ₂ hx.1 hx.2
    have hqd : HasDerivAt (fun y => q.eval y) ((derivative q).eval x) x := q.hasDerivAt x
    have hev : (fun y => 1 / 2 * (y * (1 - y) * wrightDensity θ₁ θ₂ y * q.eval y)) =ᶠ[𝓝 x] G := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [hG]
      simp only
      rw [flux_eq_rpow hy.1 hy.2]
    have h := ((hf.mul hqd).const_mul (1 / 2)).congr_of_eventuallyEq hev.symm
    refine h.congr_deriv ?_
    rw [hc]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_sub, eval_one]
    ring
  have hcont : IntervalIntegrable (fun x => c.eval x * wrightDensity θ₁ θ₂ x) volume 0 1 :=
    (intervalIntegrable_wrightDensity h₁ h₂).continuousOn_mul
      (c.continuous.continuousOn)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hGc.continuousOn hder
    hcont, hG0, hG1, sub_zero]

end Rhone.Diffusion
