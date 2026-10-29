/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Diffusion.WrightStationaryDensity
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Wright's stationary density with selection, and uniqueness of zero-flux solutions

Source: ewens2004, eq. (5.72), p. 175, sec. 4.5, eq. (4.44)–(4.46), pp. 145–146; wright1937, p. 313,
eq. (16); crow_kimura1970, sec. 9.1, eq. (9.1.3), pp. 434–435, sec. 9.3, p. 442; wright1937, p. 312,
eq. (13)–(15). -/

@[expose] public section

namespace Rhone.Diffusion

open Set Filter Topology MeasureTheory Polynomial

noncomputable def wrightDensitySel (σ θ₁ θ₂ x : ℝ) : ℝ :=
  Real.exp (2 * σ * x) * wrightDensity θ₁ θ₂ x

theorem wrightDensitySel_zero (θ₁ θ₂ x : ℝ) :
    wrightDensitySel 0 θ₁ θ₂ x = wrightDensity θ₁ θ₂ x := by
  simp [wrightDensitySel]

theorem wrightDensitySel_pos (σ θ₁ θ₂ : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < wrightDensitySel σ θ₁ θ₂ x := by
  unfold wrightDensitySel wrightDensity
  have h1 : 0 < 1 - x := by linarith
  exact mul_pos (Real.exp_pos _) (mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.rpow_pos_of_pos h1 _))

private theorem hasDerivAt_exp_lin (σ x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (2 * σ * y)) (Real.exp (2 * σ * x) * (2 * σ)) x := by
  simpa using ((hasDerivAt_id x).const_mul (2 * σ)).exp

theorem hasDerivAt_wrightDensitySel_flux (σ θ₁ θ₂ : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => y * (1 - y) * wrightDensitySel σ θ₁ θ₂ y)
      ((2 * σ * (x * (1 - x)) + θ₁ * (1 - x) - θ₂ * x) * wrightDensitySel σ θ₁ θ₂ x) x := by
  have h := (hasDerivAt_exp_lin σ x).mul (hasDerivAt_wrightDensity_flux θ₁ θ₂ hx0 hx1)
  have e : (fun y => y * (1 - y) * wrightDensitySel σ θ₁ θ₂ y) =
      fun y => Real.exp (2 * σ * y) * (y * (1 - y) * wrightDensity θ₁ θ₂ y) :=
    funext fun y => by
      unfold wrightDensitySel
      ring
  rw [e]
  refine h.congr_deriv ?_
  unfold wrightDensitySel
  ring

private theorem eq_of_hasDerivAt_zero' {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn F (Icc a b)) (hd : ∀ y ∈ Ioo a b, HasDerivAt F 0 y) : F a = F b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · obtain ⟨c, hc', hcd⟩ := exists_deriv_eq_slope F h hc
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    rw [(hd c hc').deriv] at hcd
    have := hcd.symm
    rw [div_eq_zero_iff] at this
    rcases this with h0 | h0
    · linarith
    · exact absurd h0 (sub_ne_zero.mpr h.ne')

theorem zero_flux_unique (σ θ₁ θ₂ : ℝ) {g : ℝ → ℝ}
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => y * (1 - y) * g y)
      ((2 * σ * (x * (1 - x)) + θ₁ * (1 - x) - θ₂ * x) * g x) x) :
    ∃ c : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, g x = c * wrightDensitySel σ θ₁ θ₂ x := by
  set R : ℝ → ℝ := fun y =>
    (y * (1 - y) * g y) / (y * (1 - y) * wrightDensitySel σ θ₁ θ₂ y) with hR
  have hden : ∀ y ∈ Ioo (0 : ℝ) 1, y * (1 - y) * wrightDensitySel σ θ₁ θ₂ y ≠ 0 := fun y hy =>
    (mul_pos (mul_pos hy.1 (by linarith [hy.2])) (wrightDensitySel_pos σ θ₁ θ₂ hy.1 hy.2)).ne'
  have hRd : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt R 0 y := by
    intro y hy
    have h := (hg y hy).div (hasDerivAt_wrightDensitySel_flux σ θ₁ θ₂ hy.1 hy.2) (hden y hy)
    refine h.congr_deriv ?_
    have h0 : y ≠ 0 := hy.1.ne'
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    have hw : wrightDensitySel σ θ₁ θ₂ y ≠ 0 := (wrightDensitySel_pos σ θ₁ θ₂ hy.1 hy.2).ne'
    field_simp
    ring
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem : ∀ a b : ℝ, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a ≤ b → R a = R b := by
    intro a b ha hb hab
    refine eq_of_hasDerivAt_zero' (F := R) hab ?_
      (fun t ht => hRd t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
    intro t ht
    exact (hRd t ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩).continuousAt
      |>.continuousWithinAt
  refine ⟨R (1 / 2), fun x hx => ?_⟩
  have hRx : R x = R (1 / 2) := by
    rcases le_total x (1 / 2) with hle | hle
    · exact hmem _ _ hx hhalf hle
    · exact (hmem _ _ hhalf hx hle).symm
  rw [← hRx, hR]
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hw : wrightDensitySel σ θ₁ θ₂ x ≠ 0 := (wrightDensitySel_pos σ θ₁ θ₂ hx.1 hx.2).ne'
  field_simp

theorem intervalIntegrable_wrightDensitySel (σ : ℝ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    IntervalIntegrable (wrightDensitySel σ θ₁ θ₂) volume 0 1 :=
  (intervalIntegrable_wrightDensity h₁ h₂).continuousOn_mul
    (Continuous.continuousOn (by fun_prop))

theorem integral_wrightDensitySel_pos (σ : ℝ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) :
    0 < ∫ x in (0 : ℝ)..1, wrightDensitySel σ θ₁ θ₂ x :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_wrightDensitySel σ h₁ h₂)
    (fun _ hx => wrightDensitySel_pos σ θ₁ θ₂ hx.1 hx.2) zero_lt_one

theorem zero_flux_unique_of_integral_eq_one (σ : ℝ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂)
    {g : ℝ → ℝ}
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => y * (1 - y) * g y)
      ((2 * σ * (x * (1 - x)) + θ₁ * (1 - x) - θ₂ * x) * g x) x)
    (hint : ∫ x in (0 : ℝ)..1, g x = 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1,
      g x = wrightDensitySel σ θ₁ θ₂ x / ∫ y in (0 : ℝ)..1, wrightDensitySel σ θ₁ θ₂ y := by
  obtain ⟨c, hc⟩ := zero_flux_unique σ θ₁ θ₂ hg
  have hZ := integral_wrightDensitySel_pos σ h₁ h₂
  have hcZ : c * ∫ y in (0 : ℝ)..1, wrightDensitySel σ θ₁ θ₂ y = 1 := by
    have e : c * ∫ y in (0 : ℝ)..1, wrightDensitySel σ θ₁ θ₂ y = ∫ x in (0 : ℝ)..1, g x := by
      rw [← intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun x hx => (hc x hx).symm
    rw [e, hint]
  intro x hx
  rw [hc x hx, eq_div_iff hZ.ne']
  linear_combination wrightDensitySel σ θ₁ θ₂ x * hcZ

theorem integral_wfGeneratorForces_polynomial_mul_wrightDensitySel (σ : ℝ) {θ₁ θ₂ : ℝ}
    (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (p : ℝ[X]) :
    ∫ x in (0 : ℝ)..1,
      wfGeneratorForces σ θ₁ θ₂ (fun y => p.eval y) x * wrightDensitySel σ θ₁ θ₂ x = 0 := by
  set q : ℝ[X] := derivative p with hq
  set c : ℝ[X] := C (1 / 2) * (X * (1 - X) * derivative q +
    (C (2 * σ) * (X * (1 - X)) + C θ₁ * (1 - X) - C θ₂ * X) * q) with hc
  have hint : ∀ x, wfGeneratorForces σ θ₁ θ₂ (fun y => p.eval y) x * wrightDensitySel σ θ₁ θ₂ x =
      c.eval x * wrightDensitySel σ θ₁ θ₂ x := by
    intro x
    have hd : deriv (fun y => p.eval y) x = q.eval x := p.deriv
    rw [wfGeneratorForces, wfGenerator_eval, hd, hc]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_sub, eval_one]
    ring
  simp_rw [hint]
  set G : ℝ → ℝ := fun y =>
    1 / 2 * (Real.exp (2 * σ * y) * (y ^ θ₁ * (1 - y) ^ θ₂) * q.eval y) with hG
  have hGc : Continuous G := by
    have a := Real.continuous_rpow_const h₁.le
    have b : Continuous fun y : ℝ => (1 - y) ^ θ₂ :=
      (Real.continuous_rpow_const h₂.le).comp (continuous_const.sub continuous_id)
    have c' : Continuous fun y : ℝ => q.eval y := q.continuous
    have e : Continuous fun y : ℝ => Real.exp (2 * σ * y) := by fun_prop
    exact continuous_const.mul ((e.mul (a.mul b)).mul c')
  have hG0 : G 0 = 0 := by simp [hG, Real.zero_rpow h₁.ne']
  have hG1 : G 1 = 0 := by simp [hG, Real.zero_rpow h₂.ne']
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt G (c.eval x * wrightDensitySel σ θ₁ θ₂ x) x := by
    intro x hx
    have hf := hasDerivAt_wrightDensitySel_flux σ θ₁ θ₂ hx.1 hx.2
    have hqd : HasDerivAt (fun y => q.eval y) ((derivative q).eval x) x := q.hasDerivAt x
    have hev : (fun y => 1 / 2 * (y * (1 - y) * wrightDensitySel σ θ₁ θ₂ y * q.eval y))
        =ᶠ[𝓝 x] G := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [hG]
      simp only
      rw [← flux_eq_rpow (θ₁ := θ₁) (θ₂ := θ₂) hy.1 hy.2]
      unfold wrightDensitySel
      ring
    have h := ((hf.mul hqd).const_mul (1 / 2)).congr_of_eventuallyEq hev.symm
    refine h.congr_deriv ?_
    rw [hc]
    simp only [eval_mul, eval_C, eval_add, eval_X, eval_sub, eval_one]
    ring
  have hcont : IntervalIntegrable (fun x => c.eval x * wrightDensitySel σ θ₁ θ₂ x) volume 0 1 :=
    (intervalIntegrable_wrightDensitySel σ h₁ h₂).continuousOn_mul
      (c.continuous.continuousOn)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hGc.continuousOn hder
    hcont, hG0, hG1, sub_zero]

end Rhone.Diffusion
