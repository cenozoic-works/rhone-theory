/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanRiccati
public import Rhone.Statistics.Identifiability.PanFiveSpectrum

/-! # Uniqueness of reconstruction from the scalar observable coefficients -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def riccatiDifferenceRate (rate D Ddot R₁ R₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  rate x/(2*D x)*(R₁ x+R₂ x)-(rate x*D x+Ddot x)/(2*D x)+6*rate x

set_option backward.isDefEq.respectTransparency false in
theorem panRiccati_solution_unique (rate D Ddot N R₁ R₂ : ℝ → ℝ) (t : ℝ)
    (hD : ∀ x, D x ≠ 0)
    (hK : LocallyIntegrable (riccatiDifferenceRate rate D Ddot R₁ R₂) volume)
    (h₁ : AbsolutelyContinuousOnInterval R₁ 0 t)
    (h₂ : AbsolutelyContinuousOnInterval R₂ 0 t)
    (hzero : R₁ 0 = R₂ 0)
    (he₁ : ∀ᵐ x, x ∈ uIcc 0 t →
      HasDerivAt R₁ (panRiccatiDrift (rate x) (D x) (Ddot x) (N x) (R₁ x)) x)
    (he₂ : ∀ᵐ x, x ∈ uIcc 0 t →
      HasDerivAt R₂ (panRiccatiDrift (rate x) (D x) (Ddot x) (N x) (R₂ x)) x) :
    R₁ t = R₂ t := by
  apply sub_eq_zero.mp
  apply zero_solution_scaled_clock (fun x => R₁ x-R₂ x)
    (riccatiDifferenceRate rate D Ddot R₁ R₂) hK 1 t (h₁.sub h₂)
    (by simp [hzero])
  filter_upwards [he₁,he₂] with x hx₁ hx₂
  intro hx
  convert! (hx₁ hx).sub (hx₂ hx) using 1
  rw [panRiccati_difference _ _ _ _ _ _ (hD x)]
  unfold riccatiDifferenceRate
  ring

theorem riccatiDifferenceRate_continuous (rate D Ddot R₁ R₂ : ℝ → ℝ)
    (hr : Continuous rate) (hD : Continuous D) (hd : Continuous Ddot)
    (h₁ : Continuous R₁) (h₂ : Continuous R₂) (hn : ∀ x, D x ≠ 0) :
    Continuous (riccatiDifferenceRate rate D Ddot R₁ R₂) := by
  unfold riccatiDifferenceRate
  have hden : ∀ x, 2*D x ≠ 0 := fun x => mul_ne_zero (by norm_num) (hn x)
  exact (((hr.div (continuous_const.mul hD) hden).mul (h₁.add h₂)).sub
    (((hr.mul hD).add hd).div (continuous_const.mul hD) hden)).add
      (continuous_const.mul hr)

end Rhone.Statistics.Identifiability
