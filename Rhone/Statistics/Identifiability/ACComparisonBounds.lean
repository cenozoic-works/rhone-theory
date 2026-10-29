/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AbsolutelyContinuousClock

/-! # Absolutely continuous scalar comparison -/

@[expose] public section

open Set Filter MeasureTheory

namespace Rhone.Statistics.Identifiability

theorem ac_endpoint_le_of_ae_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → deriv f x ≤ 0) :
    f b ≤ f a := by
  have hle : (∫ x in a..b, deriv f x) ≤ ∫ _ in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv
      intervalIntegrable_const
    change ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x ≤ 0
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hderiv] with x hx hxmem
    exact hx (by simpa only [uIcc_of_le hab] using hxmem)
  rw [hf.integral_deriv_eq_sub] at hle
  simpa only [intervalIntegral.integral_zero, sub_nonpos] using hle

theorem ac_endpoint_le_of_ae_hasDerivAt_nonpos {f fDot : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hfd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (fDot x) x)
    (hnonpos : ∀ᵐ x, x ∈ uIcc a b → fDot x ≤ 0) :
    f b ≤ f a := by
  apply ac_endpoint_le_of_ae_deriv_nonpos hab hf
  filter_upwards [hfd, hnonpos] with x hdx hnx hx
  rw [(hdx hx).deriv]
  exact hnx hx

theorem ac_antitoneOn_of_ae_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → deriv f x ≤ 0) :
    AntitoneOn f (uIcc a b) := by
  intro x hx y hy hxy
  have hsub : uIcc x y ⊆ uIcc a b := uIcc_subset_uIcc hx hy
  apply ac_endpoint_le_of_ae_deriv_nonpos hxy (hf.mono hsub)
  filter_upwards [hderiv] with z hz hzmem
  exact hz (hsub hzmem)

theorem ac_antitoneOn_of_ae_hasDerivAt_nonpos {f fDot : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (fDot x) x)
    (hnonpos : ∀ᵐ x, x ∈ uIcc a b → fDot x ≤ 0) :
    AntitoneOn f (uIcc a b) := by
  apply ac_antitoneOn_of_ae_deriv_nonpos hf
  filter_upwards [hfd, hnonpos] with x hdx hnx hx
  rw [(hdx hx).deriv]
  exact hnx hx

theorem ac_comparison_upper (f fDot H HDot : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hfd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (fDot x) x)
    (hHd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt H (HDot x) x)
    (hle : ∀ᵐ x, x ∈ uIcc a b → fDot x ≤ -HDot x * f x) :
    f b ≤ f a * Real.exp (H a - H b) := by
  have hac : AbsolutelyContinuousOnInterval (fun x => f x * Real.exp (H x)) a b :=
    hf.mul (ac_exp hH)
  have hg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt
      (fun y => f y * Real.exp (H y))
      (fDot x * Real.exp (H x) + f x * (Real.exp (H x) * HDot x)) x := by
    filter_upwards [hfd, hHd] with x hfx hHx hx
    exact (hfx hx).mul (hHx hx).exp
  have hgnonpos : ∀ᵐ x, x ∈ uIcc a b →
      fDot x * Real.exp (H x) + f x * (Real.exp (H x) * HDot x) ≤ 0 := by
    filter_upwards [hle] with x hx hxmem
    have h := mul_le_mul_of_nonneg_right (hx hxmem) (Real.exp_pos (H x)).le
    nlinarith
  have h := ac_endpoint_le_of_ae_hasDerivAt_nonpos hab hac hg hgnonpos
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (H b))).mp
  calc
    f b * Real.exp (H b) ≤ f a * Real.exp (H a) := h
    _ = (f a * Real.exp (H a - H b)) * Real.exp (H b) := by
      rw [mul_assoc, ← Real.exp_add, sub_add_cancel]

theorem ac_comparison_lower (f fDot H HDot : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hfd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (fDot x) x)
    (hHd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt H (HDot x) x)
    (hle : ∀ᵐ x, x ∈ uIcc a b → -HDot x * f x ≤ fDot x) :
    f a * Real.exp (H a - H b) ≤ f b := by
  have hnegd : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun y => -f y) (-fDot x) x := by
    filter_upwards [hfd] with x hx hmem
    exact (hx hmem).neg
  have hnegle : ∀ᵐ x, x ∈ uIcc a b → -fDot x ≤ -HDot x * (-f x) := by
    filter_upwards [hle] with x hx hmem
    nlinarith [hx hmem]
  have h := ac_comparison_upper (fun y => -f y) (fun y => -fDot y) H HDot a b
    hab hf.neg hH hnegd hHd hnegle
  simpa only [neg_mul, neg_le_neg_iff] using h

end Rhone.Statistics.Identifiability
