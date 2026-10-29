/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ClockLawMarginal
public import Rhone.Statistics.Identifiability.ExitCDF
public import Rhone.Statistics.Identifiability.HalfLineIdentification

/-! # The conditional pair law identifies the coalescence clock -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem conditionalPairLaw_real_Ioc (rate H : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    {T : ℝ} (hT : 0 ≤ T) :
    (conditionalPairLaw rate H 0).real (Ioc 0 T) = 1-Real.exp (H 0-H T) := by
  have hi : IntervalIntegrable (conditionalPairDensity rate H 0) volume 0 T :=
    (hr.mul (Real.continuous_exp.comp (continuous_const.sub hH))).intervalIntegrable 0 T
  unfold conditionalPairLaw
  rw [positive_density_real_Ioc _ hT hi]
  · have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => conditionalPair_CDF_derivative rate H 0 t
        (hclock t (by rw [uIcc_of_le hT] at ht; exact ht.1))) hi
    simpa using he
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (hrn t ht.1.le) (Real.exp_pos _).le

theorem conditionalPairLaw_identifies_clock (rate₁ rate₂ H₁ H₂ : ℝ → ℝ)
    (hr₁ : Continuous rate₁) (hr₂ : Continuous rate₂)
    (hH₁ : Continuous H₁) (hH₂ : Continuous H₂)
    (hn₁ : ∀ t, 0 ≤ t → 0 ≤ rate₁ t) (hn₂ : ∀ t, 0 ≤ t → 0 ≤ rate₂ t)
    (hc₁ : ∀ t, 0 ≤ t → HasDerivAt H₁ (rate₁ t) t)
    (hc₂ : ∀ t, 0 ≤ t → HasDerivAt H₂ (rate₂ t) t)
    (he : conditionalPairLaw rate₁ H₁ 0 = conditionalPairLaw rate₂ H₂ 0) :
    EqOn (fun t => H₁ 0-H₁ t) (fun t => H₂ 0-H₂ t) (Ici 0) ∧
      EqOn rate₁ rate₂ (Ici 0) := by
  have hclock : EqOn (fun t => H₁ 0-H₁ t) (fun t => H₂ 0-H₂ t) (Ici 0) := by
    intro t ht
    have h₁ := conditionalPairLaw_real_Ioc rate₁ H₁ hr₁ hH₁ hn₁ hc₁ ht
    have h₂ := conditionalPairLaw_real_Ioc rate₂ H₂ hr₂ hH₂ hn₂ hc₂ ht
    rw [he] at h₁
    apply Real.exp_injective
    linarith
  refine ⟨hclock,?_⟩
  have hd : EqOn (fun t => -rate₁ t) (fun t => -rate₂ t) (Ici 0) :=
    eqOn_halfline_derivatives hr₁.neg hr₂.neg
      (fun t ht => (hc₁ t ht).const_sub (H₁ 0))
      (fun t ht => (hc₂ t ht).const_sub (H₂ 0)) (by
        intro t ht
        apply hclock
        change 0 ≤ t
        change 0 < t at ht
        exact ht.le)
  intro t ht
  have hh := hd ht
  linarith

end Rhone.Statistics.Identifiability
