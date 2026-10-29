/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MarginalClockODE

/-! # The lower-triangle contribution to a marginal is the pending-pair mass -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem clock_density_separated (rate H N : ℝ → ℝ) (s t : ℝ) :
    rate s*N s*rate t*Real.exp (H s-H t) =
      (rate t*Real.exp (-H t))*(rate s*N s*Real.exp (H s)) := by
  rw [sub_eq_add_neg,Real.exp_add]
  ring

theorem clock_column_lintegral (rate H N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t) (hNn : ∀ t, 0 ≤ t → 0 ≤ N t)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ s in Ioo (0 : ℝ) t,
      ENNReal.ofReal (rate s*N s*rate t*Real.exp (H s-H t))) =
      ENNReal.ofReal (rate t*pendingPairMass rate H N t) := by
  let g : ℝ → ℝ := fun s => rate s*N s*Real.exp (H s)
  have hg : Continuous g := (hr.mul hN).mul (Real.continuous_exp.comp hH)
  have hi : IntegrableOn g (Ioo 0 t) := hg.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hc : 0 ≤ rate t*Real.exp (-H t) := mul_nonneg (hrn t ht.le) (Real.exp_pos _).le
  have hn : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) t), 0 ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (mul_nonneg (hrn s hs.1.le) (hNn s hs.1.le)) (Real.exp_pos _).le
  simp_rw [clock_density_separated,ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change ENNReal.ofReal (rate t*Real.exp (-H t)) * (∫⁻ s in Ioo 0 t, ENNReal.ofReal (g s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,← ENNReal.ofReal_mul hc]
  have he : (∫ s in Ioo (0 : ℝ) t, g s) = primitiveFrom g 0 t := by
    rw [primitiveFrom,intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo]
  rw [he]
  congr 1
  unfold pendingPairMass
  dsimp [g]
  ring

end Rhone.Statistics.Identifiability
