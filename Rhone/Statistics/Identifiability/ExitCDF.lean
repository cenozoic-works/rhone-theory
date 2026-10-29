/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExitLaw

/-! # The constructed first-exit measure has the semigroup survival function -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem positive_density_real_Ioc (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T)
    (hpos : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 T), 0 ≤ f t) :
    ((volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (f t))).real (Ioc 0 T) =
      ∫ t in 0..T, f t := by
  rw [measureReal_def, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hsub : Ioc (0 : ℝ) T ⊆ Ioi 0 := fun _ hx => hx.1
  rw [inter_eq_left.mpr hsub,
    ← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hf) hpos,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hpos), intervalIntegral.integral_of_le hT]

theorem firstExitLaw_real_Ioc {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) (i : Fin d) {T : ℝ} (hT : 0 ≤ T) :
    (firstExitLaw Q i).real (Ioc 0 T) = 1 - flowOutput Q i (fun _ => 1) 0 T := by
  unfold firstExitLaw
  rw [positive_density_real_Ioc _ hT
    ((flowOutput_continuous Q i (exitRate Q) 0).intervalIntegrable 0 T),
    firstExit_mass_balance]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact firstExit_density_nonneg Q hQ hrow i ht.1.le

end Rhone.Statistics.Identifiability
