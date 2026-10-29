/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationFourEpochRates
public import Rhone.Statistics.Identifiability.IntegrablePanExistence

/-! # Proper locally integrable models for the four-epoch rate -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

theorem fourEpochRate_measurable (ε δ M A τ : ℝ) :
    Measurable (fourEpochRate ε δ M A τ) := by
  unfold fourEpochRate
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const
      (Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const measurable_const))

theorem fourEpochRate_locallyIntegrable (ε δ M A τ : ℝ) :
    LocallyIntegrable (fourEpochRate ε δ M A τ) volume := by
  apply (locallyIntegrable_const
    (‖δ + A / ε‖ + ‖δ‖ + ‖δ + M / ε‖ : ℝ)).mono
    (fourEpochRate_measurable ε δ M A τ).aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_of_nonneg (add_nonneg
    (add_nonneg (norm_nonneg (δ + A / ε)) (norm_nonneg δ))
    (norm_nonneg (δ + M / ε)))]
  unfold fourEpochRate
  split_ifs <;> linarith [norm_nonneg (δ + A / ε), norm_nonneg δ,
    norm_nonneg (δ + M / ε)]

theorem fourEpochRate_locallyIntegrableOn (ε δ M A τ : ℝ) :
    LocallyIntegrableOn (fourEpochRate ε δ M A τ) (Ici 0) volume :=
  (fourEpochRate_locallyIntegrable ε δ M A τ).locallyIntegrableOn (Ici 0)

theorem fourEpochRate_nonneg {ε δ M A τ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hA : 0 ≤ A) (t : ℝ) :
    0 ≤ fourEpochRate ε δ M A τ t :=
  (fourEpochRate_pos hε hδ hM hA t).le

theorem fourEpochRate_clock_lower {ε δ M A τ t : ℝ} (hε : 0 < ε)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (ht : 0 ≤ t) :
    δ * t ≤ integrablePanClock (fourEpochRate ε δ M A τ) t := by
  rw [integrablePanClock_eq_integral _ ht]
  have hi : IntervalIntegrable (fourEpochRate ε δ M A τ) volume 0 t :=
    LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable
      (fourEpochRate_locallyIntegrable ε δ M A τ) 0 t
  have h := intervalIntegral.integral_mono ht (intervalIntegrable_const (c := δ)) hi
    (fourEpochRate_lower (δ := δ) (τ := τ) hε hM hA)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm t δ] using h

theorem fourEpochRate_clock_diverges {ε δ M A τ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hA : 0 ≤ A) :
    Tendsto (integrablePanClock (fourEpochRate ε δ M A τ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_id.const_mul_atTop hδ)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact fourEpochRate_clock_lower hε hM hA ht

theorem exists_fourEpochProperIntegrablePanModel {ε δ M A τ r : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hr : 0 ≤ r) :
    ∃ P : ProperIntegrablePanModel,
      P.rate = fourEpochRate ε δ M A τ ∧ P.pre.recomb = fun _ => r := by
  exact exists_properIntegrablePanModel (fourEpochRate ε δ M A τ) (fun _ => r)
    (fourEpochRate_locallyIntegrableOn ε δ M A τ) (locallyIntegrableOn_const r)
    (ae_of_all _ (fun t _ => fourEpochRate_nonneg hε hδ hM hA t))
    (ae_of_all _ (fun _ _ => hr)) (fourEpochRate_clock_diverges hε hδ hM hA)

end Rhone.Statistics.Identifiability.MutationPulseKernel
