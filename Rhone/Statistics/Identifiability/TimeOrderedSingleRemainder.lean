/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeOrderedRemainder

/-! # A one-mechanism exposure factor is retained even at arbitrarily flat onset -/

@[expose] public section

open MeasureTheory Set
open scoped Topology Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

theorem norm_ordered_single_insertion_sub_le
    {𝔄 : Type*} [NormedRing 𝔄] (X Z P : 𝔄) (hZ : ‖Z‖ ≤ 1) :
    ‖X * P * Z - P‖ ≤ (‖X - 1‖ + ‖Z - 1‖) * ‖P‖ := by
  have he : X * P * Z - P = (X - 1) * P * Z + P * (Z - 1) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(X - 1) * P * Z‖ + ‖P * (Z - 1)‖ := norm_add_le _ _
    _ ≤ ‖X - 1‖ * ‖P‖ * ‖Z‖ + ‖P‖ * ‖Z - 1‖ := by
      gcongr
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      · exact norm_mul_le _ _
    _ ≤ ‖X - 1‖ * ‖P‖ * 1 + ‖P‖ * ‖Z - 1‖ := by gcongr
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inhomogeneousTransition_single_remainder_le
    (C R : ℝ → Matrix ι ι ℝ)
    (hC : ∀ i j, Continuous (fun t => C t i j))
    (hR : ∀ i j, Continuous (fun t => R t i j))
    {s t K : ℝ} (hst : s ≤ t)
    (hbC : HasContractiveBoundOn C s t K)
    (hbD : HasContractiveBoundOn (C + R) s t K) :
    ‖inhomogeneousTransition (C + R) s t - inhomogeneousTransition C s t -
        (∫ u in s..t, R u)‖ ≤ K * (t - s) * (∫ u in s..t, ‖R u‖) := by
  have hD : ∀ i j, Continuous (fun u => (C + R) u i j) :=
    fun i j => (hC i j).add (hR i j)
  have hRc : Continuous R := continuous_pi fun i => continuous_pi (hR i)
  let F : ℝ → Matrix ι ι ℝ := fun u =>
    inhomogeneousTransition (C + R) s u * R u * inhomogeneousTransition C u t
  have hFc : Continuous F :=
    (((inhomogeneousTransition_continuous _ hD).comp
      (continuous_const.prodMk continuous_id)).mul hRc).mul
      ((inhomogeneousTransition_continuous _ hC).comp (continuous_id.prodMk continuous_const))
  rw [inhomogeneousTransition_sub_eq_integral (C + R) C hD hC]
  simp only [Pi.add_apply, add_sub_cancel_left]
  change ‖(∫ u in s..t, F u) - (∫ u in s..t, R u)‖ ≤ _
  rw [← intervalIntegral.integral_sub (hFc.intervalIntegrable s t)
    (hRc.intervalIntegrable s t)]
  calc
    _ ≤ ∫ u in s..t, K * (t - s) * ‖R u‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hst
      · apply Filter.Eventually.of_forall
        intro u hu
        have hsu : s ≤ u := hu.1.le
        have hut : u ≤ t := hu.2
        calc
          ‖F u - R u‖ ≤
              (‖inhomogeneousTransition (C + R) s u - 1‖ +
                ‖inhomogeneousTransition C u t - 1‖) * ‖R u‖ :=
            norm_ordered_single_insertion_sub_le _ _ _ (hbC.2 u t hsu hut le_rfl)
          _ ≤ (K * (u - s) + K * (t - u)) * ‖R u‖ := by
            gcongr
            · exact hbD.norm_sub_one_le hD le_rfl hsu hut
            · exact hbC.norm_sub_one_le hC hsu hut le_rfl
          _ = _ := by ring
      · exact (continuous_const.mul hRc.norm).intervalIntegrable s t
    _ = _ := intervalIntegral.integral_const_mul _ _

end Rhone.Statistics.Identifiability
