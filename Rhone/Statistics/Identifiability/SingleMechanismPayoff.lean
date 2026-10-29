/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeOrderedSingleRemainder
public import Rhone.Statistics.Identifiability.TimeOrderedMixedRemainder

/-! # Scalar payoff control retaining the activating mechanism's full exposure -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι]

noncomputable def rowPayoff (ρ : ι → ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ρ i * (M *ᵥ v) i

lemma rowPayoff_sub (ρ : ι → ℝ) (M N : Matrix ι ι ℝ) (v : ι → ℝ) :
    rowPayoff ρ (M - N) v = rowPayoff ρ M v - rowPayoff ρ N v := by
  simp only [rowPayoff, Matrix.sub_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rowPayoff_smul (ρ : ι → ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) (a : ℝ) :
    rowPayoff ρ (a • M) v = a * rowPayoff ρ M v := by
  simp only [rowPayoff, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma rowPayoff_abs_le (ρ : ι → ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    |rowPayoff ρ M v| ≤ (∑ i, |ρ i|) * ‖M‖ * ‖v‖ := by
  calc
    _ ≤ ∑ i, |ρ i * (M *ᵥ v) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |ρ i| * (‖M‖ * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (norm_le_pi_norm (M *ᵥ v) i).trans (Matrix.linfty_opNorm_mulVec M v)
    _ = _ := by rw [← Finset.sum_mul]; ring

variable [DecidableEq ι]

theorem rowPayoff_single_remainder_le
    (C : ℝ → Matrix ι ι ℝ) (r : ℝ → ℝ) (R : Matrix ι ι ℝ) (ρ v : ι → ℝ)
    (hC : ∀ i j, Continuous (fun t => C t i j)) (hr : Continuous r)
    {s t K : ℝ} (hst : s ≤ t)
    (hrn : ∀ u ∈ Icc s t, 0 ≤ r u)
    (hbC : HasContractiveBoundOn C s t K)
    (hbD : HasContractiveBoundOn (C + fun u => r u • R) s t K)
    (hzero : rowPayoff ρ (inhomogeneousTransition C s t) v = 0) :
    |rowPayoff ρ (inhomogeneousTransition (C + fun u => r u • R) s t) v -
        (∫ u in s..t, r u) * rowPayoff ρ R v| ≤
      ((∑ i, |ρ i|) * K * ‖R‖ * ‖v‖) * (t - s) * (∫ u in s..t, r u) := by
  have hRc : ∀ i j, Continuous (fun u => (r u • R) i j) :=
    fun i j => hr.mul continuous_const
  have h := inhomogeneousTransition_single_remainder_le C (fun u => r u • R)
    hC hRc hst hbC hbD
  rw [intervalIntegral.integral_smul_const] at h
  have hn := integral_norm_scalar_mark r R (a := 1) (by norm_num) hst hrn
  simp only [one_mul] at hn
  rw [hn] at h
  let E := inhomogeneousTransition (C + fun u => r u • R) s t -
    inhomogeneousTransition C s t - (∫ u in s..t, r u) • R
  have he : rowPayoff ρ E v =
      rowPayoff ρ (inhomogeneousTransition (C + fun u => r u • R) s t) v -
        (∫ u in s..t, r u) * rowPayoff ρ R v := by
    simp only [E, rowPayoff_sub, rowPayoff_smul, hzero, sub_zero]
  rw [← he]
  calc
    _ ≤ (∑ i, |ρ i|) * ‖E‖ * ‖v‖ := rowPayoff_abs_le ρ E v
    _ ≤ (∑ i, |ρ i|) * (K * (t - s) * (‖R‖ * (∫ u in s..t, r u))) * ‖v‖ := by
      gcongr
    _ = _ := by ring

end Rhone.Statistics.Identifiability
