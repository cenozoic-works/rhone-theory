/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ExponentialDuhamelDerivative

/-! # Stability of exponential insertion integrals -/

@[expose] public section

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.ContractiveDuhamel

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

theorem expInsertion_smul_self (C : 𝔄) (a : ℝ) :
    expInsertion (a • C) C = C * NormedSpace.exp (a • C) := by
  have h := hasDerivAt_exp_affine C (0 : 𝔄) a
  simp only [add_zero] at h
  exact h.unique (hasDerivAt_exp_smul_const' C a)

theorem norm_expInsertion_add_sub_le (A B H : 𝔄)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, ‖NormedSpace.exp (s • A)‖ ≤ 1)
    (hAB : ∀ s ∈ Icc (0 : ℝ) 1, ‖NormedSpace.exp (s • (A + B))‖ ≤ 1) :
    ‖expInsertion (A + B) H - expInsertion A H‖ ≤ ‖B‖ * ‖H‖ := by
  have hc (X : 𝔄) : Continuous (fun s : ℝ =>
      NormedSpace.exp ((1-s) • X) * H * NormedSpace.exp (s • X)) :=
    (((differentiable_exp_smul_const ℝ X).continuous.comp
      (continuous_const.sub continuous_id)).mul continuous_const).mul
        (differentiable_exp_smul_const ℝ X).continuous
  unfold expInsertion
  rw [← intervalIntegral.integral_sub ((hc (A + B)).intervalIntegrable 0 1)
    ((hc A).intervalIntegrable 0 1)]
  have hb (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖NormedSpace.exp (s • (A + B)) - NormedSpace.exp (s • A)‖ ≤ s * ‖B‖ :=
    norm_exp_add_sub_exp_le A B hs.1
      (fun u hu => hA u ⟨hu.1, hu.2.trans hs.2⟩)
      (fun u hu => hAB u ⟨hu.1, hu.2.trans hs.2⟩)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖B‖ * ‖H‖)
    (f := fun s : ℝ =>
      NormedSpace.exp ((1-s) • (A + B)) * H * NormedSpace.exp (s • (A + B)) -
        NormedSpace.exp ((1-s) • A) * H * NormedSpace.exp (s • A)) (fun s hs => ?_)
  · simpa using hi
  rw [uIoc_of_le zero_le_one] at hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  have hts : 1-s ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr hs.2, sub_le_self 1 hs.1.le⟩
  let P := NormedSpace.exp ((1-s) • (A + B))
  let P₀ := NormedSpace.exp ((1-s) • A)
  let Q := NormedSpace.exp (s • (A + B))
  let Q₀ := NormedSpace.exp (s • A)
  have hleft : ‖(P-P₀)*H*Q‖ ≤ ((1-s)*‖B‖)*‖H‖ := by
    calc
      _ ≤ ‖P-P₀‖ * ‖H‖ * ‖Q‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (((1-s)*‖B‖)*‖H‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hb (1-s) hts) (norm_nonneg _))
          (hAB s hs') (norm_nonneg _)
          (mul_nonneg (mul_nonneg hts.1 (norm_nonneg _)) (norm_nonneg _))
      _ = _ := mul_one _
  have hright : ‖P₀*H*(Q-Q₀)‖ ≤ (s*‖B‖)*‖H‖ := by
    calc
      _ ≤ ‖P₀‖ * ‖H‖ * ‖Q-Q₀‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖H‖) * (s*‖B‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hA (1-s) hts) (norm_nonneg _))
          (hb s hs') (norm_nonneg _) (by positivity)
      _ = _ := by ring
  change ‖P*H*Q - P₀*H*Q₀‖ ≤ _
  calc
    _ = ‖(P-P₀)*H*Q + P₀*H*(Q-Q₀)‖ := by congr 1; noncomm_ring
    _ ≤ ‖(P-P₀)*H*Q‖ + ‖P₀*H*(Q-Q₀)‖ := norm_add_le _ _
    _ ≤ ((1-s)*‖B‖)*‖H‖ + (s*‖B‖)*‖H‖ := add_le_add hleft hright
    _ = ‖B‖ * ‖H‖ := by ring

end Rhone.Statistics.Identifiability.ContractiveDuhamel
