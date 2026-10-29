/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-! # Duhamel identity and contractive exponential perturbations -/

@[expose] public section

open MeasureTheory Set

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.ContractiveDuhamel

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

theorem interpolation_hasDerivAt (A B : 𝔄) (t s : ℝ) :
    HasDerivAt
      (fun u : ℝ => -(NormedSpace.exp ((t-u) • (A + B)) * NormedSpace.exp (u • A)))
      (NormedSpace.exp ((t-s) • (A + B)) * B * NormedSpace.exp (s • A)) s := by
  have hleft : HasDerivAt (fun u : ℝ => NormedSpace.exp ((t-u) • (A + B)))
      (-(NormedSpace.exp ((t-s) • (A + B)) * (A + B))) s := by
    simpa only [neg_smul, one_smul, Function.comp_def] using (hasDerivAt_exp_smul_const (A + B)
      (t-s)).scomp s
      ((hasDerivAt_id s).const_sub t)
  have hright := hasDerivAt_exp_smul_const' A s
  convert! (hleft.mul hright).neg using 1
  noncomm_ring

theorem exp_add_sub_exp (A B : 𝔄) (t : ℝ) :
    NormedSpace.exp (t • (A + B)) - NormedSpace.exp (t • A) =
      ∫ s in (0 : ℝ)..t,
        NormedSpace.exp ((t-s) • (A + B)) * B * NormedSpace.exp (s • A) := by
  have hcont : Continuous (fun s : ℝ =>
      NormedSpace.exp ((t-s) • (A + B)) * B * NormedSpace.exp (s • A)) := by
    exact ((((differentiable_exp_smul_const ℝ (A + B)).continuous.comp
      (continuous_const.sub continuous_id)).mul continuous_const).mul
        (differentiable_exp_smul_const ℝ A).continuous)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => interpolation_hasDerivAt A B t s) (hcont.intervalIntegrable 0 t)
  simpa [sub_eq_add_neg, add_comm] using h.symm

theorem exp_add_sub_exp_one (A B : 𝔄) :
    NormedSpace.exp (A + B) - NormedSpace.exp A =
      ∫ s in (0 : ℝ)..1,
        NormedSpace.exp ((1-s) • (A + B)) * B * NormedSpace.exp (s • A) := by
  simpa only [one_smul] using exp_add_sub_exp A B 1

theorem norm_exp_add_sub_exp_le (A B : 𝔄) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc (0 : ℝ) t, ‖NormedSpace.exp (s • A)‖ ≤ 1)
    (hAB : ∀ s ∈ Icc (0 : ℝ) t, ‖NormedSpace.exp (s • (A + B))‖ ≤ 1) :
    ‖NormedSpace.exp (t • (A + B)) - NormedSpace.exp (t • A)‖ ≤ t * ‖B‖ := by
  rw [exp_add_sub_exp]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := ‖B‖)
    (f := fun s : ℝ => NormedSpace.exp ((t-s) • (A + B)) * B * NormedSpace.exp (s • A))
    (fun s hs => ?_)
  · simpa [abs_of_nonneg ht, mul_comm] using h
  rw [uIoc_of_le ht] at hs
  have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
  have hts : t-s ∈ Icc (0 : ℝ) t := ⟨sub_nonneg.mpr hs.2, sub_le_self t hs.1.le⟩
  calc
    ‖NormedSpace.exp ((t-s) • (A + B)) * B * NormedSpace.exp (s • A)‖
        ≤ ‖NormedSpace.exp ((t-s) • (A + B))‖ * ‖B‖ * ‖NormedSpace.exp (s • A)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖B‖ * 1 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hAB _ hts) (norm_nonneg _))
        (hA _ hs') (norm_nonneg _) (by positivity)
    _ = ‖B‖ := by ring

theorem norm_exp_add_sub_exp_le_one (A B : 𝔄)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, ‖NormedSpace.exp (s • A)‖ ≤ 1)
    (hAB : ∀ s ∈ Icc (0 : ℝ) 1, ‖NormedSpace.exp (s • (A + B))‖ ≤ 1) :
    ‖NormedSpace.exp (A + B) - NormedSpace.exp A‖ ≤ ‖B‖ := by
  simpa using norm_exp_add_sub_exp_le A B (t := 1) zero_le_one hA hAB

end Rhone.Statistics.Identifiability.ContractiveDuhamel
