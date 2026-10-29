/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableExposureOnset

/-! # A locally integrable rate that is not almost everywhere zero has positive exposure -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability.IntegrableExposure

lemma exists_positive_exposure_of_not_ae_zero (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ f t) (hne : ¬ ∀ᵐ t, 0 ≤ t → f t = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ 0 < integratedClock f A := by
  by_contra hex
  have hz (A : ℝ) (hA : 0 ≤ A) : integratedClock f A = 0 :=
    le_antisymm (le_of_not_gt (fun hpos => hex ⟨A, hA, hpos⟩))
      (interval_nonnegative f le_rfl hA hn)
  have hzN (N : ℕ) : ∀ᵐ t, t ∈ Icc (0 : ℝ) (N : ℝ) → f t = 0 :=
    ae_zero_of_exposure_zero f hf (by positivity) hn (hz N (by positivity))
  have hall : ∀ᵐ t, ∀ N : ℕ, t ∈ Icc (0 : ℝ) (N : ℝ) → f t = 0 := ae_all_iff.mpr hzN
  apply hne
  filter_upwards [hall] with t ht hnonneg
  obtain ⟨N, hN⟩ := exists_nat_ge t
  exact ht N ⟨hnonneg, hN⟩

lemma not_ae_zero_of_positive_exposure (f : ℝ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hpos : 0 < integratedClock f A) : ¬ ∀ᵐ t, 0 ≤ t → f t = 0 := by
  intro he
  have hz : integratedClock f A = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [he] with t ht hmem
    rw [uIoc_of_le hA] at hmem
    exact ht hmem.1.le
  exact hpos.ne' hz

end Rhone.Statistics.Identifiability.IntegrableExposure
