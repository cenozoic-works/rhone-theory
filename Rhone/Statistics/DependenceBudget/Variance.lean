/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic.Linarith

/-! # A variance tail bound for the dependence budget -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Rhone.Statistics.DependenceBudget

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {S : Ω → ℝ} {m A v : ℝ}

theorem upper_tail (hS : MemLp S 2 μ) (hm : (∫ x, S x ∂μ) ≤ m)
    (hv : ProbabilityTheory.variance S μ ≤ v) (hA : m < A) :
    μ.real {x | A ≤ S x} ≤ v / (A - m) ^ 2 := by
  have hc : 0 < A - m := sub_pos.mpr hA
  have hsub : {x | A ≤ S x} ⊆ {x | A - m ≤ |S x - ∫ y, S y ∂μ|} := by
    intro x hx
    have hs : A - m ≤ S x - ∫ y, S y ∂μ := by dsimp at hx; linarith
    exact hs.trans (le_abs_self _)
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hS hc
  have hv0 : 0 ≤ v := (ProbabilityTheory.variance_nonneg S μ).trans hv
  have hb : μ {x | A ≤ S x} ≤ ENNReal.ofReal (v / (A - m) ^ 2) :=
    (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hv (sq_nonneg _))))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (div_nonneg hv0 (sq_nonneg _)))

theorem lower_tail (hS : MemLp S 2 μ) (hm : m ≤ ∫ x, S x ∂μ)
    (hv : ProbabilityTheory.variance S μ ≤ v) (hA : A < m) :
    μ.real {x | S x ≤ A} ≤ v / (m - A) ^ 2 := by
  have hc : 0 < m - A := sub_pos.mpr hA
  have hsub : {x | S x ≤ A} ⊆ {x | m - A ≤ |S x - ∫ y, S y ∂μ|} := by
    intro x hx
    have hs : m - A ≤ -(S x - ∫ y, S y ∂μ) := by dsimp at hx; linarith
    exact hs.trans (neg_le_abs _)
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hS hc
  have hv0 : 0 ≤ v := (ProbabilityTheory.variance_nonneg S μ).trans hv
  have hb : μ {x | S x ≤ A} ≤ ENNReal.ofReal (v / (m - A) ^ 2) :=
    (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hv (sq_nonneg _))))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (div_nonneg hv0 (sq_nonneg _)))

theorem null_size (hS : MemLp S 2 μ) (hm : (∫ x, S x ∂μ) ≤ 0)
    {α : ℝ} (hv : ProbabilityTheory.variance S μ ≤ v)
    (hbudget : v ≤ α * A ^ 2) (hA : 0 < A) :
    μ.real {x | A ≤ S x} ≤ α := by
  have h := upper_tail hS hm hv hA
  simp only [sub_zero] at h
  exact h.trans ((div_le_iff₀ (sq_pos_of_pos hA)).mpr hbudget)

theorem source_power_strict (hS : MemLp S 2 μ)
    (hm : m ≤ ∫ x, S x ∂μ) {β : ℝ}
    (hv : ProbabilityTheory.variance S μ ≤ v)
    (hbudget : v ≤ β * (m - A) ^ 2) (hA : A < m) :
    1 - β ≤ μ.real {x | A < S x} := by
  have htail := lower_tail hS hm hv hA
  have hbound : μ.real {x | S x ≤ A} ≤ β :=
    htail.trans ((div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hA))).mpr hbudget)
  have hsum := measureReal_add_measureReal_compl₀ (μ := μ) (s := {x | S x ≤ A})
    (hS.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)
  rw [probReal_univ] at hsum
  have heq : {x | S x ≤ A}ᶜ = {x | A < S x} := by ext x; simp
  rw [heq] at hsum
  linarith

theorem source_power (hS : MemLp S 2 μ) (hm : m ≤ ∫ x, S x ∂μ) {β : ℝ}
    (hv : ProbabilityTheory.variance S μ ≤ v)
    (hbudget : v ≤ β * (m - A) ^ 2) (hA : A < m) :
    1 - β ≤ μ.real {x | A ≤ S x} := by
  apply (source_power_strict hS hm hv hbudget hA).trans
  apply measureReal_mono
  · intro x hx
    exact (show A < S x from hx).le
  · exact measure_ne_top μ _

end Rhone.Statistics.DependenceBudget
