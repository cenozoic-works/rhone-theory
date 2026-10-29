/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
/-
Banach-valued generalization of the primitive absolute-continuity theorem.
Adapted from Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean,
Copyright (c) 2025 Yizheng Zhu, Apache 2.0.
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Absolute continuity of interval integrals of Banach-valued functions -/

@[expose] public section

open Set Filter Function MeasureTheory
open AbsolutelyContinuousOnInterval
open scoped Topology NNReal
namespace Rhone.Statistics.Identifiability.VectorPrimitiveAC

theorem intervalIntegral_absolutelyContinuousOnInterval_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E}
    {a b c : ℝ} (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
    (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
    (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp this
  refine squeeze_zero' ?_ ?_ this
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [comp_apply, s]
  have : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [this] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [dist_eq_norm,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
        Measure.restrict_restrict_of_subset
          (uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, norm_neg,
        intervalIntegral.norm_intervalIntegral_eq]
    exact norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have h_subset := uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset h_subset]
    exact IntegrableOn.mono_set h.def'.norm h_subset |>.integrable

end Rhone.Statistics.Identifiability.VectorPrimitiveAC
