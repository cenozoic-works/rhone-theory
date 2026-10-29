/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeAttachmentCdf
/-!
# Density of the attachment time from the cumulative hazard between finite boundaries

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–6. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess Filter Set
open scoped Topology

theorem continuous_attachmentHazard {N : ℕ} (T : Tree N) (t : ℝ) :
    Continuous (attachmentHazard T t) :=
  intervalIntegral.continuous_primitive (attachmentRate_intervalIntegrable T) t

theorem attachmentRate_rightContinuous {N : ℕ} (T : Tree N) (s : ℝ) :
    ContinuousWithinAt (attachmentRate T) (Set.Ici s) s := by
  by_cases hr : rootHeight T ≤ s
  · refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (show attachmentRate T x = attachmentRate T s by
      simp [attachmentRate, hr, hr.trans hx])
  · have hn := next_boundary_strict T s (lt_of_not_ge hr)
    refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
    have hx : ∀ᶠ x in 𝓝[Ici s] s, x < nextBoundary T s :=
      nhdsWithin_le_nhds (Iio_mem_nhds hn)
    filter_upwards [self_mem_nhdsWithin, hx] with x hs hxb
    exact (attachmentRate_eq_before_boundary T s x (lt_of_not_ge hr) hs hxb)

theorem attachmentHazard_rightDerivative {N : ℕ} (T : Tree N) (t s : ℝ) :
    HasDerivWithinAt (attachmentHazard T t) (attachmentRate T s) (Set.Ioi s) s := by
  exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Ici s) (t := Ioi s)
    (attachmentRate_intervalIntegrable T t s)
    ((measurable_attachmentRate T).stronglyMeasurable.stronglyMeasurableAtFilter)
    ((attachmentRate_rightContinuous T s).mono Ioi_subset_Ici_self)).mono Ioi_subset_Ici_self

private theorem rate_bound {N : ℕ} (T : Tree N) (s : ℝ) :
    attachmentRate T s ≤ (T.1 : ℝ) + 1 := by
  unfold attachmentRate
  split_ifs
  · have h : (0 : ℝ) ≤ T.1 := Nat.cast_nonneg _
    linarith
  · have h := Finset.card_le_univ (activeBranches T s)
    simp only [Fintype.card_fin] at h
    have hc : ((activeBranches T s).card : ℝ) ≤ T.1 := by exact_mod_cast h
    linarith

private theorem density_integrableOn {N : ℕ} (T : Tree N) (t x : ℝ) (_hx : t ≤ x) :
    IntegrableOn (fun s => Real.exp (-attachmentHazard T t s) * attachmentRate T s)
      (Icc t x) := by
  have hm : Measurable (fun s => Real.exp (-attachmentHazard T t s) * attachmentRate T s) :=
    ((Real.continuous_exp.comp (continuous_attachmentHazard T t).neg).measurable).mul
      (measurable_attachmentRate T)
  apply Integrable.of_bound hm.aestronglyMeasurable ((T.1 : ℝ) + 1)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (attachmentRate_nonneg T s))]
  have he : Real.exp (-attachmentHazard T t s) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (attachmentHazard_nonneg T t s hs.1))
  exact (mul_le_of_le_one_left (attachmentRate_nonneg T s) he).trans (rate_bound T s)

private theorem density_intervalIntegral {N : ℕ} (T : Tree N) (t x : ℝ) (hx : t ≤ x) :
    ∫ s in t..x, Real.exp (-attachmentHazard T t s) * attachmentRate T s =
      1 - Real.exp (-attachmentHazard T t x) := by
  have hi : IntervalIntegrable
      (fun s => Real.exp (-attachmentHazard T t s) * attachmentRate T s) volume t x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (density_integrableOn T t x hx)
  have hd (s : ℝ) : HasDerivWithinAt (fun z => 1 - Real.exp (-attachmentHazard T t z))
      (Real.exp (-attachmentHazard T t s) * attachmentRate T s) (Ioi s) s := by
    convert (hasDerivWithinAt_const s (Ioi s) (1 : ℝ)).sub
      (attachmentHazard_rightDerivative T t s).neg.exp using 1
    simp only [Pi.neg_apply]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx
    (continuous_const.sub
      (Real.continuous_exp.comp (continuous_attachmentHazard T t).neg)).continuousOn
    (fun s _ => hd s) hi
  simpa [attachmentHazard] using hFTC
/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
theorem attachment_time_law_density {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t : ℝ) (ht : 0 ≤ t) :
    unitUniform.map (fun u => attachmentTime T t (-Real.log u)) =
      (volume.restrict (Set.Ici t)).withDensity
        (fun s => ENNReal.ofReal (Real.exp (-attachmentHazard T t s) * attachmentRate T s)) := by
  have hm : Measurable (fun u => attachmentTime T t (-Real.log u)) :=
    (measurable_attachmentTime_budget T t).comp (by fun_prop)
  have : IsProbabilityMeasure (unitUniform.map (fun u => attachmentTime T t (-Real.log u))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.ext_of_Iic
  intro x
  rw [withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  by_cases hx : t ≤ x
  · have hset : Iic x ∩ Ici t = Icc t x := by ext s; simp [and_comm]
    rw [hset, attachment_time_cdf T hT t x ht hx]
    rw [← ofReal_integral_eq_lintegral_ofReal (density_integrableOn T t x hx)
      (Eventually.of_forall fun s => mul_nonneg (Real.exp_pos _).le
        (attachmentRate_nonneg T s)), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx, density_intervalIntegral T t x hx]
  · have hset : Iic x ∩ Ici t = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_empty_iff_false, iff_false]
      intro hs
      exact hx (hs.2.trans hs.1)
    rw [hset, Measure.restrict_empty, lintegral_zero_measure,
      Measure.map_apply hm measurableSet_Iic]
    calc
      unitUniform ((fun u => attachmentTime T t (-Real.log u)) ⁻¹' Iic x) =
          unitUniform ∅ := by
        apply measure_congr
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        have he : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
        have hb := (attachment_time_budget_bound T hT t (-Real.log u) ht he).1
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false]
        exact propext (iff_false_intro (by intro h; exact hx (hb.trans h)))
      _ = 0 := measure_empty
end Rhone.Coalescent.SmcPrime
