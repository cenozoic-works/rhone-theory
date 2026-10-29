/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeAttachmentDensity
public import Rhone.Coalescent.SmcPrimeAttachmentTargetLaw
/-!
# Joint law of the attachment time and old-branch target from two uniforms

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–6. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess Filter Set
open scoped ENNReal

theorem measurable_attachmentUniformMap {N : ℕ} (T : Tree N) (t : ℝ) :
    Measurable (fun uv : ℝ × ℝ =>
      let a := attachmentTime T t (-Real.log uv.1)
      (a, attachmentTarget T a uv.2)) := by
  have ha : Measurable (fun uv : ℝ × ℝ => attachmentTime T t (-Real.log uv.1)) :=
    (measurable_attachmentTime_budget T t).comp (by fun_prop)
  exact ha.prodMk ((attachmentTargetFiber_measurable N T.1).comp
    (measurable_const.prodMk (ha.prodMk measurable_snd)))

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
noncomputable def attachmentUniformLaw {N : ℕ} (T : Tree N) (t : ℝ) :
    Measure (ℝ × Finset (Fin N)) :=
  (unitUniform.prod unitUniform).map (fun uv =>
    let a := attachmentTime T t (-Real.log uv.1)
    (a, attachmentTarget T a uv.2))
instance attachmentUniformLaw_probability {N : ℕ} (T : Tree N) (t : ℝ) :
    IsProbabilityMeasure (attachmentUniformLaw T t) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_attachmentUniformMap T t).aemeasurable).mpr inferInstance

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
theorem attachment_target_joint_density {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t : ℝ) (ht : 0 ≤ t)
    (A : Set ℝ) (hA : MeasurableSet A) (c : Finset (Fin N)) :
    attachmentUniformLaw T t {p | p.1 ∈ A ∧ p.2 = c} =
      ∫⁻ s in A ∩ Set.Ici t,
        ENNReal.ofReal (Real.exp (-attachmentHazard T t s) * attachmentTargetRate T s c) := by
  let a : ℝ → ℝ := fun u => attachmentTime T t (-Real.log u)
  have ha : Measurable a := (measurable_attachmentTime_budget T t).comp (by fun_prop)
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal
    (attachmentTargetRate T s c / attachmentRate T s)
  have hf : Measurable f := ((measurable_attachmentTargetRate T c).div
    (measurable_attachmentRate T)).ennreal_ofReal
  have hif : Measurable (A.indicator f) := hf.indicator hA
  have hevent : MeasurableSet {p : ℝ × Finset (Fin N) | p.1 ∈ A ∧ p.2 = c} :=
    (hA.preimage measurable_fst).inter ((measurableSet_singleton c).preimage measurable_snd)
  have he : attachmentUniformLaw T t {p | p.1 ∈ A ∧ p.2 = c} =
      ∫⁻ s, A.indicator f s ∂unitUniform.map a := by
    unfold attachmentUniformLaw
    rw [Measure.map_apply (measurable_attachmentUniformMap T t) hevent,
      Measure.prod_apply (hevent.preimage (measurable_attachmentUniformMap T t)),
      lintegral_map hif ha]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have he : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
    have hs : 0 ≤ a u := ht.trans (attachment_time_budget_bound T hT t (-Real.log u) ht he).1
    change unitUniform {v | a u ∈ A ∧ attachmentTarget T (a u) v = c} = A.indicator f (a u)
    by_cases hau : a u ∈ A
    · have hmt : Measurable (fun v => attachmentTarget T (a u) v) :=
        (attachmentTargetFiber_measurable N T.1).comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      have hmass := attachment_target_mass T hT (a u) hs c
      rw [Measure.map_apply hmt (measurableSet_singleton c)] at hmass
      change unitUniform {v | attachmentTarget T (a u) v = c} = _ at hmass
      simpa only [hau, true_and, Set.indicator_of_mem hau, f] using hmass
    · simp only [hau, false_and, Set.ofPred_false, measure_empty, Set.indicator_of_notMem hau]
  rw [he, attachment_time_law_density T hT t ht]
  have hd : Measurable (fun s => ENNReal.ofReal
      (Real.exp (-attachmentHazard T t s) * attachmentRate T s)) :=
    (((Real.continuous_exp.comp (continuous_attachmentHazard T t).neg).measurable).mul
      (measurable_attachmentRate T)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hif]
  calc
    (∫⁻ s, (fun s => ENNReal.ofReal
        (Real.exp (-attachmentHazard T t s) * attachmentRate T s) * A.indicator f s) s
        ∂volume.restrict (Ici t)) =
      ∫⁻ s, A.indicator (fun s => ENNReal.ofReal
        (Real.exp (-attachmentHazard T t s) * attachmentTargetRate T s c)) s
        ∂volume.restrict (Ici t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
      by_cases hsa : s ∈ A
      · simp only [Set.indicator_of_mem hsa, f]
        rw [← ENNReal.ofReal_mul
          (mul_nonneg (Real.exp_pos _).le (attachmentRate_nonneg T s))]
        congr 1
        have hr : 0 < attachmentRate T s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
          (attachment_rate_ge_one T hT s (ht.trans hs))
        field_simp [hr.ne']
      · simp only [Set.indicator_of_notMem hsa, mul_zero]
    _ = ∫⁻ s in A ∩ Set.Ici t, ENNReal.ofReal
        (Real.exp (-attachmentHazard T t s) * attachmentTargetRate T s c) := by
      rw [lintegral_indicator hA, Measure.restrict_restrict hA]
end Rhone.Coalescent.SmcPrime
