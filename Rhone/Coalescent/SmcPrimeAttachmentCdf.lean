/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeAttachmentInverse
/-!
# Distribution function of the attachment waiting time in the finite-source recursion

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–6. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess Filter

theorem measurable_attachmentTime_budget {N : ℕ} (T : Tree N) (t : ℝ) :
    Measurable (fun e => attachmentTime T t e) :=
  (attachmentAuxFiber_measurable N T.1 (2 * T.1 + 1)).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- Source: marjoram_wall2006, “The SMC′ algorithm”, step 4. -/
theorem attachment_time_cdf {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t x : ℝ) (ht : 0 ≤ t) (hx : t ≤ x) :
    (unitUniform.map (fun u => attachmentTime T t (-Real.log u))) (Set.Iic x) =
      ENNReal.ofReal (1 - Real.exp (-attachmentHazard T t x)) := by
  have hm : Measurable (fun u => attachmentTime T t (-Real.log u)) :=
    (measurable_attachmentTime_budget T t).comp (by fun_prop)
  have hc := inverseClock_cdf 1 (by norm_num) (attachmentHazard T t x)
  simp only [div_one, one_mul] at hc
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic] at hc
  rw [Measure.map_apply hm measurableSet_Iic]
  calc
    unitUniform ((fun u => attachmentTime T t (-Real.log u)) ⁻¹' Set.Iic x) =
        unitUniform ((fun u => -Real.log u) ⁻¹' Set.Iic (attachmentHazard T t x)) := by
      apply measure_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have he : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.1.le hu.2.le)
      exact propext (attachment_time_budget_iff T hT t (-Real.log u) x ht he hx)
    _ = ENNReal.ofReal (1 - Real.exp (-attachmentHazard T t x)) := hc
end Rhone.Coalescent.SmcPrime
