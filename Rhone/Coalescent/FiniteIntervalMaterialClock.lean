/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialMarked
public import Mathlib.Tactic.Linarith

/-! # The inverse-uniform holding clock has an exponential distribution function -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped ENNReal

theorem inverseClock_cdf (r : ℝ) (hr : 0 < r) (t : ℝ) :
    (unitUniform.map (fun u => -Real.log u / r)) (Set.Iic t) =
      ENNReal.ofReal (1 - Real.exp (-(r*t))) := by
  have hm : Measurable (fun u : ℝ => -Real.log u / r) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Iic, unitUniform,
    Measure.restrict_apply (hm measurableSet_Iic)]
  have hequiv (u : ℝ) (hu : 0 < u) :
      -Real.log u / r ≤ t ↔ Real.exp (-(r*t)) ≤ u := by
    rw [div_le_iff₀ hr, ← Real.le_log_iff_exp_le hu]
    constructor <;> intro h <;> nlinarith
  have heq : (fun u : ℝ => -Real.log u / r) ⁻¹' Set.Iic t ∩ Set.Ioo 0 1 =
      Set.Ico (Real.exp (-(r*t))) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic,
      Set.mem_Ioo, Set.mem_Ico]
    constructor
    · rintro ⟨hclock, hu0, hu1⟩
      exact ⟨(hequiv u hu0).1 hclock, hu1⟩
    · rintro ⟨hlo, hhi⟩
      have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hlo
      exact ⟨(hequiv u hu0).2 hlo, hu0, hhi⟩
  rw [heq, Real.volume_Ico]

end Rhone.Coalescent.IntervalProcess
