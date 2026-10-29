/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Continuous - time cost of a haploid substitution

Source: haldane1957_cost_selection, pp. 514–515, eq. 1–4. -/

@[expose] public section
namespace Rhone.Dynamics
open Filter MeasureTheory

noncomputable def substitutionFrequency (s p0 t : ℝ) : ℝ :=
  1 / (1 + ((1 - p0) / p0) * Real.exp (-s * t))

/-- Source: haldane1957_cost_selection, pp. 514–515. -/
theorem substitution_frequency_initial {s p0 : ℝ}
    (hp0 : 0 < p0) (_hp1 : p0 < 1) :
    substitutionFrequency s p0 0 = p0 := by
  unfold substitutionFrequency
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-- Source: haldane1957_cost_selection, pp. 514–515. -/
theorem substitution_frequency_mem {s p0 t : ℝ}
    (hp0 : 0 < p0) (hp1 : p0 < 1) :
    substitutionFrequency s p0 t ∈ Set.Ioo 0 1 := by
  have hc : 0 < ((1 - p0) / p0) * Real.exp (-s * t) :=
    mul_pos (div_pos (sub_pos.mpr hp1) hp0) (Real.exp_pos _)
  unfold substitutionFrequency
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).mpr
    linarith

/-- Source: haldane1957_cost_selection, pp. 514–515. -/
theorem substitution_frequency_deriv {s p0 : ℝ}
    (hp0 : 0 < p0) (hp1 : p0 < 1) (t : ℝ) :
    HasDerivAt (substitutionFrequency s p0)
      (s * substitutionFrequency s p0 t * (1 - substitutionFrequency s p0 t)) t := by
  have hc : 0 < ((1 - p0) / p0) * Real.exp (-s * t) :=
    mul_pos (div_pos (sub_pos.mpr hp1) hp0) (Real.exp_pos _)
  have hn : 1 + ((1 - p0) / p0) * Real.exp (-s * t) ≠ 0 := by positivity
  unfold substitutionFrequency
  generalize hC : (1 - p0) / p0 = C at hn ⊢
  have hd := (((hasDerivAt_id t).const_mul (-s)).exp.const_mul C).const_add 1
  have hi := hd.inv hn
  convert hi using 1
  · funext x
    simp [one_div]
  · simp only [id_eq]
    rw [show 1 - 1 / (1 + C * Real.exp (-s * t)) =
      ((1 + C * Real.exp (-s * t)) - 1) / (1 + C * Real.exp (-s * t)) from by
        rw [sub_div, div_self hn]]
    simp only [div_eq_mul_inv, ← inv_pow]
    ring

/-- Source: haldane1957_cost_selection, pp. 514–515. -/
theorem substitution_frequency_tendsto {s p0 : ℝ}
    (hs : 0 < s) (_hp0 : 0 < p0) (_hp1 : p0 < 1) :
    Tendsto (substitutionFrequency s p0) atTop (nhds 1) := by
  have hex : Tendsto (fun t : ℝ => Real.exp (-s * t)) atTop (nhds 0) :=
    by simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_const_mul_atTop_of_pos hs).2 tendsto_id)
  have hden : Tendsto (fun t : ℝ => 1 + ((1 - p0) / p0) * Real.exp (-s * t))
      atTop (nhds (1 + ((1 - p0) / p0) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hex)
  unfold substitutionFrequency
  simpa only [Pi.div_def, zero_mul, mul_zero, add_zero, div_one] using
    (tendsto_const_nhds.div hden (by norm_num : (1:ℝ) + ((1 - p0) / p0) * 0 ≠ 0))

/-- Source: haldane1957_cost_selection, pp. 514–515, eq. 1–4. -/
theorem substitution_cost_integral {s p0 : ℝ}
    (hs : 0 < s) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    (∫ t in Set.Ioi (0:ℝ), s * (1 - substitutionFrequency s p0 t)) = -Real.log p0 := by
  have hder (t : ℝ) : HasDerivAt (fun t => Real.log (substitutionFrequency s p0 t))
      (s * (1 - substitutionFrequency s p0 t)) t := by
    have hpos := (substitution_frequency_mem (s := s) (t := t) hp0 hp1).1
    convert (substitution_frequency_deriv hp0 hp1 t).log hpos.ne' using 1
    field_simp
  have hlim : Tendsto (fun t => Real.log (substitutionFrequency s p0 t)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp
      (substitution_frequency_tendsto hs hp0 hp1)
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0:ℝ))
    (fun t _ => hder t)
    (fun t _ => mul_nonneg hs.le (le_of_lt (sub_pos.mpr
      (substitution_frequency_mem (s := s) (t := t) hp0 hp1).2))) hlim
  simpa [substitution_frequency_initial hp0 hp1] using h

end Rhone.Dynamics
