/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeResidual
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Integration
/-!
# Centred founder-effect moments

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section

open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics
open scoped ENNReal

namespace Rhone.Statistics
theorem centered_gene_mean (ν : Measure Real) [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) :
    (∫ x, x - ∫ y, y ∂ν ∂ν) = 0 := by
  have hi : Integrable (fun x : Real => x) ν := hν.integrable (by norm_num)
  rw [integral_sub hi (integrable_const _), integral_const]
  simp

theorem centered_founder_cross {n : Nat} (ν : Measure Real) [IsProbabilityMeasure ν]
    (hν : MemLp id 2 ν) (a b : Fin n) :
    (∫ e : Fin n → Real, (e a - ∫ x, x ∂ν) * (e b - ∫ x, x ∂ν)
      ∂(Measure.pi fun _ : Fin n => ν)) =
      if a = b then Var[id; ν] else 0 := by
  classical
  let m := ∫ x, x ∂ν
  have hm : MemLp (fun x : Real => x - m) 2 ν := hν.sub (memLp_const m)
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    have heq : (fun e : Fin n → Real => (e a - m) * (e a - m)) =
        (fun e => (e a - m)^2) := by funext e; ring
    change (∫ e : Fin n → Real, (e a - m) * (e a - m) ∂Measure.pi (fun _ => ν)) = _
    rw [heq]
    rw [integral_comp_eval (μ := fun _ : Fin n => ν) (i := a)
      (f := fun x : Real => (x - m)^2) (by fun_prop)]
    exact (variance_eq_integral aemeasurable_id).symm
  · simp only [hab, ↓reduceIte]
    have hind : iIndepFun (fun i : Fin n => fun e : Fin n → Real => e i - m)
        (Measure.pi fun _ : Fin n => ν) :=
      iIndepFun_pi (μ := fun _ : Fin n => ν)
        (X := fun _ : Fin n => fun x : Real => x - m) (fun _ => by fun_prop)
    change (∫ e : Fin n → Real, (e a - m) * (e b - m) ∂Measure.pi (fun _ => ν)) = 0
    rw [(hind.indepFun hab).integral_fun_mul_eq_mul_integral
      ((measurable_pi_apply a).sub measurable_const).aestronglyMeasurable
      ((measurable_pi_apply b).sub measurable_const).aestronglyMeasurable]
    rw [integral_comp_eval (μ := fun _ : Fin n => ν) (i := a)
      (f := fun x : Real => x - m) (by fun_prop),
      integral_comp_eval (μ := fun _ : Fin n => ν) (i := b)
        (f := fun x : Real => x - m) (by fun_prop)]
    rw [centered_gene_mean ν hν]
    simp
end Rhone.Statistics
