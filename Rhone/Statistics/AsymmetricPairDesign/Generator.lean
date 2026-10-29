/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExitLaw
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-! # Asymmetric three-state absorption generator and probability laws -/

@[expose] public section

open scoped Matrix Topology
open Filter MeasureTheory Set
namespace Rhone.Statistics.AsymmetricPairDesign
open MarkovChain.Identifiability Identifiability

noncomputable def generator (a b c d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-c - 2 * a, 2 * a, 0; b, -a - b, a; 0, 2 * b, -d - 2 * b]

noncomputable def rate (c d : ℝ) : Fin 3 → ℝ := ![c, 0, d]

noncomputable def meanDenominator (a b c d : ℝ) : ℝ :=
  2 * a ^ 2 * d + a * c * d + 2 * b ^ 2 * c + b * c * d

noncomputable def meanPotential (a b c d : ℝ) : Fin 3 → ℝ :=
  ![(2 * a ^ 2 + 4 * a * b + 3 * a * d + 2 * b ^ 2 + b * d) / meanDenominator a b c d,
    (2 * a ^ 2 + 4 * a * b + a * c + 2 * a * d + 2 * b ^ 2 + 2 * b * c + b * d + c * d) /
      meanDenominator a b c d,
    (2 * a ^ 2 + 4 * a * b + a * c + 2 * b ^ 2 + 3 * b * c) / meanDenominator a b c d]

theorem generator_metzler {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsMetzler (generator a b c d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [generator]

theorem generator_row_sum (a b c d : ℝ) (i : Fin 3) :
    ∑ j, generator a b c d i j = -rate c d i := by
  fin_cases i <;> simp [generator, rate, Fin.sum_univ_succ]; ring

theorem exit_rate (a b c d : ℝ) : exitRate (generator a b c d) = rate c d := by
  funext i
  simp [exitRate, Matrix.mulVec, dotProduct, generator_row_sum]

theorem mean_denominator_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) : 0 < meanDenominator a b c d := by
  unfold meanDenominator
  positivity

theorem mean_potential_nonneg {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (i : Fin 3) : 0 ≤ meanPotential a b c d i := by
  have hD := mean_denominator_pos ha hb hc hd
  fin_cases i <;> change 0 ≤ _ / _ <;> exact div_nonneg (by positivity) hD.le

theorem mean_equation {a b c d : ℝ} (hD : meanDenominator a b c d ≠ 0) :
    generator a b c d *ᵥ meanPotential a b c d = fun _ => -1 := by
  ext i
  fin_cases i <;> simp [generator, meanPotential, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> field_simp [hD] <;> simp only [meanDenominator] <;> ring

theorem survival_vanishes {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (i : Fin 3) :
    Tendsto (flowOutput (generator a b c d) i (fun _ => 1) 0) atTop (𝓝 0) := by
  apply survival_tendsto_zero_of_lyapunov (generator a b c d)
    (generator_metzler ha.le hb.le) (fun j => 1 + meanPotential a b c d j)
    (fun j => by linarith [mean_potential_nonneg ha hb hc hd j]) (a := 1)
    zero_lt_one _ i
  intro j
  have heq := congrFun (mean_equation (mean_denominator_pos ha hb hc hd).ne') j
  have hrow := generator_row_sum a b c d j
  have hr : 0 ≤ rate c d j := by fin_cases j <;> simp [rate, hc.le, hd.le]
  simp only [Matrix.mulVec, dotProduct, mul_add, mul_one, Finset.sum_add_distrib] at *
  linarith

noncomputable def pairLaw (a b c d : ℝ) (i : Fin 3) : Measure ℝ :=
  firstExitLaw (generator a b c d) i

theorem pair_law_probability {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (i : Fin 3) : IsProbabilityMeasure (pairLaw a b c d i) := by
  apply firstExitLaw_probability _ (generator_metzler ha.le hb.le) _ i
    (survival_vanishes ha hb hc hd i)
  intro j
  rw [generator_row_sum]
  fin_cases j <;> simp [rate, hc.le, hd.le]

end Rhone.Statistics.AsymmetricPairDesign
