/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePatternMoments.ClockBridge
public import Rhone.Statistics.ConcretePatternMoments.SourceValues

/-! # Full labelled probability-table identities from CTMC moments -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ConcretePatternMoments
open ThreeTipSites ThreeSiteSeparator MarkovChain.Identifiability Identifiability

def momentTable (k : ℝ) (μ : Measure (ℝ × ℝ)) (j : Fin 19) : ℝ :=
  ∫ t, scaledKernel k (exponents j).1 (exponents j).2 t ∂μ

def tableMass (M : Fin 19 → ℝ) (r : Row) : ℝ :=
  (∑ j : Fin 19, (coefficient r j : ℝ) * M j) / 786432

def sourceWeights (r : Row) : ℝ := tableMass sourceValues r

theorem scaled_kernel_integrable {k : ℝ} (hk : 0 ≤ k) (p q : ℕ)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    Integrable (scaledKernel k p q) μ := by
  have hm : Measurable (scaledKernel k p q) := by unfold scaledKernel; fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [hμ] with t ht
  unfold scaledKernel
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  obtain ⟨ht1, ht2⟩ := ht
  have hp : 0 ≤ ((p : ℝ) + q) * t.1 + q * t.2 := by positivity
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hp

theorem mass_table {k : ℝ} (hk : 0 ≤ k) (μ : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) (x : Panel 4 3) :
    mass (uniformBlockRoots 4 3 (by norm_num)) k μ x = tableMass (momentTable k μ) (rowOf x) := by
  unfold mass
  simp_rw [conditional_moment_expansion]
  rw [integral_div, integral_finsetSum _ (fun j _ =>
    (scaled_kernel_integrable hk _ _ μ hμ).const_mul (coefficient (rowOf x) j : ℝ))]
  simp only [integral_const_mul, tableMass, momentTable]

theorem source_moment_table (j : Fin 19) :
    momentTable 2 (IslandThreeTimes.durationLaw 0 1 (1 / 100)) j = sourceValues j := by
  have he : scaledKernel 2 (exponents j).1 (exponents j).2 = fun t : ℝ × ℝ =>
      Real.exp (-(((exponents j).1 : ℝ) + (exponents j).2) * t.1 -
        ((exponents j).2 : ℝ) * t.2) := by
    funext t
    unfold scaledKernel
    congr 1
    ring
  unfold momentTable
  rw [he, integral_eq_sourceValues]

theorem source_full_labelled_mass (x : Panel 4 3) :
    mass (uniformBlockRoots 4 3 (by norm_num)) 2
      (IslandThreeTimes.durationLaw 0 1 (1 / 100)) x = sourceWeights (rowOf x) := by
  let := IslandThreeTimes.durationLaw_probability 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 100)
  rw [mass_table (by norm_num) _ (IslandThreeTimes.durationLaw_nonnegative 0 1 (1 / 100))]
  simp only [tableMass, sourceWeights, source_moment_table]

theorem source_weights_nonnegative (x : Panel 4 3) : 0 ≤ sourceWeights (rowOf x) := by
  rw [← source_full_labelled_mass]
  exact mass_nonneg _ (by norm_num) (IslandThreeTimes.durationLaw_nonnegative 0 1 (1 / 100)) x

theorem source_weights_normalized : (∑ x : Panel 4 3, sourceWeights (rowOf x)) = 1 := by
  let := IslandThreeTimes.durationLaw_probability 0 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 100)
  simp_rw [← source_full_labelled_mass]
  exact mass_sum (by norm_num) _ (by norm_num)
    (IslandThreeTimes.durationLaw_nonnegative 0 1 (1 / 100))

end Rhone.Statistics.ConcretePatternMoments
