/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.FiniteMixture
public import Rhone.Statistics.PairObservationChannel.LaplaceKernel
public import Rhone.Statistics.PairObservationChannel.Law

/-! # Finite linked-panel mixture: one shared pair time, conditionally independent reported sites -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairMoments
open DependenceBudget DependentPairedTest PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def panelWeight (E : Channel K H) (k t : ℝ) (L : ℕ)
    (x : Fin L → H × H) : ℝ :=
  ∏ i, reportedMass E (Real.exp (-k * t)) (x i).1 (x i).2

theorem exp_parameter_bounds {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t) :
    0 ≤ Real.exp (-k * t) ∧ Real.exp (-k * t) ≤ 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith)⟩

theorem panel_weight_nonneg (E : Channel K H) {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    (L : ℕ) (x : Fin L → H × H) : 0 ≤ panelWeight E k t L x :=
  (iid (reportedLaw E _ (exp_parameter_bounds hk ht)) L).nonneg x

theorem panel_weight_total (E : Channel K H) {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    (L : ℕ) : ∑ x, panelWeight E k t L x = 1 :=
  (iid (reportedLaw E _ (exp_parameter_bounds hk ht)) L).total

theorem panel_weight_le_one (E : Channel K H) {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    (L : ℕ) (x : Fin L → H × H) : panelWeight E k t L x ≤ 1 := by
  rw [← panel_weight_total E hk ht L]
  exact Finset.single_le_sum (fun y _ => panel_weight_nonneg E hk ht L y)
    (Finset.mem_univ x)

theorem panel_weight_integrable (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (L : ℕ) (x : Fin L → H × H) : Integrable (fun t => panelWeight E k t L x) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold panelWeight reportedMass; fun_prop)
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (panel_weight_nonneg E hk ht L x)]
  exact panel_weight_le_one E hk ht L x

noncomputable def panelLaw (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (L : ℕ) : Law (Fin L → H × H) :=
  finiteMixture μ (fun t x => panelWeight E k t L x)
    (panel_weight_integrable E μ hk hμ L)
    (fun x => hμ.mono (fun _ ht => panel_weight_nonneg E hk ht L x))
    (hμ.mono (fun _ ht => panel_weight_total E hk ht L))

theorem conditional_product_expectation (E : Channel K H) {k t : ℝ}
    (hk : 0 ≤ k) (ht : 0 ≤ t) (L : ℕ) (f : Fin L → H × H → ℝ) :
    (∑ x, panelWeight E k t L x * ∏ i, f i (x i)) =
      ∏ i, rejection (reportedLaw E _ (exp_parameter_bounds hk ht)) (f i) :=
  expectation_product (reportedLaw E _ (exp_parameter_bounds hk ht)) L f

end Rhone.Statistics.LinkedPairMoments
