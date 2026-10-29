/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableCountLaw

/-! # A nonnegative L1 pan candidate from the source first-merger law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma rateRatio_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) (t : ℝ) : 0 ≤ rateRatio k c q t := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (preRow_nonnegative k c q hc hq hqn (le_max_right t 0) i)
    fin_cases i <;> norm_num [mergerWeight]
  · exact mul_nonneg (by norm_num) (survival_positive k c q hc hq hqn (le_max_right t 0)).le

def normalizedRate (k : ℕ) (c q : ℝ → ℝ) : ℝ → ℝ :=
  PanThreeSample.nonnegativeRepresentative (fun t => c t * rateRatio k c q t)

lemma normalizedRate_nonnegative (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) :
    0 ≤ normalizedRate k c q t := PanThreeSample.representative_nonneg _ t

lemma normalizedRate_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) : LocallyIntegrable (normalizedRate k c q) volume :=
  PanThreeSample.representative_locallyIntegrable
    ((hc.mul_continuous (rateRatio_continuous k c q hc hq hqn)).locallyIntegrableOn (Ici 0))

lemma normalizedRate_eq_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ∀ᵐ t, 0 ≤ t → c t * rateRatio k c q t = normalizedRate k c q t := by
  apply PanThreeSample.representative_eq_ae
  filter_upwards [hcn] with t ht ht0
  exact mul_nonneg (ht ht0) (rateRatio_nonnegative k c q hc hq hqn t)

lemma survival_normalized_clock (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) :
    survival k c q t = Real.exp (-3 * integratedClock (normalizedRate k c q) t) := by
  have hL := normalizedRate_locallyIntegrable k c q hc hq hqn
  have h3 : LocallyIntegrable (fun u => 3 * normalizedRate k c q u) volume := by
    convert! hL.smul (3 : ℝ) using 1
  have hd : ∀ᵐ u, u ∈ uIcc (0 : ℝ) t → HasDerivAt (survival k c q)
      (-(3 * normalizedRate k c q u) * survival k c q u) u := by
    filter_upwards [survival_derivative_ae k c q hc hq,
      normalizedRate_eq_ae k c q hc hq hcn hqn] with u hu he hmem
    have hu0 : 0 ≤ u := (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ u ∧ u ≤ t).1
    apply hu.congr_deriv
    rw [← he hu0]
    unfold firstDensity
    rw [← rateRatio_mul_survival k c q hc hq hqn hu0]
    ring
  have he := scalar_ac_survival_identity (fun u => 3 * normalizedRate k c q u)
    (survival k c q) h3 0 t (survival_ac k c q hc hq 0 t) hd
  simpa [survival_initial k c q hc hq, intervalIntegral.integral_const_mul,
    integratedClock] using he

lemma normalized_clock_diverges (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (integratedClock (normalizedRate k c q)) atTop atTop := by
  have hdiv : Tendsto (fun t => 3 * integratedClock (normalizedRate k c q) t) atTop atTop := by
    apply tendsto_atTop_of_survival_lower_bound (survival k c q)
      (fun t => 3 * integratedClock (normalizedRate k c q) t) (a := 1) (by norm_num)
      (survival_tendsto_zero_of_pair k c q hc hq hcn hqn hproper)
    intro t ht
    rw [survival_normalized_clock k c q hc hq hcn hqn ht]
    simp only [one_mul, neg_mul, le_refl]
  have h := hdiv.const_mul_atTop (show (0 : ℝ) < 1 / 3 by norm_num)
  convert! h using 1
  funext t
  ring

end Rhone.Statistics.Identifiability.ThreeIntegrable
