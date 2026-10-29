/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableNormalizedRate
public import Rhone.Statistics.Identifiability.ThreeSourceCDFSeparation

/-! # Three event probabilities separate every proper locally L1 island source with migration -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma first_marginal_normalized (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    (law k c q).map Prod.fst = (PanThreeSample.law (normalizedRate k c q)).map Prod.fst := by
  have hL := normalizedRate_locallyIntegrable k c q hc hq hqn
  have hLn := normalizedRate_nonnegative k c q
  have hdiv := normalized_clock_diverges k c q hc hq hcn hqn hproper
  rw [law_first_marginal k c q hc hq hcn hqn
    (fun s _ i =>
      PairIntegrable.all_pair_tails_of_initial_proper k c q hc hq hqn hproper hA hQ s i),
    PanThreeSample.first_marginal _ hL hLn hdiv]
  unfold firstLaw panPairLaw
  apply withDensity_congr_ae
  filter_upwards [(normalizedRate_eq_ae k c q hc hq hcn hqn).filter_mono
    (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioi] with t he ht
  change ENNReal.ofReal (firstDensity k c q t) =
    ENNReal.ofReal (3 * normalizedRate k c q t *
      Real.exp (-integratedClock (fun u => 3 * normalizedRate k c q u) t))
  rw [integratedClock_scale, ← neg_mul,
    ← survival_normalized_clock k c q hc hq hcn hqn ht.le, ← he ht.le]
  congr 1
  unfold firstDensity
  rw [← rateRatio_mul_survival k c q hc hq hqn ht.le]
  ring

theorem exists_nonzero_rectangleResidual (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ ThreeSampleCDF.rectangleResidual (law k c q) s t ≠ 0 := by
  by_contra hnone
  push Not at hnone
  let L := normalizedRate k c q
  have hL : LocallyIntegrable L volume := normalizedRate_locallyIntegrable k c q hc hq hqn
  have hLn : ∀ u, 0 ≤ L u := normalizedRate_nonnegative k c q
  have hdiv := normalized_clock_diverges k c q hc hq hcn hqn hproper
  let : IsProbabilityMeasure (law k c q) := law_probability k c q hc hq hcn hqn hproper
  let : IsProbabilityMeasure (PanThreeSample.law L) := PanThreeSample.isProbability L hL hLn hdiv
  have hfirst := first_marginal_normalized k c q hc hq hcn hqn hproper hA hQ
  change (law k c q).map Prod.fst = (PanThreeSample.law L).map Prod.fst at hfirst
  have he : law k c q = PanThreeSample.law L := by
    apply ThreeSampleCDF.eq_of_ordered_prefix_tail _ _ (ThreeTimeVarying.law_ordered_support k c q)
      (PanThreeSample.law_ordered_support L) hfirst
    intro s t hs hst
    have hi := hnone s t hs hst
    have hp := ThreeSampleCDF.pan_rectangleResidual_zero L hL hLn hdiv hs hst
    unfold ThreeSampleCDF.rectangleResidual ThreeSampleCDF.clockRoot
      ThreeSampleCDF.firstSurvival at hi hp
    rw [hfirst] at hi
    linarith
  exact law_ne_pan_of_positive_migration k c q hc hq hcn hqn hproper hA hQ L hL hLn hdiv he

end Rhone.Statistics.Identifiability.ThreeIntegrable
