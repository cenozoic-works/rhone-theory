/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeCanonicalFirstLaw
public import Rhone.Statistics.Identifiability.OrderedPrefixTailUniqueness

/-! # A finite-event, density-free separator for every nonzero continuous island history -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma first_marginal_canonical (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    (law k c q).map Prod.fst = (PanThreeSample.law (canonicalRate k c q)).map Prod.fst := by
  have hL := canonicalRate_continuous k c q hc hq hqn
  have hLn := canonicalRate_nonnegative k c q hc hq hcn hqn
  have hdiv := canonical_clock_diverges k c q hc hq hcn hqn hproper
  rw [law_first_marginal k c q hc hq hcn hqn
    (fun s _ i =>
      PairProperness.all_pair_tails_of_initial_proper k c q hc hq hqn hproper hA hQ s i),
    PanThreeSample.first_marginal _ hL.locallyIntegrable hLn hdiv]
  unfold firstLaw panPairLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ENNReal.ofReal (firstDensity k c q t) =
    ENNReal.ofReal (3 * canonicalRate k c q t *
      Real.exp (-integratedClock (fun u => 3 * canonicalRate k c q u) t))
  rw [integratedClock_scale, ← neg_mul, ← survival_canonical_clock k c q hc hq hqn ht.le,
    canonicalRate_mul_survival k c q hc hq hqn ht.le]

theorem exists_nonzero_rectangleResidual (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ ThreeSampleCDF.rectangleResidual (law k c q) s t ≠ 0 := by
  by_contra hnone
  push Not at hnone
  let L := canonicalRate k c q
  have hL : Continuous L := canonicalRate_continuous k c q hc hq hqn
  have hLn : ∀ u, 0 ≤ L u := canonicalRate_nonnegative k c q hc hq hcn hqn
  have hdiv := canonical_clock_diverges k c q hc hq hcn hqn hproper
  let : IsProbabilityMeasure (law k c q) := law_probability k c q hc hq hcn hqn hproper
  let : IsProbabilityMeasure (PanThreeSample.law L) :=
    PanThreeSample.isProbability L hL.locallyIntegrable hLn hdiv
  have hfirst := first_marginal_canonical k c q hc hq hcn hqn hproper hA hQ
  change (law k c q).map Prod.fst = (PanThreeSample.law L).map Prod.fst at hfirst
  have he : law k c q = PanThreeSample.law L := by
    apply ThreeSampleCDF.eq_of_ordered_prefix_tail _ _ (law_ordered_support k c q)
      (PanThreeSample.law_ordered_support L) hfirst
    intro s t hs hst
    have hi := hnone s t hs hst
    have hp := ThreeSampleCDF.pan_rectangleResidual_zero L hL.locallyIntegrable hLn hdiv hs hst
    unfold ThreeSampleCDF.rectangleResidual ThreeSampleCDF.clockRoot
      ThreeSampleCDF.firstSurvival at hi hp
    rw [hfirst] at hi
    linarith
  exact law_ne_pan_of_positive_migration k c q hc hq hcn hqn hproper hA hQ
    L hL.locallyIntegrable hLn hdiv he

end Rhone.Statistics.Identifiability.ThreeTimeVarying
