/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.PanClockLaw
public import Rhone.Statistics.ThreeSiteSeparator.SortedMonomialIID

/-! # Pan merger moments agree with the sorted clock law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open AtomicRank AtomicSmoothing Algebra.Identifiability MarkovChain.Identifiability Identifiability
    PanIIDRepresentation

def scaledDurationKernel (a : ℝ) (p q : ℕ) (t : ℝ × ℝ) : ℝ :=
  Real.exp (-a*t.1)^p*Real.exp (-a*(t.1+t.2))^q

lemma pan_ordered_sorted_moment (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {a : ℝ} (ha : 0 ≤ a) (p q : ℕ) :
    (∫ t, (scaledClock a t.1)^p*(scaledClock a t.2)^q ∂PanThreeSample.law r) =
      ∫ z, z.1^p*z.2^q ∂sortedPairLaw (panClockLaw a r) := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  let : IsProbabilityMeasure (panClockLaw a r) := panClockLaw_probability a r hr hn ht
  rw [sortedPair_monomial_iid _ (panClockLaw_unit_support a r)]
  unfold panClockLaw
  rw [mapped_iid_polynomial _ _ (scaledClock_continuous a).measurable,
    ← pan_scaled_polynomial_iid r hr hn ht ha]
  simp only [scaledFeature, value_single, one_mul]

lemma pan_duration_sorted_moment (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {a : ℝ} (ha : 0 ≤ a) (p q : ℕ) :
    (∫ t, scaledDurationKernel a p q t ∂PanThreeSample.durationLaw r) =
      ∫ z, z.1^p*z.2^q ∂sortedPairLaw (panClockLaw a r) := by
  rw [← pan_ordered_sorted_moment r hr hn ht ha p q,
    PanThreeSample.durationLaw,
    integral_map_of_stronglyMeasurable PanThreeSample.measurable_toDurations
      (by unfold scaledDurationKernel; fun_prop)]
  apply integral_congr_ae
  filter_upwards [PanThreeSample.law_ordered_support r] with t ht
  unfold scaledDurationKernel PanThreeSample.toDurations scaledClock
  dsimp only
  rw [unitClock_eq (mul_nonneg ha ht.1.le),
    unitClock_eq (mul_nonneg ha (ht.1.trans ht.2).le)]
  simp only [show t.1+(t.2-t.1) = t.2 by ring, neg_mul]

end Rhone.Statistics.ThreeSiteSeparator
