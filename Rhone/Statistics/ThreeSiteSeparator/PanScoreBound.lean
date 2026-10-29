/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ScaledGenealogyScore
public import Rhone.Statistics.ThreeSiteSeparator.SortedPairMoments

/-! # Universal nonpositive three-site score for proper panmictic histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open Algebra.Identifiability MarkovChain.Identifiability Identifiability

lemma pan_combined_sorted (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {a : ℝ} (ha : 0 ≤ a) (p q s t : ℕ) :
    (∫ z, scaledCombinedKernel a p q s t z ∂PanThreeSample.durationLaw r) =
      ((∫ z, z.1^p*z.2^q ∂sortedPairLaw (panClockLaw a r))+
        2*(∫ z, z.1^s*z.2^t ∂sortedPairLaw (panClockLaw a r)))/3 := by
  let : IsProbabilityMeasure (PanThreeSample.durationLaw r) :=
    PanThreeSample.durationLaw_probability r hr hn ht
  rw [scaledCombinedKernel_integral ha _ (PanThreeSample.durationLaw_nonnegative r),
    pan_duration_sorted_moment r hr hn ht ha, pan_duration_sorted_moment r hr hn ht ha]

lemma pan_pair_CDF_moment (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {a : ℝ} (ha : 0 < a) (s : ℕ) :
    (∫ z, scaledCombinedKernel a (s+1) 0 0 (s+1) z ∂PanThreeSample.durationLaw r) =
      cdfPairMoment (s+1) (fun x => (panClockLaw a r).real (Iic x)) := by
  let : IsProbabilityMeasure (panClockLaw a r) := panClockLaw_probability a r hr hn ht
  rw [pan_combined_sorted r hr hn ht ha.le]
  simp only [pow_zero, mul_one, one_mul]
  exact sortedPair_pair_moment _ (panClockLaw_unit_support a r)
    (panClockLaw_CDF_continuous ha r hr hn ht) s

lemma pan_mixed_CDF_moment (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {a : ℝ} (ha : 0 < a) (p q : ℕ) :
    (∫ z, scaledDurationKernel a (p+1) (q+1) z ∂PanThreeSample.durationLaw r) =
      cdfMixedMoment (p+1) (q+1) (fun x => (panClockLaw a r).real (Iic x)) := by
  let : IsProbabilityMeasure (panClockLaw a r) := panClockLaw_probability a r hr hn ht
  rw [pan_duration_sorted_moment r hr hn ht ha.le]
  exact sortedPair_mixed_moment _ (panClockLaw_unit_support a r)
    (panClockLaw_CDF_continuous ha r hr hn ht) p q

theorem pan_genealogy_score_nonpos (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {k : ℝ} (hk : 0 < k) : genealogyScore k (PanThreeSample.durationLaw r) ≤ 0 := by
  let : IsProbabilityMeasure (PanThreeSample.durationLaw r) :=
    PanThreeSample.durationLaw_probability r hr hn ht
  let : IsProbabilityMeasure (panClockLaw (k/2) r) := panClockLaw_probability (k/2) r hr hn ht
  have ha : 0 < k/2 := by positivity
  rw [genealogyScore_scaled]
  rw [pan_pair_CDF_moment r hr hn ht ha 1, pan_pair_CDF_moment r hr hn ht ha 3,
    pan_pair_CDF_moment r hr hn ht ha 5]
  rw [scaledCombinedKernel_integral ha.le _ (PanThreeSample.durationLaw_nonnegative r),
    scaledCombinedKernel_integral ha.le _ (PanThreeSample.durationLaw_nonnegative r)]
  rw [pan_mixed_CDF_moment r hr hn ht ha 4 1, pan_mixed_CDF_moment r hr hn ht ha 0 5,
    pan_mixed_CDF_moment r hr hn ht ha 2 3]
  have h := cdf_moment_score_nonpos (panClockLaw (k/2) r)
    ((panClockLaw_unit_support (k/2) r).mono fun _ h => h.1)
    (panClockLaw_CDF_continuous ha r hr hn ht) (fun _ => rfl)
  convert! h using 1
  unfold cdfH cdfJ
  congr 1
  ring

end Rhone.Statistics.ThreeSiteSeparator
