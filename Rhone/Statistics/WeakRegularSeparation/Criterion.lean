/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.UniformGap
public import Rhone.Statistics.WeakRegularSeparation.EncodedMarginal
public import Rhone.Statistics.WeakRegularSeparation.WeakFirstMarginal
public import Rhone.Statistics.FiniteBlockModel.ExactPan

/-! # Weak-branch regular-profile criterion with one alphabet-uniform block and gap -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites
open FiniteBlockModel Algebra.Identifiability MarkovChain.Identifiability Identifiability
    ThreeSampleMembership

def UniformlySeparated (k : ℝ) (μ : Measure Joint) : Prop :=
  ∃ L : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (K : ℕ) (hK : 2 ≤ K)
    (r : ℝ → ℝ) (_hr : LocallyIntegrable r volume) (_hn : ∀ t, 0 ≤ r t)
    (_ht : Tendsto (integratedClock r) atTop atTop) (l : ℝ), 0 < l →
    ε ≤ blockDistance (K := K) (L := L) k l μ (uniformLift (PanThreeSample.durationLaw r))
      (show 0 < K by omega)

theorem lifted_first_marginal (μ : Measure (ℝ × ℝ)) [SFinite μ] :
    (uniformLift μ).map (fun g : Joint => g.1.1) = μ.map Prod.fst := by
  calc
    _ = ((uniformLift μ).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by rw [uniform_lift_projection]

theorem regular_profile_uniform_criterion {k : ℝ} (hk : 0 < k)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : NonnegativeTimes μ) (hu : ∀ᵐ t ∂μ, 0 < t.1)
    (P : FirstSurvivalProfile) (hP : P.Matches μ) :
    UniformlySeparated k (uniformLift μ) ↔ μ ≠ PanThreeSample.durationLaw P.rate := by
  let := PanThreeSample.durationLaw_probability P.rate P.rate_locallyIntegrable
    P.rate_nonnegative P.clock_diverges
  constructor
  · rintro ⟨L, ε, hε, hgap⟩ he
    have hh := hgap 2 (by omega) P.rate P.rate_locallyIntegrable P.rate_nonnegative
      P.clock_diverges k hk
    rw [he] at hh
    simp only [blockDistance, sub_self, abs_zero, Finset.sum_const_zero] at hh
    linarith
  · intro hne
    have hfirst : (uniformLift μ).map (fun g : Joint => g.1.1) =
        (uniformLift (PanThreeSample.durationLaw P.rate)).map (fun g : Joint => g.1.1) := by
      rw [lifted_first_marginal, lifted_first_marginal,
        candidate_duration_first_marginal, weak_first_marginal_eq P μ hu hP]
    have hpan : encodedProbability k (uniformLift (PanThreeSample.durationLaw P.rate)) ∈
        range compactPan := by
      let := panClockLaw_probability k P.rate P.rate_locallyIntegrable
        P.rate_nonnegative P.clock_diverges
      exact ⟨compactify (panClockLaw k P.rate),
        (pan_compact P.rate P.rate_locallyIntegrable
          P.rate_nonnegative P.clock_diverges hk.le).symm⟩
    have hout := outside_compact_of_distinct_candidate hk (uniformLift μ)
      (uniformLift (PanThreeSample.durationLaw P.rate)) (uniform_lift_nonnegative μ hμ)
      (uniform_lift_nonnegative _ (PanThreeSample.durationLaw_nonnegative P.rate))
      (uniform_lift_internal_positive _ (pan_internal_positive P.rate)) hfirst hpan
      (fun he => hne ((uniform_lift_injective μ _).mp he))
    obtain ⟨L, ε, hε, hgap⟩ := uniform_gap_of_outside hk.le (uniformLift μ)
      (uniform_lift_nonnegative μ hμ) hout
    exact ⟨L, ε, hε, fun K hK r hr hn ht l hl => hgap K hK r hr hn ht l hl.le⟩

end Rhone.Statistics.WeakRegularSeparation
