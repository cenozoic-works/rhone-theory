/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.Criterion

/-! # Criterion for a general labelled duration law, including zero internal branches -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites
open FiniteBlockModel Algebra.Identifiability MarkovChain.Identifiability Identifiability
    ThreeSampleMembership

theorem nonnegative_internal_branch_separation_iff {k : ℝ} (hk : 0 < k)
    (μ : Measure Joint) [IsProbabilityMeasure μ]
    (hμ : NonnegativeJoint μ) (hu : ∀ᵐ g ∂μ, 0 < g.1.1)
    (P : FirstSurvivalProfile) (hP : P.Matches (μ.map Prod.fst)) :
    UniformlySeparated k μ ↔ μ ≠ uniformLift (PanThreeSample.durationLaw P.rate) := by
  let := PanThreeSample.durationLaw_probability P.rate P.rate_locallyIntegrable
    P.rate_nonnegative P.clock_diverges
  let : IsProbabilityMeasure (μ.map Prod.fst) :=
    inferInstance
  constructor
  · rintro ⟨L, ε, hε, hgap⟩ he
    have hh := hgap 2 (by omega) P.rate P.rate_locallyIntegrable P.rate_nonnegative
      P.clock_diverges k hk
    rw [he] at hh
    simp only [blockDistance, sub_self, abs_zero, Finset.sum_const_zero] at hh
    linarith
  · intro hne
    have hup : ∀ᵐ t ∂μ.map Prod.fst, 0 < t.1 :=
      (ae_map_iff measurable_fst.aemeasurable
        (show MeasurableSet {t : ℝ × ℝ | 0 < t.1} by measurability)).mpr hu
    have hfirst : μ.map (fun g : Joint => g.1.1) =
        (uniformLift (PanThreeSample.durationLaw P.rate)).map (fun g : Joint => g.1.1) := by
      rw [lifted_first_marginal, candidate_duration_first_marginal,
        ← weak_first_marginal_eq P (μ.map Prod.fst) hup hP,
        Measure.map_map measurable_fst measurable_fst]
      rfl
    have hpan : encodedProbability k (uniformLift (PanThreeSample.durationLaw P.rate)) ∈
        range compactPan := by
      let := panClockLaw_probability k P.rate P.rate_locallyIntegrable
        P.rate_nonnegative P.clock_diverges
      exact ⟨compactify (panClockLaw k P.rate),
        (pan_compact P.rate P.rate_locallyIntegrable
          P.rate_nonnegative P.clock_diverges hk.le).symm⟩
    have hout := outside_compact_of_distinct_candidate hk μ
      (uniformLift (PanThreeSample.durationLaw P.rate)) hμ
      (uniform_lift_nonnegative _ (PanThreeSample.durationLaw_nonnegative P.rate))
      (uniform_lift_internal_positive _ (pan_internal_positive P.rate)) hfirst hpan hne
    obtain ⟨L, ε, hε, hgap⟩ := uniform_gap_of_outside hk.le μ hμ hout
    exact ⟨L, ε, hε, fun K hK r hr hn ht l hl => hgap K hK r hr hn ht l hl.le⟩

end Rhone.Statistics.WeakRegularSeparation
