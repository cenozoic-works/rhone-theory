/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleScalarClock

/-! # Island three-sample counts separate from pan counts with an unknown mutation scalar -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace ScalarCountClock

def ClockCompetitor := {r : ℝ // 0 < r} × FiniteCountSeparation.ProperHazard

def competitorDuration (targetRate : ℝ) (P : ClockCompetitor) :
    ProbabilityMeasure (ℝ × ℝ) :=
  scaleProbability (P.1.val / targetRate) (FiniteCountSeparation.panDuration P.2)

lemma competitorDuration_countVector {targetRate : ℝ} (htarget : 0 < targetRate)
    (P : ClockCompetitor) (k : ℕ × ℕ) :
    ThreeSampleCounts.countVector targetRate (competitorDuration targetRate P) k =
      (PanThreeSample.countLaw P.1.val P.2.val).real {k} := by
  rw [competitorDuration, countVector_scaleProbability (FiniteCountSeparation.panDuration P.2)
    (PanThreeSample.durationLaw_nonnegative P.2.val)
    (div_pos P.1.property htarget).le htarget.le]
  rw [show targetRate * (P.1.val / targetRate) = P.1.val by
    field_simp [htarget.ne']]
  rfl

end ScalarCountClock

theorem island_three_counts_uniform_finite_box_unknown_scalar (k : ℕ)
    {c q targetMutation : ℝ} (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < targetMutation) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ panMutation : ℝ, 0 < panMutation →
      ∀ rate : ℝ → ℝ, LocallyIntegrable rate volume → (∀ t, 0 ≤ rate t) →
      Tendsto (integratedClock rate) atTop atTop →
      ∃ i ≤ K, ∃ j ≤ K,
        ε ≤ |(PanThreeSample.countLaw panMutation rate).real {(i, j)} -
          (IslandThreeTimes.countLaw k c q targetMutation).real {(i, j)}| := by
  obtain ⟨K, ε, hε, hsep⟩ := FiniteCountSeparation.uniform_count_box_of_pan_invariant
    (ScalarCountClock.competitorDuration targetMutation)
    (FiniteCountSeparation.islandDuration k hc hq)
    (fun P => ScalarCountClock.nonnegative_scaleProbability
      (div_pos P.1.property hmutation).le _
      (PanThreeSample.durationLaw_nonnegative P.2.val))
    (IslandThreeTimes.durationLaw_nonnegative k c q)
    (fun P => ScalarCountClock.scaled_pan_invariant P.2 (div_pos P.1.property hmutation))
    (FiniteCountSeparation.islandDuration_not_invariant k hc hq) hmutation
  refine ⟨K, ε, hε, fun panMutation hpan rate hr hn htail => ?_⟩
  let P : ScalarCountClock.ClockCompetitor := (⟨panMutation, hpan⟩, ⟨rate, hr, hn, htail⟩)
  obtain ⟨i, hi, j, hj, hgap⟩ := hsep P
  refine ⟨i, hi, j, hj, ?_⟩
  rw [ScalarCountClock.competitorDuration_countVector hmutation P] at hgap
  exact hgap

theorem island_three_counts_uniform_finite_box_halfLine_unknown_scalar (k : ℕ)
    {c q targetMutation : ℝ} (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < targetMutation) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ panMutation : ℝ, 0 < panMutation →
      ∀ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume →
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) →
      Tendsto (integrablePanClock rate) atTop atTop →
      ∃ i ≤ K, ∃ j ≤ K,
        ε ≤ |(PanThreeSample.countLaw panMutation rate).real {(i, j)} -
          (IslandThreeTimes.countLaw k c q targetMutation).real {(i, j)}| := by
  obtain ⟨K, ε, hε, hsep⟩ :=
    island_three_counts_uniform_finite_box_unknown_scalar k hc hq hmutation
  refine ⟨K, ε, hε, fun panMutation hpan rate hr hn htail => ?_⟩
  rw [PanThreeSample.countLaw_congr_halfLine_ae panMutation
    (PanThreeSample.representative_eq_ae hn)]
  exact hsep panMutation hpan (PanThreeSample.nonnegativeRepresentative rate)
    (PanThreeSample.representative_locallyIntegrable hr)
    (PanThreeSample.representative_nonneg rate)
    (PanThreeSample.representative_clock_diverges hn htail)

theorem island_three_counts_uniform_iid_test_unknown_scalar (k : ℕ)
    {c q targetMutation : ℝ} (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < targetMutation) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ S : ℕ, 0 < S →
      (FinitePanelSampling.iidLaw (IslandThreeTimes.countLaw k c q targetMutation) S).real
        (FiniteCountSeparation.acceptTarget
          (fun cell => (IslandThreeTimes.countLaw k c q targetMutation).real {cell}) K S ε)ᶜ ≤
        2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) ∧
      ∀ panMutation : ℝ, 0 < panMutation →
        ∀ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume →
          (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) →
          Tendsto (integrablePanClock rate) atTop atTop →
          (FinitePanelSampling.iidLaw (PanThreeSample.countLaw panMutation rate) S).real
            (FiniteCountSeparation.acceptTarget
              (fun cell => (IslandThreeTimes.countLaw k c q targetMutation).real {cell}) K S ε) ≤
            2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  obtain ⟨K, ε, hε, hsep⟩ :=
    island_three_counts_uniform_finite_box_halfLine_unknown_scalar k hc hq hmutation
  refine ⟨K, ε, hε, fun S hS => ?_⟩
  let : IsProbabilityMeasure (IslandThreeTimes.countLaw k c q targetMutation) :=
    IslandThreeTimes.countLaw_probability k hc hq hmutation.le
  refine ⟨FiniteCountSeparation.target_error _ K hS hε.le, ?_⟩
  intro panMutation hpan rate hr hn htail
  let : IsProbabilityMeasure (PanThreeSample.countLaw panMutation rate) :=
    PanThreeSample.countLaw_probability_halfLine panMutation hpan.le rate hr hn htail
  exact FiniteCountSeparation.competitor_error _ _ K hS hε.le
    (hsep panMutation hpan rate hr hn htail)

end Rhone.Statistics.Identifiability
