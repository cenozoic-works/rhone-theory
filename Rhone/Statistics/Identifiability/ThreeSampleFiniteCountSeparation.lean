/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleWeakObservation
public import Rhone.Statistics.Identifiability.FiniteCountTesting
public import Rhone.Statistics.Identifiability.ThreeSampleCountAE

/-! # A uniform finite-count experiment for every fixed island target -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace FiniteCountSeparation

def ProperHazard := {rate : ℝ → ℝ // LocallyIntegrable rate volume ∧
  (∀ t, 0 ≤ rate t) ∧ Tendsto (integratedClock rate) atTop atTop}

def panDuration (rate : ProperHazard) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨PanThreeSample.durationLaw rate.val,
    PanThreeSample.durationLaw_probability rate.val rate.property.1
      rate.property.2.1 rate.property.2.2⟩

def islandDuration (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ProbabilityMeasure (ℝ × ℝ) :=
  ⟨IslandThreeTimes.durationLaw k c q, IslandThreeTimes.durationLaw_probability k hc hq⟩

lemma panDuration_invariant (rate : ProperHazard) : PanInvariant (panDuration rate) := by
  intro t ht
  have hr := rate.property.1
  have hn := rate.property.2.1
  have htail := rate.property.2.2
  have h3rate : LocallyIntegrable (fun s => 3 * rate.val s) volume := by
    convert! hr.smul (3 : ℝ) using 1
  have hfirst : 1 - firstCDF (panDuration rate) t =
      Real.exp (-3 * integratedClock rate.val t) := by
    change 1 - ((PanThreeSample.durationLaw rate.val).map Prod.fst).real (Ioc 0 t) = _
    rw [PanThreeSample.durationLaw_first_marginal rate.val hr hn htail,
      panPairLaw_real_Ioc _ h3rate (fun s => mul_nonneg (by norm_num) (hn s)) ht.1,
      integratedClock_scale]
    ring_nf
  have hroot : 1 - rootCDF (panDuration rate) t =
      (3/2 : ℝ) * Real.exp (-integratedClock rate.val t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate.val t) := by
    change 1 - ((PanThreeSample.durationLaw rate.val).map
      (fun p => p.1 + p.2)).real (Ioc 0 t) = _
    rw [PanThreeSample.durationLaw_root_cdf rate.val hr hn ht.1]
    ring
  rw [hfirst, hroot]
  have heq : Real.exp (-3 * integratedClock rate.val t) / 3 +
      2 * ((3/2 : ℝ) * Real.exp (-integratedClock rate.val t) -
        (1/2 : ℝ) * Real.exp (-3 * integratedClock rate.val t)) / 3 =
      Real.exp (-integratedClock rate.val t) := by ring
  rw [heq, ← Real.exp_nat_mul]
  congr 1
  ring

lemma islandDuration_not_invariant (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ¬ PanInvariant (islandDuration k hc hq) := by
  intro h
  apply threeWitness_not_zero_on_unit_interval k hc hq
  intro t ht
  have hfirst : 1 - firstCDF (islandDuration k hc hq) t =
      threeSurvivalJet k c q 0 t := by
    change 1 - ((IslandThreeTimes.durationLaw k c q).map Prod.fst).real (Ioc 0 t) = _
    rw [IslandThreeTimes.durationLaw_map_first k hc hq]
    exact threeLaw_survival_CDF k hc.le hq.le ht.1
  have hroot : 1 - rootCDF (islandDuration k hc hq) t =
      flowOutput (islandThreeTreeGenerator k c q) 0 (fun _ => 1) 0 t := by
    change 1 - ((IslandThreeTimes.durationLaw k c q).map
      (fun p => p.1 + p.2)).real (Ioc 0 t) = _
    rw [IslandThreeTimes.durationLaw_map_root k hc.le hq.le,
      firstExitLaw_real_Ioc _ (islandThreeTree_metzler k hc.le hq.le)
        (islandThreeTree_rows_nonpos k hc.le) 0 ht.1]
    ring
  have hinv := h t ht
  rw [hfirst, hroot] at hinv
  have hpair := island_pair_first_root_survival_identity k c q t
  unfold threeWitness
  rw [hpair]
  nlinarith [hinv]

instance islandDuration_first_nullSingleton (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    NullSingletonClass ((islandDuration k hc hq : Measure (ℝ × ℝ)).map Prod.fst) := by
  change NullSingletonClass ((IslandThreeTimes.durationLaw k c q).map Prod.fst)
  rw [IslandThreeTimes.durationLaw_map_first k hc hq]
  unfold firstExitLaw
  infer_instance

instance islandDuration_root_nullSingleton (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    NullSingletonClass ((islandDuration k hc hq : Measure (ℝ × ℝ)).map
      (fun p => p.1 + p.2)) := by
  change NullSingletonClass ((IslandThreeTimes.durationLaw k c q).map (fun p => p.1 + p.2))
  rw [IslandThreeTimes.durationLaw_map_root k hc.le hq.le]
  unfold firstExitLaw
  infer_instance

end FiniteCountSeparation

theorem island_three_counts_uniform_finite_box (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ rate : ℝ → ℝ,
      LocallyIntegrable rate volume → (∀ t, 0 ≤ rate t) →
      Tendsto (integratedClock rate) atTop atTop →
      ∃ i ≤ K, ∃ j ≤ K,
        ε ≤ |(PanThreeSample.countLaw mutationRate rate).real {(i, j)} -
          (IslandThreeTimes.countLaw k c q mutationRate).real {(i, j)}| := by
  obtain ⟨K, ε, hε, hsep⟩ := FiniteCountSeparation.uniform_count_box_of_pan_invariant
    FiniteCountSeparation.panDuration (FiniteCountSeparation.islandDuration k hc hq)
    (fun rate => PanThreeSample.durationLaw_nonnegative rate.val)
    (IslandThreeTimes.durationLaw_nonnegative k c q)
    FiniteCountSeparation.panDuration_invariant
    (FiniteCountSeparation.islandDuration_not_invariant k hc hq) hmutation
  refine ⟨K, ε, hε, fun rate hr hn htail => ?_⟩
  exact hsep ⟨rate, hr, hn, htail⟩

theorem island_three_counts_uniform_finite_box_halfLine (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ rate : ℝ → ℝ,
      LocallyIntegrableOn rate (Ici 0) volume → (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) →
      Tendsto (integrablePanClock rate) atTop atTop →
      ∃ i ≤ K, ∃ j ≤ K,
        ε ≤ |(PanThreeSample.countLaw mutationRate rate).real {(i, j)} -
          (IslandThreeTimes.countLaw k c q mutationRate).real {(i, j)}| := by
  obtain ⟨K, ε, hε, hsep⟩ := island_three_counts_uniform_finite_box k hc hq hmutation
  refine ⟨K, ε, hε, fun rate hr hn htail => ?_⟩
  rw [PanThreeSample.countLaw_congr_halfLine_ae mutationRate
    (PanThreeSample.representative_eq_ae hn)]
  exact hsep (PanThreeSample.nonnegativeRepresentative rate)
    (PanThreeSample.representative_locallyIntegrable hr)
    (PanThreeSample.representative_nonneg rate)
    (PanThreeSample.representative_clock_diverges hn htail)

theorem island_three_counts_uniform_iid_test (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate) :
    ∃ K : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ S : ℕ, 0 < S →
      (FinitePanelSampling.iidLaw (IslandThreeTimes.countLaw k c q mutationRate) S).real
        (FiniteCountSeparation.acceptTarget
          (fun cell => (IslandThreeTimes.countLaw k c q mutationRate).real {cell}) K S ε)ᶜ ≤
        2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) ∧
      ∀ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume →
        (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) →
        Tendsto (integrablePanClock rate) atTop atTop →
        (FinitePanelSampling.iidLaw (PanThreeSample.countLaw mutationRate rate) S).real
          (FiniteCountSeparation.acceptTarget
            (fun cell => (IslandThreeTimes.countLaw k c q mutationRate).real {cell}) K S ε) ≤
          2 * ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  obtain ⟨K, ε, hε, hsep⟩ :=
    island_three_counts_uniform_finite_box_halfLine k hc hq hmutation
  refine ⟨K, ε, hε, fun S hS => ?_⟩
  let : IsProbabilityMeasure (IslandThreeTimes.countLaw k c q mutationRate) :=
    IslandThreeTimes.countLaw_probability k hc hq hmutation.le
  refine ⟨FiniteCountSeparation.target_error _ K hS hε.le, ?_⟩
  intro rate hr hn htail
  let : IsProbabilityMeasure (PanThreeSample.countLaw mutationRate rate) :=
    PanThreeSample.countLaw_probability_halfLine mutationRate hmutation.le rate hr hn htail
  exact FiniteCountSeparation.competitor_error _ _ K hS hε.le (hsep rate hr hn htail)

end Rhone.Statistics.Identifiability
