/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.InfiniteCriterion
public import Rhone.Statistics.PooledPairPowerIndex.Classification

/-! # Source-specific finite linked-panel category-scan testing -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.LinkedPairMoments
open PairObservationChannel DependenceBudget DependentPairedTest
open LinkedAgreementPower PooledPairPowerIndex
variable {K : ℕ} {H : Type*} [Fintype H] [Nonempty H]

theorem panel_scan_power (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L N : ℕ)
    (hbudget : 80 * (Fintype.card (Fin L → H × H) : ℝ) ^ 2 ≤
      N * pooledIndex (panelLaw E μ hk hμ L) (panelLaw E ν hk hν L)) :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair
      (panelLaw E μ hk hμ L) (panelLaw E ν hk hν L)) N) ScanRejects :=
  scan_source_power _ _ N hbudget

theorem some_panel_test_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∃ L N : ℕ,
      (19 : ℝ) / 20 ≤ probability (iid (independentPair
        (panelLaw E μ hk.le hμ L) (panelLaw E ν hk.le hν L)) N) ScanRejects ∧
      ∀ R : Law (Fin L → H × H),
        probability (iid (independentPair R R) N) ScanRejects ≤ (1 : ℝ) / 20) ↔
      μ ≠ ν := by
  rw [← some_panel_separates_iff E hE μ ν hk hμ hν]
  constructor
  · rintro ⟨L, N, hp, hs⟩
    refine ⟨L, ?_⟩
    intro he
    rw [he] at hp
    have hh := hs (panelLaw E ν hk.le hν L)
    linarith
  · rintro ⟨L, hne⟩
    have ht : 0 < pooledIndex (panelLaw E μ hk.le hμ L) (panelLaw E ν hk.le hν L) := by
      apply lt_of_le_of_ne (pooled_index_nonneg _ _)
      intro he
      exact hne ((pooled_index_zero_iff _ _).mp he.symm)
    obtain ⟨N, hp⟩ := (finite_scan_power_iff _ _).mpr ht
    exact ⟨L, N, hp, fun R => scan_common_size R N⟩

end Rhone.Statistics.LinkedPairMoments
