/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.GeneralPairTimePower.Classification
public import Rhone.Statistics.PooledPairPowerIndex.ScanPower
public import Rhone.Statistics.PooledPairPowerIndex.Necessary

/-! # Pair-time power and proper-pan pooled necessary bound -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.GeneralPairTimePower
open DependenceBudget PairObservationChannel DependentPairedTest
open LinkedAgreementPower PooledPairPowerIndex
variable {K : ℕ} {H : Type*} [Fintype H]

theorem index_positive_iff (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    0 < pooledIndex (observedLaw E μ hk hμ) (observedLaw E ν hk hν) ↔
      pairLaplace μ k ≠ pairLaplace ν k ∧ Informative E := by
  rw [lt_iff_le_and_ne]
  simp only [pooled_index_nonneg, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    pooled_index_zero_iff]
  exact reported_pair_ne_iff E μ ν hk hμ hν

theorem scan_power [Nonempty H] (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (N : ℕ)
    (hbudget : 80 * (Fintype.card (H × H) : ℝ) ^ 2 ≤
      N * pooledIndex (observedLaw E μ hk hμ) (observedLaw E ν hk hν)) :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair
      (observedLaw E μ hk hμ) (observedLaw E ν hk hν)) N) ScanRejects :=
  scan_source_power _ _ N hbudget

theorem pan_scan_size [Nonempty H] (E : Channel K H)
    (r : ℝ → ℝ) (hr : AdmittedPan r) {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) :
    probability (iid (independentPair (panObservedLaw E r hr hκ)
      (panObservedLaw E r hr hκ)) N) ScanRejects ≤ (1 : ℝ) / 20 :=
  scan_common_size _ N

theorem uniform_pan_general_necessary_bound (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 < t) (hν : ∀ᵐ t ∂ν, 0 < t) (N : ℕ)
    (φ : (Fin N → (H × H) × (H × H)) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α β : ℝ} (hab : α + β ≤ 1)
    (hsize : ∀ r : ℝ → ℝ, ∀ hr : AdmittedPan r, ∀ κ : ℝ, ∀ hκ : 0 < κ,
      rejection (iid (independentPair (panObservedLaw E r hr hκ.le)
        (panObservedLaw E r hr hκ.le)) N) φ ≤ α)
    (hpower : 1 - β ≤ rejection (iid (independentPair
      (observedLaw E μ hk.le (hμ.mono fun _ h => h.le))
      (observedLaw E ν hk.le (hν.mono fun _ h => h.le))) N) φ) :
    (1 - α - β) ^ 2 / (2 * pooledIndex
      (observedLaw E μ hk.le (hμ.mono fun _ h => h.le))
      (observedLaw E ν hk.le (hν.mono fun _ h => h.le))) ≤ (N : ℝ) := by
  apply pooled_necessary_bound _ _ N φ hφ (by linarith)
  have hs := hsize (fun _ => matchingRate k (pooledLaplace μ ν k))
    (constant_pan_admitted (matching_rate_pos hk (pooled_laplace_interval μ ν hk hμ hν))) k hk
  rw [pooled_reported_law E μ ν hk hμ hν] at hs
  linarith

theorem uniform_pan_necessary_bound (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 < t) (hν : ∀ᵐ t ∂ν, 0 < t) (N : ℕ)
    (φ : (Fin N → (H × H) × (H × H)) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsize : ∀ r : ℝ → ℝ, ∀ hr : AdmittedPan r, ∀ κ : ℝ, ∀ hκ : 0 < κ,
      rejection (iid (independentPair (panObservedLaw E r hr hκ.le)
        (panObservedLaw E r hr hκ.le)) N) φ ≤ (1 : ℝ) / 20)
    (hpower : (19 : ℝ) / 20 ≤ rejection (iid (independentPair
      (observedLaw E μ hk.le (hμ.mono fun _ h => h.le))
      (observedLaw E ν hk.le (hν.mono fun _ h => h.le))) N) φ) :
    (81 : ℝ) / 100 / (2 * pooledIndex
      (observedLaw E μ hk.le (hμ.mono fun _ h => h.le))
      (observedLaw E ν hk.le (hν.mono fun _ h => h.le))) ≤ (N : ℝ) := by
  apply necessary_ninety_five_five _ _ N φ hφ _ hpower
  have hs := hsize (fun _ => matchingRate k (pooledLaplace μ ν k))
    (constant_pan_admitted (matching_rate_pos hk (pooled_laplace_interval μ ν hk hμ hν))) k hk
  rw [pooled_reported_law E μ ν hk hμ hν] at hs
  exact hs

end Rhone.Statistics.GeneralPairTimePower
