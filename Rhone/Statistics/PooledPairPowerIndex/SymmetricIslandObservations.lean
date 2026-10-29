/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.GeneralPairTimePower.Power
public import Rhone.Statistics.SpatialPairDesign.Observation

/-! # Pooled-index endpoints for symmetric-island observations -/

@[expose] public section

namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest LinkedAgreementPower
open PairObservationChannel SpatialPairDesign GeneralPairTimePower
variable {K : ℕ} {H : Type*} [Fintype H]

theorem island_index_positive_iff (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) :
    0 < pooledIndex (sourceLaw E n hc hq hk.le 0) (sourceLaw E n hc hq hk.le 1) ↔
      Informative E := by
  rw [lt_iff_le_and_ne]
  simp only [pooled_index_nonneg, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    pooled_index_zero_iff]
  exact source_separated_iff E n hc hq hk

theorem island_scan_power [Nonempty H] (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) (N : ℕ)
    (hbudget : 80 * (Fintype.card (H × H) : ℝ) ^ 2 ≤
      N * pooledIndex (sourceLaw E n hc hq hk 0) (sourceLaw E n hc hq hk 1)) :
    (19 : ℝ) / 20 ≤ probability (iid (independentPair
      (sourceLaw E n hc hq hk 0) (sourceLaw E n hc hq hk 1)) N) ScanRejects :=
  scan_source_power _ _ N hbudget

theorem island_necessary_bound (E : Channel K H) (n : ℕ) {c q k : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) (N : ℕ)
    (φ : (Fin N → (H × H) × (H × H)) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsize : ∀ r : ℝ → ℝ, ∀ hr : AdmittedPan r, ∀ κ : ℝ, ∀ hκ : 0 < κ,
      rejection (iid (independentPair (panObservedLaw E r hr hκ.le)
        (panObservedLaw E r hr hκ.le)) N) φ ≤ (1 : ℝ) / 20)
    (hpower : (19 : ℝ) / 20 ≤ rejection (iid (independentPair
      (sourceLaw E n hc hq hk.le 0) (sourceLaw E n hc hq hk.le 1)) N) φ) :
    (81 : ℝ) / 100 / (2 * pooledIndex
      (sourceLaw E n hc hq hk.le 0) (sourceLaw E n hc hq hk.le 1)) ≤ (N : ℝ) := by
  let := pair_law_probability n hc hq (0 : Fin 2)
  let := pair_law_probability n hc hq (1 : Fin 2)
  exact uniform_pan_necessary_bound E _ _ hk
    (pair_law_positive_support n c q 0) (pair_law_positive_support n c q 1) N φ hφ hsize hpower

end Rhone.Statistics.PooledPairPowerIndex
