/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PooledPairPowerIndex.ScanPower

/-! # Finite scan existence and zero-index obstruction -/

@[expose] public section

namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest LinkedAgreementPower
variable {X : Type*} [Fintype X] [Nonempty X]

theorem finite_scan_power_iff (P Q : Law X) :
    (∃ N : ℕ, (19 : ℝ) / 20 ≤ probability (iid (independentPair P Q) N) ScanRejects) ↔
      0 < pooledIndex P Q := by
  constructor
  · rintro ⟨N, hpower⟩
    have ht := pooled_index_nonneg P Q
    by_contra hn
    have hz : pooledIndex P Q = 0 := le_antisymm (le_of_not_gt hn) ht
    have he := (pooled_index_zero_iff P Q).mp hz
    rw [he] at hpower
    have hs := scan_common_size Q N
    linarith
  · intro ht
    obtain ⟨N, hN⟩ := exists_nat_ge (80 * (Fintype.card X : ℝ) ^ 2 / pooledIndex P Q)
    exact ⟨N, scan_source_power P Q N ((div_le_iff₀ ht).mp hN)⟩

omit [Nonempty X] in
theorem zero_index_obstruction (P Q : Law X) (hz : pooledIndex P Q = 0)
    (N : ℕ) (φ : (Fin N → X × X) → ℝ) {α : ℝ}
    (hsize : ∀ R : Law X, rejection (iid (independentPair R R) N) φ ≤ α) :
    rejection (iid (independentPair P Q) N) φ ≤ α := by
  rw [(pooled_index_zero_iff P Q).mp hz]
  exact hsize Q

end Rhone.Statistics.PooledPairPowerIndex
