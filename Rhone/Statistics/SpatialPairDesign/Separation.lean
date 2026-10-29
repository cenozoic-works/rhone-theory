/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SpatialPairDesign.Observation

/-! # Known-stratum obstruction to any one common observed pair law -/

@[expose] public section

namespace Rhone.Statistics.SpatialPairDesign
open DependenceBudget PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

theorem no_common_observed_law (E : Channel K H) (hE : Informative E) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) (P : Law (H × H)) :
    ¬ (sourceLaw E n hc hq hk.le 0 = P ∧ sourceLaw E n hc hq hk.le 1 = P) := by
  rintro ⟨h0, h1⟩
  exact ((source_separated_iff E n hc hq hk).mpr hE) (h0.trans h1.symm)

theorem clean_no_common_observed_law (hK : 2 ≤ K) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) (P : Law (Fin K × Fin K)) :
    ¬ (sourceLaw (identityChannel K (by omega)) n hc hq hk.le 0 = P ∧
      sourceLaw (identityChannel K (by omega)) n hc hq hk.le 1 = P) := by
  apply no_common_observed_law (identityChannel K (by omega)) _ n hc hq hk P
  apply (retained_variance_pos_iff _).mp
  rw [identity_variance]
  have hKr : (1 : ℝ) < K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hdiv : (1 : ℝ) / K < 1 := (div_lt_one hKpos).mpr hKr
  linarith

end Rhone.Statistics.SpatialPairDesign
