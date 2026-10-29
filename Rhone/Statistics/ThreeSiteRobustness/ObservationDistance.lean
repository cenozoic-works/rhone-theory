/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.ScoreLipschitz
public import Rhone.Statistics.DependenceBudget.Transfer

/-! # Finite-law TV stability of the three-site test -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteRobustness
open DependenceBudget
variable {X : Type*} [Fintype X]

theorem bounded_mean (P : Law X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |rejection P f| ≤ 1 := by
  unfold rejection
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [← P.total]
  apply Finset.sum_le_sum
  intro x _
  rw [abs_mul, abs_of_nonneg (P.nonneg x)]
  simpa using mul_le_mul_of_nonneg_left (hf x) (P.nonneg x)

theorem bounded_mean_difference (P Q : Law X) (f : X → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |rejection P f - rejection Q f| ≤ 2 * totalVariation P Q := by
  unfold rejection
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    |∑ x, (P.mass x - Q.mass x) * f x| ≤
        ∑ x, |(P.mass x - Q.mass x) * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |P.mass x - Q.mass x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (hf x) (abs_nonneg (P.mass x - Q.mass x))
    _ = 2 * totalVariation P Q := by unfold totalVariation; ring

theorem score_tv_bound (P Q : Law X) (f : Fin 5 → X → ℝ)
    (hf : ∀ i x, |f i x| ≤ 1) :
    |scoreVector (fun i => rejection P (f i)) -
      scoreVector (fun i => rejection Q (f i))| ≤ 1467240 * totalVariation P Q := by
  have h := score_lipschitz (fun i => bounded_mean P (f i) (hf i))
    (fun i => bounded_mean Q (f i) (hf i))
    (fun i => bounded_mean_difference P Q (f i) (hf i))
  linarith

theorem positive_score_tv_margin (P Q : Law X) (f : Fin 5 → X → ℝ)
    (hf : ∀ i x, |f i x| ≤ 1) {g : ℝ}
    (hsource : scoreVector (fun i => rejection P (f i)) = g)
    (hnull : scoreVector (fun i => rejection Q (f i)) ≤ 0) :
    g / 1467240 ≤ totalVariation P Q := by
  have h := (abs_le.mp (score_tv_bound P Q f hf)).2
  rw [hsource] at h
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1467240)).mpr
  linarith

end Rhone.Statistics.ThreeSiteRobustness
