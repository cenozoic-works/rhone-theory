/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.IslandSampling

/-! # Probability interval bounds for the existing unrelated-pool identity law -/

@[expose] public section
namespace Rhone.Statistics.IslandIdentity

theorem island_step_bounds (N : Nat) (hN : 0 < N) (m F : Real)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 ≤ Rhone.Dynamics.ibdStep (2 * N) m F ∧
      Rhone.Dynamics.ibdStep (2 * N) m F ≤ 1 := by
  have hn : (1 : Real) ≤ (2 * N : Nat) := by exact_mod_cast (by omega : 1 ≤ 2 * N)
  have hnpos : (0 : Real) < (2 * N : Nat) := by linarith
  have ha0 : (0 : Real) ≤ 1 / (2 * N : Nat) := by positivity
  have ha1 : (1 : Real) / (2 * N : Nat) ≤ 1 :=
    (div_le_one hnpos).mpr hn
  have hb0 : 0 ≤ 1 / (2 * N : Nat) + (1 - 1 / (2 * N : Nat)) * F :=
    add_nonneg ha0 (mul_nonneg (by linarith) hF0)
  have hb1 : (1 : Real) / (2 * N : Nat) + (1 - 1 / (2 * N : Nat)) * F ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hF1)]
  have hs1 : (1 - m) ^ 2 ≤ 1 := by nlinarith
  unfold Rhone.Dynamics.ibdStep
  constructor
  · exact mul_nonneg (sq_nonneg _) hb0
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hb0]

theorem island_iterate_bounds (N : Nat) (hN : 0 < N) (m F0 : Real)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hF0 : 0 ≤ F0) (hF1 : F0 ≤ 1) (t : Nat) :
    0 ≤ Rhone.Dynamics.ibdIter (2 * N) m t F0 ∧
      Rhone.Dynamics.ibdIter (2 * N) m t F0 ≤ 1 := by
  induction t with
  | zero => exact ⟨hF0, hF1⟩
  | succ t ih => exact island_step_bounds N hN m _ hm0 hm1 ih.1 ih.2

end Rhone.Statistics.IslandIdentity
