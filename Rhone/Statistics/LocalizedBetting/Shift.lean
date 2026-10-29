/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LocalizedBetting.Moments

/-! # Exact centring identities used to discharge concrete log-moment premises -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.LocalizedBetting
open DependenceBudget DependentPairedTest
open scoped BigOperators
variable {X : Type*} [Fintype X]

theorem increment_mean (P : Law X) (z : X → ℝ) (eta d : ℝ)
    (hz : rejection P z = 0) : rejection P (fun x => eta * (z x + d)) = eta * d := by
  have h : rejection P (fun x => eta * (z x + d)) =
      eta * rejection P z + eta * d * (∑ x, P.mass x) := by
    simp only [rejection, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h, hz, P.total]
  ring

theorem increment_second (P : Law X) (z : X → ℝ) (eta d : ℝ)
    (hz : rejection P z = 0) :
    rejection P (fun x => (eta * (z x + d)) ^ 2) =
      eta ^ 2 * (rejection P (fun x => z x ^ 2) + d ^ 2) := by
  have h : rejection P (fun x => (eta * (z x + d)) ^ 2) =
      eta ^ 2 * rejection P (fun x => z x ^ 2) +
        2 * eta ^ 2 * d * rejection P z + eta ^ 2 * d ^ 2 * (∑ x, P.mass x) := by
    simp only [rejection, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h, hz, P.total]
  ring

end Rhone.Statistics.LocalizedBetting
