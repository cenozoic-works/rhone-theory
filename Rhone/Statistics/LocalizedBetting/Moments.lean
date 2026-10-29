/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LocalizedBetting.LogBounds
public import Rhone.Statistics.LocalizedBetting.FiniteNull
public import Rhone.Statistics.LocalizedBetting.Score

/-! # Finite-law expectation bridge for the source-centred score and log increments -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.LocalizedBetting
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

theorem contrast_expectation (P : Law X) (s : Fin 5 → ℝ) (f : Fin 5 → X → ℝ) :
    rejection P (fun x => contrast s (fun i => f i x)) =
      contrast s (fun i => rejection P (f i)) := by
  unfold contrast
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rejection, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have he : (∑ x, P.mass x * (gradient s i * f i x)) =
      gradient s i * ∑ x, P.mass x * f i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he, P.total]
  ring

theorem log_mean_lower (P : Law X) (increment : X → ℝ)
    (hb : ∀ x, |increment x| ≤ 1 / 100) :
    rejection P increment - 511 / 1000 * rejection P (fun x => increment x ^ 2) ≤
      rejection P (fun x => Real.log (1 + increment x)) := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (log_lower (hb x)) (P.nonneg x))
  have he : (∑ x, P.mass x * (increment x - 511 / 1000 * increment x ^ 2)) =
      rejection P increment - 511 / 1000 * rejection P (fun x => increment x ^ 2) := by
    simp only [rejection, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he] at h
  exact h

theorem log_second_bound (P : Law X) (increment : X → ℝ)
    (hb : ∀ x, |increment x| ≤ 1 / 100) :
    rejection P (fun x => Real.log (1 + increment x) ^ 2) ≤
      1021 / 1000 * rejection P (fun x => increment x ^ 2) := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (log_second_upper (hb x)) (P.nonneg x))
  have he : (∑ x, P.mass x * (1021 / 1000 * increment x ^ 2)) =
      1021 / 1000 * rejection P (fun x => increment x ^ 2) := by
    simp only [rejection, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he] at h
  exact h

end Rhone.Statistics.LocalizedBetting
