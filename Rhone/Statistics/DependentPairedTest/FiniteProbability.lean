/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.MomentAlgebra

/-! # Finite whole-data probability and second-moment bounds for fixed tests -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

noncomputable def probability (P : Law X) (A : X → Prop) : ℝ := by
  classical
  exact ∑ x, if A x then P.mass x else 0

theorem probability_mono (P : Law X) {A B : X → Prop} (h : ∀ x, A x → B x) :
    probability P A ≤ probability P B := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hA : A x
  · simp only [ite_eq_left hA, ite_eq_left (h x hA)]
    exact le_rfl
  · simp only [ite_eq_right hA]
    split_ifs <;> first | exact P.nonneg x | exact le_rfl

theorem probability_complement (P : Law X) (A : X → Prop) :
    probability P (fun x => ¬ A x) = 1 - probability P A := by
  classical
  have h : probability P A + probability P (fun x => ¬ A x) = 1 := by
    unfold probability
    rw [← Finset.sum_add_distrib, ← P.total]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : A x <;> simp [hx]
  linarith

theorem probability_union_le (P : Law X) (A B : X → Prop) :
    probability P (fun x => A x ∨ B x) ≤ probability P A + probability P B := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb, P.nonneg x]

theorem finite_markov (P : Law X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : 0 < t) : probability P (fun x => t ≤ f x) ≤ rejection P f / t := by
  classical
  apply (le_div_iff₀ ht).mpr
  unfold probability rejection
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t ≤ f x
  · simp only [ite_eq_left hx]
    exact mul_le_mul_of_nonneg_left hx (P.nonneg x)
  · simp only [ite_eq_right hx, zero_mul]
    exact mul_nonneg (P.nonneg x) (hf x)

theorem finite_chebyshev (P : Law X) (f : X → ℝ) (c : ℝ)
    {t : ℝ} (ht : 0 < t) :
    probability P (fun x => t ≤ |f x - c|) ≤
      rejection P (fun x => (f x - c)^2) / t^2 := by
  have hsub : ∀ x, t ≤ |f x - c| → t^2 ≤ (f x - c)^2 := by
    intro x hx
    have h := (sq_le_sq₀ ht.le (abs_nonneg (f x - c))).mpr hx
    simpa only [sq_abs] using h
  exact (probability_mono P hsub).trans
    (finite_markov P (fun x => (f x - c)^2) (fun _ => sq_nonneg _)
      (sq_pos_of_pos ht))

end Rhone.Statistics.DependentPairedTest
