/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Symmetry

/-! # Finite-sample self-normalized size proof for sign-symmetric contrasts -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

theorem symmetric_ratio_expectation (P : Law X) (N : ℕ) (e : X ≃ X) (f : X → ℝ)
    (hP : ∀ x, P.mass (e x) = P.mass x) (hf : ∀ x, f (e x) = -f x) :
    rejection (iid P N) (fun x => (sumStatistic (fun i => f (x i))) ^ 2 /
      squareStatistic (fun i => f (x i))) =
    rejection (iid P N) (fun x => squareStatistic (fun i => f (x i)) /
      squareStatistic (fun i => f (x i))) := by
  have hx : ∀ x : Fin N → X,
      (sumStatistic (fun i => f (x i))) ^ 2 / squareStatistic (fun i => f (x i)) =
      ∑ i, ∑ j, f (x i) * f (x j) / squareStatistic (fun i => f (x i)) := by
    intro x
    unfold sumStatistic
    rw [pow_two, Finset.sum_mul_sum]
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp_rw [hx, expectation_sum]
  have hc : ∀ i j : Fin N,
      rejection (iid P N) (fun x => f (x i) * f (x j) /
        squareStatistic (fun k => f (x k))) =
      if i = j then rejection (iid P N) (fun x => (f (x i)) ^ 2 /
        squareStatistic (fun k => f (x k))) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [pow_two]
    · simp only [ite_eq_right hij]
      exact cross_ratio_zero P N e f hP hf i j hij
  simp_rw [hc]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← expectation_sum]
  congr 1
  funext x
  simp only [squareStatistic, div_eq_mul_inv, Finset.sum_mul]

theorem symmetric_null_size (P : Law X) (N : ℕ) (e : X ≃ X) (f : X → ℝ)
    (hP : ∀ x, P.mass (e x) = P.mass x) (hf : ∀ x, f (e x) = -f x) :
    probability (iid P N) (fun x => Rejects (fun i => f (x i))) ≤ (1 : ℝ) / 20 := by
  let R : (Fin N → X) → ℝ := fun x =>
    (sumStatistic (fun i => f (x i))) ^ 2 / squareStatistic (fun i => f (x i))
  have hR : ∀ x, 0 ≤ R x := by
    intro x
    exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hmean : rejection (iid P N) R ≤ 1 := by
    rw [show R = _ from rfl, symmetric_ratio_expectation P N e f hP hf, ← (iid P N).total]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_of_le_one_right ((iid P N).nonneg x)
    exact div_self_le_one _
  have hsub : ∀ x, Rejects (fun i => f (x i)) → 20 ≤ R x := by
    intro x hx
    exact (le_div_iff₀ hx.1).mpr hx.2
  exact (probability_mono (iid P N) hsub).trans
    ((finite_markov (iid P N) R hR (by norm_num : (0 : ℝ) < 20)).trans
      (div_le_div_of_nonneg_right hmean (by norm_num)))

end Rhone.Statistics.DependentPairedTest
