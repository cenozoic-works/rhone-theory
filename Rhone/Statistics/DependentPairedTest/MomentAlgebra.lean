/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProduct

/-! # Finite-experiment moment identities for the fixed-N power proof -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

theorem expectation_sum {ι : Type*} [Fintype ι] (P : Law X) (f : ι → X → ℝ) :
    rejection P (fun x => ∑ i, f i x) = ∑ i, rejection P (f i) := by
  simp only [rejection, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectation_const (P : Law X) (c : ℝ) : rejection P (fun _ => c) = c := by
  simp [rejection, ← Finset.sum_mul, P.total]

theorem expectation_centered (P : Law X) (f : X → ℝ) :
    rejection P (fun x => f x - rejection P f) = 0 := by
  simp [rejection, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P.total]

theorem expectation_centered_sq (P : Law X) (f : X → ℝ) :
    rejection P (fun x => (f x - rejection P f)^2) =
      rejection P (fun x => (f x)^2) - (rejection P f)^2 := by
  have heq : ∀ x, P.mass x * (f x - rejection P f)^2 =
      P.mass x * (f x)^2 - 2 * rejection P f * (P.mass x * f x) +
        P.mass x * (rejection P f)^2 := by intro x; ring1
  unfold rejection at *
  simp_rw [heq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, P.total]
  ring1

theorem iid_centered_sq (P : Law X) (N : ℕ) (f : X → ℝ) :
    rejection (iid P N) (fun x => ((∑ i, f (x i)) - N * rejection P f)^2) =
      N * (rejection P (fun x => (f x)^2) - (rejection P f)^2) := by
  let g : X → ℝ := fun x => f x - rejection P f
  have hg : rejection P g = 0 := expectation_centered P f
  have hsum : ∀ x : Fin N → X,
      (∑ i, f (x i)) - N * rejection P f = ∑ i, g (x i) := by
    intro x
    simp [g, Finset.sum_sub_distrib]
  have hcross : ∀ i j : Fin N,
      rejection (iid P N) (fun x => g (x i) * g (x j)) =
        if i = j then rejection P (fun x => (g x)^2) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using expectation_coordinate P N (fun x => g x * g x) i
    · simp only [ite_eq_right hij]
      rw [expectation_two_coordinates P N g g i j hij, hg, zero_mul]
  simp_rw [hsum, pow_two, Finset.sum_mul_sum]
  rw [expectation_sum]
  simp_rw [expectation_sum]
  simp_rw [hcross]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show rejection P (fun x => (g x)^2) =
    rejection P (fun x => (f x)^2) - (rejection P f)^2 from expectation_centered_sq P f]
  simp only [pow_two]

end Rhone.Statistics.DependentPairedTest
