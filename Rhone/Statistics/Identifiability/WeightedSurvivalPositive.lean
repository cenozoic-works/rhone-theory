/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteExitMassBound
public import Rhone.Statistics.Identifiability.ThreeNoMigrationDensity

/-! # Every normalized nonnegative finite initial row has positive finite-time survival -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.WeightedExit
variable {n : ℕ}

lemma survival_nonnegative (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hα : ∀ i, 0 ≤ α i) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ survival Q α t :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (survival_nonneg Q hQ i ht)

lemma survival_positive (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    {t : ℝ} (ht : 0 ≤ t) : 0 < survival Q α t := by
  have hsum : 0 < ∑ i, α i := by rw [hαsum]; norm_num
  have hex : ∃ i, 0 < α i := by
    by_contra hn
    push Not at hn
    have hle := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hn i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have he := ThreeNoMigration.exponential_diagonal_lower_bound Q hQ ht i
  have hrow : NormedSpace.exp (t • Q) i i ≤ flowOutput Q i (fun _ => 1) 0 t := by
    simp only [flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct, mul_one]
    exact Finset.single_le_sum (fun j _ => exp_generator_nonneg Q hQ ht i j) (Finset.mem_univ i)
  have hp := (Real.exp_pos (t * Q i i)).trans_le (he.trans hrow)
  exact (mul_pos hi hp).trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (hα j) (survival_nonneg Q hQ j ht)) (Finset.mem_univ i))

end Rhone.Statistics.Identifiability.WeightedExit
