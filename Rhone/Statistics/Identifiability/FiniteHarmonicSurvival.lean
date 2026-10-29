/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.WeightedSurvivalPositive
public import Rhone.Statistics.Identifiability.FiniteRowSpaceCertificate

/-! # Proper finite-state survival annihilates every harmonic column -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
variable {n : ℕ}

lemma matrix_exp_mulVec_of_kernel (Q : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : Q *ᵥ w = 0) (t : ℝ) : NormedSpace.exp (t • Q) *ᵥ w = w := by
  funext i
  have hd (s : ℝ) : HasDerivAt (flowOutput Q i w 0) 0 s := by
    have h := flowOutput_hasDerivAt_right Q i w s
    simpa [hw, flowOutput] using h
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [flowOutput] using he

namespace WeightedExit
lemma survival_eq_matrix (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (t : ℝ) :
    survival Q α t = dotProduct α (NormedSpace.exp (t • Q) *ᵥ (fun _ => 1)) := by
  simp only [survival, flowOutput, pow_zero, Matrix.one_mul, dotProduct]

lemma row_nonnegative (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hα : ∀ i, 0 ≤ α i) {t : ℝ} (ht : 0 ≤ t) (j : Fin n) :
    0 ≤ (α ᵥ* NormedSpace.exp (t • Q)) j := by
  change 0 ≤ ∑ i, α i * NormedSpace.exp (t • Q) i j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (exp_generator_nonneg Q hQ ht i j)

lemma row_sum_eq_survival (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ) (t : ℝ) :
    (∑ j, (α ᵥ* NormedSpace.exp (t • Q)) j) = survival Q α t := by
  rw [survival_eq_matrix, dotProduct_mulVec]
  simp [dotProduct]

lemma abs_output_le_survival (Q : Matrix (Fin n) (Fin n) ℝ) (α w : Fin n → ℝ)
    (hQ : IsMetzler Q) (hα : ∀ i, 0 ≤ α i) {t : ℝ} (ht : 0 ≤ t) :
    |dotProduct α (NormedSpace.exp (t • Q) *ᵥ w)| ≤
      (∑ j, |w j|) * survival Q α t := by
  rw [dotProduct_mulVec, ← row_sum_eq_survival]
  unfold dotProduct
  calc
    _ ≤ ∑ j, |(α ᵥ* NormedSpace.exp (t • Q)) j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (α ᵥ* NormedSpace.exp (t • Q)) j * |w j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (row_nonnegative Q α hQ hα ht j)]
    _ ≤ ∑ j, (α ᵥ* NormedSpace.exp (t • Q)) j * (∑ l, |w l|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun l _ => abs_nonneg (w l)) (Finset.mem_univ j))
        (row_nonnegative Q α hQ hα ht j)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

lemma rowSpace_of_survival_tendsto_zero (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hα : ∀ i, 0 ≤ α i)
    (htail : Tendsto (survival Q α) atTop (𝓝 0)) : ∃ β : Fin n → ℝ, β ᵥ* Q = α := by
  apply (finite_rowSpace_iff_annihilates_kernel Q α).mpr
  intro w hw
  have hlim : Tendsto (fun t => (∑ j, |w j|) * survival Q α t) atTop (𝓝 0) := by
    simpa using htail.const_mul (∑ j, |w j|)
  have he : |dotProduct α w| ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [matrix_exp_mulVec_of_kernel Q w hw t] using
      abs_output_le_survival Q α w hQ hα ht
  exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))

end WeightedExit
end Rhone.Statistics.Identifiability
