/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CTMC
public import Rhone.Statistics.Identifiability.DensityPositive

/-! # Strict diagonal positivity and finite-time survival for finite generators -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset
namespace Rhone.Statistics.Identifiability

theorem exp_diagonal_ge_one {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (i : Fin d) : 1 ≤ NormedSpace.exp A i i := by
  have h := sum_le_hasSum ({0} : Finset Nat)
    (fun n _ => mul_nonneg (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹)
      (Matrix.pow_apply_nonneg hA n i i)) (exp_entry_hasSum A i i)
  simpa using h

theorem exp_generator_diagonal_pos {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) {t : ℝ} (ht : 0 ≤ t) (i : Fin d) :
    0 < NormedSpace.exp (t • Q) i i := by
  let b : ℝ := ∑ j, |Q j j|
  have hdiag : ∀ j, -Q j j ≤ b := by
    intro j
    exact le_trans (neg_le_abs (Q j j))
      (Finset.single_le_sum (fun z _ => abs_nonneg (Q z z)) (Finset.mem_univ j))
  have hA : ∀ j k, 0 ≤ (Q + b • 1) j k := by
    intro j k
    by_cases hjk : j = k
    · subst k
      simpa [add_comm] using (neg_le_iff_add_nonneg.mp (hdiag j))
    · simpa [Matrix.one_apply, hjk] using hQ j k hjk
  have hsplit : t • Q = (-t*b) • 1 + t • (Q + b • 1) := by
    ext j k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((-t*b) • (1 : Matrix (Fin d) (Fin d) ℝ))
      (t • (Q + b • 1)) := (Commute.one_left _).smul_left _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_identity]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
  apply mul_pos (Real.exp_pos _)
  exact lt_of_lt_of_le zero_lt_one
    (exp_diagonal_ge_one _ (fun a b => mul_nonneg ht (hA a b)) i)

theorem finite_survival_pos {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) {t : ℝ} (ht : 0 ≤ t) (i : Fin d) :
    0 < flowOutput Q i (fun _ => 1) 0 t := by
  simp only [flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct, mul_one]
  exact lt_of_lt_of_le (exp_generator_diagonal_pos Q hQ ht i)
    (single_le_sum (fun j _ => exp_generator_nonneg Q hQ ht i j) (mem_univ i))

end Rhone.Statistics.Identifiability
