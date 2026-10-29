/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisher
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Factorial moments for the finite Wright–Fisher spectrum

Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/

@[expose] public section
namespace Rhone.MarkovChain
open Finset
open scoped Matrix

/-- Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/
theorem sum_binomRow_descFactorial (N k : ℕ) (p : ℝ) :
    ∑ j ∈ Finset.range (N + 1), binomRow N p j * (j.descFactorial k : ℝ) =
      (N.descFactorial k : ℝ) * p ^ k := by
  induction N generalizing k with
  | zero =>
    cases k with
    | zero => simp [binomRow]
    | succ k => simp [binomRow]
  | succ N ih =>
    cases k with
    | zero => simpa using sum_binomRow (N + 1) p
    | succ k =>
      have h := sum_binomRow_shift N p (fun j => ((j - 1).descFactorial k : ℝ))
      have hd (j : ℕ) : (j.descFactorial (k + 1) : ℝ) =
          (j : ℝ) * ((j - 1).descFactorial k : ℝ) := by
        cases j with
        | zero => simp
        | succ j => rw [Nat.succ_descFactorial_succ]; push_cast; simp
      simp_rw [← hd] at h
      simp only [Nat.add_sub_cancel] at h
      rw [ih k] at h
      rw [h, Nat.succ_descFactorial_succ]
      push_cast
      ring

/-- Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/
noncomputable def wfFactorialBasisMatrix (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i k => (i.val.descFactorial k.val : ℝ)

/-- Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/
theorem wfFactorialBasisMatrix_det (N : ℕ) :
    Matrix.det (wfFactorialBasisMatrix N) =
      ∏ k : Fin (N + 1), (k.val.factorial : ℝ) := by
  have ht : (wfFactorialBasisMatrix N).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    simp only [wfFactorialBasisMatrix, Nat.descFactorial_eq_zero_iff_lt.mpr hij',
      Nat.cast_zero]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp [wfFactorialBasisMatrix, Nat.descFactorial_self]

/-- Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/
theorem wf_mul_factorialBasis (N : ℕ) (i k : Fin (N + 1)) :
    (Matrix.of (fun i j : Fin (N + 1) => wf N i j) * wfFactorialBasisMatrix N :
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i k =
      (N.descFactorial k.val : ℝ) * ((i.val : ℝ) / N) ^ k.val := by
  change (∑ j : Fin (N + 1), binomRow N ((i.val : ℝ) / N) j.val *
    (j.val.descFactorial k.val : ℝ)) = _
  rw [sum_fin_eq_range (fun j => binomRow N ((i.val : ℝ) / N) j *
    (j.descFactorial k.val : ℝ))]
  exact sum_binomRow_descFactorial N k.val _

/-- Source: feller1951, sec. 8, eq. (8.1), p. 239. -/
noncomputable def wfEigenvalue (N k : ℕ) : ℝ :=
  (N.descFactorial k : ℝ) / (N : ℝ)^k

/-- Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/
noncomputable def wfFactorialOperator (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun j k => (Nat.stirlingSecond k.val j.val : ℝ) * wfEigenvalue N k.val

/-- Source: feller1951, Appendix I, eq. (11.1)–(11.8), p. 244. -/
theorem wf_factorial_intertwining (N : ℕ) :
    Matrix.of (fun i j : Fin (N + 1) => wf N i j) * wfFactorialBasisMatrix N =
      wfFactorialBasisMatrix N * wfFactorialOperator N := by
  ext i k
  rw [wf_mul_factorialBasis, Matrix.mul_apply]
  simp only [wfFactorialBasisMatrix, wfFactorialOperator, wfEigenvalue,
    ← mul_assoc, ← Finset.sum_mul]
  have hp : (∑ j : Fin (N + 1), (i.val.descFactorial j.val : ℝ) *
      (Nat.stirlingSecond k.val j.val : ℝ)) = (i.val : ℝ) ^ k.val := by
    rw [sum_fin_eq_range (fun j => (i.val.descFactorial j : ℝ) *
      (Nat.stirlingSecond k.val j : ℝ))]
    have he : (∑ j ∈ range (N + 1), (i.val.descFactorial j : ℝ) *
        (Nat.stirlingSecond k.val j : ℝ)) =
        ∑ j ∈ range (k.val + 1), (i.val.descFactorial j : ℝ) *
          (Nat.stirlingSecond k.val j : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ k.is_le))
      intro j hj hjk
      have hk : k.val < j := by simp only [mem_range] at hjk; omega
      simp [Nat.stirlingSecond_eq_zero_of_lt hk]
    rw [he]
    have h := Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i.val k.val
    have h' : (i.val : ℝ) ^ k.val =
        ∑ j ∈ range (k.val + 1), (Nat.stirlingSecond k.val j : ℝ) *
          (i.val.descFactorial j : ℝ) := by exact_mod_cast h
    simpa only [mul_comm] using h'.symm
  rw [hp, div_pow]
  ring

/-- Source: feller1951, sec. 8, eq. (8.1), p. 239; feller1951, Appendix I, p. 244. -/
theorem wf_charpoly (N : ℕ) :
  Matrix.charpoly (wf N) =
    ∏ k : Fin (N + 1), (Polynomial.X - Polynomial.C (wfEigenvalue N k)) := by
  let F := wfFactorialBasisMatrix N
  let B := wfFactorialOperator N
  let P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.of (fun i j => wf N i j)
  have hdet : F.det ≠ 0 := by
    rw [wfFactorialBasisMatrix_det]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact_mod_cast Nat.factorial_ne_zero k.val
  have hu : IsUnit F.det := isUnit_iff_ne_zero.mpr hdet
  have hPF : P * F = F * B := wf_factorial_intertwining N
  have hP : P = (F * B) * F⁻¹ := by
    rw [← hPF, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  have hchar : P.charpoly = B.charpoly := by
    rw [hP, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have htri : B.IsUpperTriangular := by
    intro i j hij
    have hij' : j.val < i.val := hij
    simp [B, wfFactorialOperator, Nat.stirlingSecond_eq_zero_of_lt hij']
  change P.charpoly = _
  rw [hchar, Matrix.charpoly_of_isUpperTriangular _ htri]
  simp [B, wfFactorialOperator, Nat.stirlingSecond_self]

end Rhone.MarkovChain
