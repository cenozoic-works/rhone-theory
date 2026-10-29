/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisherMultialleleMoments
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Subset counts of the multinomial Wright–Fisher chain

Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1. -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset Polynomial

/-- Source: ewens2004, sec. 3.5. -/
private theorem linear_power_coeff (p q : ℝ) (N j : ℕ) :
    ((C p * X + C q : Polynomial ℝ) ^ N).coeff j =
      (N.choose j : ℝ) * p ^ j * q ^ (N - j) := by
  have h : ((X + C q : Polynomial ℝ) ^ N).comp (C p * X) =
      (C p * X + C q) ^ N := by simp
  rw [← h, comp_C_mul_X_coeff, coeff_X_add_C_pow]
  ring

/-- Source: ewens2004, sec. 3.5. -/
private theorem colour_polynomial (K : ℕ) (p : Fin K → ℝ) (S : Finset (Fin K)) :
    (∑ l : Fin K, C (p l) * (X : Polynomial ℝ) ^ (if l ∈ S then 1 else 0)) =
      C (∑ l ∈ S, p l) * X + C (∑ l ∈ Sᶜ, p l) := by
  classical
  have ht (l : Fin K) :
      C (p l) * (X : Polynomial ℝ) ^ (if l ∈ S then 1 else 0) =
        if l ∈ S then C (p l) * X else C (p l) := by
    by_cases hl : l ∈ S <;> simp [hl]
  simp_rw [ht]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff]
  rw [← Finset.sum_mul, ← map_sum, ← map_sum]

/-- Source: cannings1974, sec. 3.1. -/
private theorem subset_coeff (N K : ℕ) (a : AlleleCounts N K)
    (S : Finset (Fin K)) (j : ℕ) :
    ((∑ l : Fin K, C ((a.val l : ℝ) / N) *
      (X : Polynomial ℝ) ^ (if l ∈ S then 1 else 0)) ^ N).coeff j =
      ∑ b : AlleleCounts N K,
        if (∑ l ∈ S, b.val l) = j then wfMultiallele N K a b else 0 := by
  classical
  have hterm (b : AlleleCounts N K) :
      (Nat.multinomial (Finset.univ : Finset (Fin K)) b.val : Polynomial ℝ) *
        (∏ l : Fin K, (C ((a.val l : ℝ) / N) *
          X ^ (if l ∈ S then 1 else 0)) ^ b.val l) =
      C (wfMultiallele N K a b) * X ^ (∑ l ∈ S, b.val l) := by
    have he : (∑ l : Fin K, (if l ∈ S then 1 else 0) * b.val l) =
        ∑ l ∈ S, b.val l := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp
    simp_rw [mul_pow, ← C_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
    rw [← map_natCast (C : ℝ →+* Polynomial ℝ), ← mul_assoc, ← C_mul, he]
    rfl
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin K))
    (fun l => C ((a.val l : ℝ) / N) *
      (X : Polynomial ℝ) ^ (if l ∈ S then 1 else 0)) N
  rw [← Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin K)) N)] at h
  simp_rw [hterm] at h
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff j) h
  rw [Polynomial.finsetSum_coeff] at hc
  simpa only [coeff_C_mul_X_pow, eq_comm] using hc

/-- Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfMultiallele_subset_count (N K : ℕ) (a : AlleleCounts N K)
    (S : Finset (Fin K)) (j : ℕ) :
    (∑ b : AlleleCounts N K,
      if (∑ l ∈ S, b.val l) = j then wfMultiallele N K a b else 0) =
      binomRow N ((∑ l ∈ S, (a.val l : ℝ)) / N) j := by
  classical
  rw [← subset_coeff]
  by_cases hN : N = 0
  · cases j <;> simp [hN, binomRow, Polynomial.coeff_one]
  let p : Fin K → ℝ := fun l => (a.val l : ℝ) / N
  have hp : (∑ l : Fin K, p l) = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, a.sum_real, div_self (Nat.cast_ne_zero.mpr hN)]
  have hcompl : (∑ l ∈ Sᶜ, p l) = 1 - ∑ l ∈ S, p l := by
    have h := Finset.sum_add_sum_compl S p
    rw [hp] at h
    linarith
  have hs : (∑ l ∈ S, p l) = (∑ l ∈ S, (a.val l : ℝ)) / N := by
    dsimp [p]
    rw [← Finset.sum_div]
  change ((∑ l : Fin K, C (p l) *
    (X : Polynomial ℝ) ^ (if l ∈ S then 1 else 0)) ^ N).coeff j = _
  rw [colour_polynomial, hcompl, linear_power_coeff, ← hs]
  rfl

end Rhone.MarkovChain
