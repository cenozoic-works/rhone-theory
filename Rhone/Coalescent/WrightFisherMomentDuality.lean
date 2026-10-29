/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Duality
public import Rhone.MarkovChain.CoreBridge
public import Rhone.MarkovChain.WrightFisherSpectrum

/-! # Moment duality for the haploid Wright–Fisher chain -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Matrix MarkovChain

theorem sum_stirlingSecond_descFactorial (x n : ℕ) :
    ∑ m ∈ range (n + 1), Nat.stirlingSecond n m * x.descFactorial m = x ^ n :=
  (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial x n).symm

theorem sum_stirlingSecond_descFactorial_cast (x n : ℕ) :
    ∑ m ∈ range (n + 1), (Nat.stirlingSecond n m : ℝ) * (x.descFactorial m : ℝ) =
      (x : ℝ) ^ n := by
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_stirlingSecond_descFactorial x n)

theorem sum_fin_stirlingSecond_mul (N : ℕ) (n : Fin (N + 1)) (f : ℕ → ℝ) :
    ∑ m : Fin (N + 1), (Nat.stirlingSecond n m : ℝ) * f m =
      ∑ m ∈ range ((n : ℕ) + 1), (Nat.stirlingSecond n m : ℝ) * f m := by
  rw [Fin.sum_univ_eq_sum_range (fun m => (Nat.stirlingSecond n m : ℝ) * f m) (N + 1)]
  refine (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Fin.is_le n)))
    fun m _ hm => ?_).symm
  have hlt : (n : ℕ) < m := by
    rw [mem_range] at hm
    omega
  rw [Nat.stirlingSecond_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]

theorem natCast_pow_fin_ne_zero (N : ℕ) (n : Fin (N + 1)) : (N : ℝ) ^ (n : ℕ) ≠ 0 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · have hn : (n : ℕ) = 0 := by
      have := Fin.is_le n
      omega
    rw [hn, pow_zero]
    exact one_ne_zero
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr h.ne')

noncomputable def wfAncestralChain (N : ℕ) : FinChain (Fin (N + 1)) where
  P := fun n m =>
    (Nat.stirlingSecond n m : ℝ) * (N.descFactorial m : ℝ) / (N : ℝ) ^ (n : ℕ)
  nonneg _ _ :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  row_sum n := by
    change ∑ m : Fin (N + 1),
      (Nat.stirlingSecond n m : ℝ) * (N.descFactorial m : ℝ) / (N : ℝ) ^ (n : ℕ) = 1
    rw [← Finset.sum_div, sum_fin_stirlingSecond_mul N n (fun m => (N.descFactorial m : ℝ)),
      sum_stirlingSecond_descFactorial_cast]
    exact div_self (natCast_pow_fin_ne_zero N n)

noncomputable def powerDual (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i n => ((i : ℝ) / N) ^ (n : ℕ)

theorem wfAncestralChain_apply (N : ℕ) (n m : Fin (N + 1)) :
    (wfAncestralChain N).P n m =
      (Nat.stirlingSecond n m : ℝ) * (N.descFactorial m : ℝ) / (N : ℝ) ^ (n : ℕ) :=
  rfl

theorem sum_binomRow_mul_div_pow (N n : ℕ) (p : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N) ^ n =
      (∑ m ∈ range (n + 1),
        (Nat.stirlingSecond n m : ℝ) * ((N.descFactorial m : ℝ) * p ^ m)) / (N : ℝ) ^ n := by
  have h : ∀ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N) ^ n =
      ∑ m ∈ range (n + 1), (Nat.stirlingSecond n m : ℝ) *
        (binomRow N p j * (j.descFactorial m : ℝ)) / (N : ℝ) ^ n := by
    intro j _
    rw [div_pow, ← sum_stirlingSecond_descFactorial_cast j n, ← Finset.sum_div,
      ← mul_div_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  have h2 : ∀ m ∈ range (n + 1), ∑ j ∈ range (N + 1), (Nat.stirlingSecond n m : ℝ) *
      (binomRow N p j * (j.descFactorial m : ℝ)) / (N : ℝ) ^ n =
      (Nat.stirlingSecond n m : ℝ) * ((N.descFactorial m : ℝ) * p ^ m) / (N : ℝ) ^ n := by
    intro m _
    rw [← Finset.sum_div, ← Finset.mul_sum, sum_binomRow_descFactorial]
  rw [Finset.sum_congr rfl h, Finset.sum_comm, Finset.sum_congr rfl h2, Finset.sum_div]

/-- Source: mohle1999, Prop. 3.5, eq. (11), p. 771. -/
theorem wf_blockCount_duality (N : ℕ) :
    FinChain.MomentDuality (wfChain N) (wfAncestralChain N) (powerDual N) := by
  refine FinChain.MomentDuality.of_step ?_
  ext i n
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ j, (wfChain N).P i j * powerDual N j n = _ :=
    (Fin.sum_univ_eq_sum_range
      (fun j => binomRow N (((i : ℕ) : ℝ) / N) j * ((j : ℝ) / N) ^ (n : ℕ)) (N + 1)).trans
      (sum_binomRow_mul_div_pow N n _)
  have hR : ∑ m, powerDual N i m * (wfAncestralChain N).Pᵀ m n =
      ∑ m ∈ range ((n : ℕ) + 1), (Nat.stirlingSecond n m : ℝ) *
        ((N.descFactorial m : ℝ) * (((i : ℕ) : ℝ) / N) ^ m / (N : ℝ) ^ (n : ℕ)) :=
    (Finset.sum_congr rfl fun m _ => by
      change (((i : ℕ) : ℝ) / N) ^ (m : ℕ) *
        ((Nat.stirlingSecond n m : ℝ) * (N.descFactorial m : ℝ) / (N : ℝ) ^ (n : ℕ)) =
        (Nat.stirlingSecond n m : ℝ) *
          ((N.descFactorial m : ℝ) * (((i : ℕ) : ℝ) / N) ^ (m : ℕ) / (N : ℝ) ^ (n : ℕ))
      ring).trans
      (sum_fin_stirlingSecond_mul N n
        (fun m => (N.descFactorial m : ℝ) * (((i : ℕ) : ℝ) / N) ^ m / (N : ℝ) ^ (n : ℕ)))
  rw [hL, hR, Finset.sum_div]
  exact Finset.sum_congr rfl fun m _ => by ring

end Rhone.Coalescent
