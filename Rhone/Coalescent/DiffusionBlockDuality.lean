/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Semigroup
public import Rhone.Diffusion.GeneratorC2
public import Rhone.Coalescent.KingmanChain

/-! # Generator duality of the Wright–Fisher diffusion and Kingman's block-counting chain -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Matrix Polynomial Diffusion MarkovChain Rhone.Combinatorics

/-- Source: berestycki2009, Thm 2.7, eq. (33)–(34); etheridge2011. -/
theorem wfGenerator_pow (k : ℕ) (x : ℝ) :
    wfGenerator (fun y => y ^ k) x = (coalRate k : ℝ) * (x ^ (k - 1) - x ^ k) := by
  have h := wfGenerator_eval (X ^ k) x
  simp only [eval_pow, eval_X] at h
  rw [h]
  rcases k with _ | _ | k
  · simp [coalRate]
  · simp [coalRate]
  · simp only [derivative_X_pow, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul,
      eval_C, eval_pow, eval_X, coalRate, Nat.add_sub_cancel]
    push_cast
    ring

/-- Source: berestycki2009, Thm 2.7, eq. (33)–(34); etheridge2011. -/
theorem wfGenerator_blockChain_duality (n : ℕ) (k : Fin (n + 1)) (x : ℝ) :
    wfGenerator (fun y => y ^ (k : ℕ)) x = ∑ j, (blockChain n).Q k j * x ^ (j : ℕ) := by
  rw [wfGenerator_pow]
  by_cases hk : 1 ≤ (k : ℕ)
  · rw [blockChain_Q, sum_blockQ_mul n k hk fun j => x ^ (j : ℕ)]
  · have h0 : coalRate (k : ℕ) = 0 := coalRate_eq_zero (by omega)
    simp [blockChain_Q, blockQ, h0]

theorem wfGenerator_sum_mul_pow (n : ℕ) (c : Fin (n + 1) → ℝ) (x : ℝ) :
    wfGenerator (fun y => ∑ j, c j * y ^ (j : ℕ)) x =
      ∑ j, c j * wfGenerator (fun y => y ^ (j : ℕ)) x := by
  have e : (fun y : ℝ => ∑ j, c j * y ^ (j : ℕ)) =
      fun y => (∑ j : Fin (n + 1), C (c j) * X ^ (j : ℕ) : ℝ[X]).eval y :=
    funext fun y => by simp [eval_finsetSum]
  have e' : ∀ j : Fin (n + 1), wfGenerator (fun y => y ^ (j : ℕ)) x =
      x * (1 - x) / 2 * (derivative (derivative (X ^ (j : ℕ) : ℝ[X]))).eval x := fun j => by
    have h := wfGenerator_eval (X ^ (j : ℕ)) x
    simpa only [eval_pow, eval_X] using h
  rw [e, wfGenerator_eval]
  simp only [e', derivative_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem blockChain_moment_zero (n : ℕ) (k : Fin (n + 1)) (x : ℝ) :
    ∑ j, (blockChain n).semigroup 0 k j * x ^ (j : ℕ) = x ^ (k : ℕ) := by
  simp [RateChain.semigroup_zero, Matrix.one_apply]

/-- Source: berestycki2009, Thm 2.7, eq. (33)–(34); etheridge2011. -/
theorem hasDerivAt_blockChain_moment (n : ℕ) (k : Fin (n + 1)) (x t : ℝ) :
    HasDerivAt (fun s => ∑ j, (blockChain n).semigroup s k j * x ^ (j : ℕ))
      (wfGenerator (fun y => ∑ j, (blockChain n).semigroup t k j * y ^ (j : ℕ)) x) t := by
  have h : HasDerivAt (fun s => ∑ j, (blockChain n).semigroup s k j * x ^ (j : ℕ))
      (∑ j, ((blockChain n).semigroup t * (blockChain n).Q) k j * x ^ (j : ℕ)) t :=
    HasDerivAt.fun_sum fun j _ =>
      ((blockChain n).hasDerivAt_semigroup t k j).mul_const (x ^ (j : ℕ))
  convert h using 1
  rw [wfGenerator_sum_mul_pow]
  simp only [wfGenerator_blockChain_duality, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Rhone.Coalescent
