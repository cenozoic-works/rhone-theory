/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.CountChain
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-! # Haploid two-allele Wright–Fisher chain -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

def binomRow (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

theorem binomRow_nonneg {n : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (j : ℕ) :
    0 ≤ binomRow n p j := by
  have : 0 ≤ 1 - p := by linarith
  unfold binomRow
  positivity

theorem sum_binomRow (n : ℕ) (p : ℝ) : ∑ j ∈ range (n + 1), binomRow n p j = 1 := by
  have := (add_pow p (1 - p) n).symm
  simpa [binomRow, mul_comm, mul_left_comm, mul_assoc] using this

theorem sum_binomRow_shift (n : ℕ) (p : ℝ) (g : ℕ → ℝ) :
    ∑ j ∈ range (n + 2), binomRow (n + 1) p j * (j * g j) =
      (n + 1) * p * ∑ k ∈ range (n + 1), binomRow n p k * g (k + 1) := by
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun k _ => ?_
  have h : ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) = ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  simp only [binomRow, Nat.add_sub_add_right]
  push_cast at h ⊢
  calc (((n + 1).choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (n - k))
        * (((k : ℝ) + 1) * g (k + 1))
      = (((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1)) * p ^ (k + 1) * (1 - p) ^ (n - k)
          * g (k + 1) := by ring
    _ = _ := by rw [← h]; ring

theorem sum_binomRow_mul (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * j = n * p := by
  cases n with
  | zero => simp [binomRow]
  | succ n =>
    have := sum_binomRow_shift n p (fun _ => 1)
    simp only [mul_one, sum_binomRow] at this
    push_cast
    rw [this]

theorem sum_binomRow_mul_mul (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * (j * j) = n * p * (1 - p) + (n * p) ^ 2 := by
  cases n with
  | zero => simp [binomRow]
  | succ n =>
    have h := sum_binomRow_shift n p (fun j => (j : ℝ))
    have h1 : ∑ k ∈ range (n + 1), binomRow n p k * ((k + 1 : ℕ) : ℝ) = n * p + 1 := by
      push_cast
      simp only [mul_add, mul_one, sum_add_distrib, sum_binomRow_mul, sum_binomRow]
    rw [h1] at h
    push_cast
    rw [h]; ring

noncomputable def wfRow (N i j : ℕ) : ℝ := binomRow N ((i : ℝ) / N) j

noncomputable def wf (N : ℕ) : CountKernel N := fun i j => wfRow N i j

theorem wf_apply (N : ℕ) (i j : Fin (N + 1)) : wf N i j = wfRow N i j := rfl

private theorem freq_mem {N i : ℕ} (hi : i ≤ N) : 0 ≤ (i : ℝ) / N ∧ (i : ℝ) / N ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hi

theorem sum_fin_eq_range {N : ℕ} (f : ℕ → ℝ) :
    ∑ j : Fin (N + 1), f j = ∑ j ∈ range (N + 1), f j :=
  Fin.sum_univ_eq_sum_range f (N + 1)

theorem wf_isStochastic (N : ℕ) : (wf N).IsStochastic := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have := freq_mem (Nat.lt_succ_iff.mp i.2)
    exact binomRow_nonneg this.1 this.2 _
  · simp only [wf_apply, wfRow]
    rw [sum_fin_eq_range (fun j => binomRow N ((i : ℝ) / N) j), sum_binomRow]

theorem wf_expect_id (N : ℕ) (i : Fin (N + 1)) :
    (wf N).expect (fun j => (j : ℝ)) i = i := by
  have hN : (N : ℝ) = 0 ∨ (N : ℝ) ≠ 0 := by tauto
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range (fun j => binomRow N ((i : ℝ) / N) j * j), sum_binomRow_mul]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · have : (i : ℕ) = 0 := by omega
    simp [h0, this]
  · field_simp

theorem wf_expect_sq (N : ℕ) (i : Fin (N + 1)) :
    (wf N).expect (fun j => (j : ℝ) * j) i =
      N * ((i : ℝ) / N) * (1 - (i : ℝ) / N) + (i : ℝ) ^ 2 := by
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range (fun j => binomRow N ((i : ℝ) / N) j * (j * j)), sum_binomRow_mul_mul]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · have : (i : ℕ) = 0 := by omega
    simp [h0, this]
  · have : (N : ℝ) ≠ 0 := by positivity
    field_simp

theorem wf_variance (N : ℕ) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) - i) ^ 2) i =
      N * ((i : ℝ) / N) * (1 - (i : ℝ) / N) := by
  have h1 := wf_expect_id N i
  have h2 := wf_expect_sq N i
  have hs := (wf_isStochastic N).2 i
  have : (wf N).expect (fun j => ((j : ℝ) - i) ^ 2) i =
      (wf N).expect (fun j => (j : ℝ) * j) i
        - 2 * (i : ℝ) * (wf N).expect (fun j => (j : ℝ)) i + (i : ℝ) ^ 2 := by
    simp only [CountKernel.expect]
    have : ∀ j : Fin (N + 1), wf N i j * ((j - (i : ℝ)) ^ 2) =
        wf N i j * (j * j) - 2 * i * (wf N i j * j) + (i : ℝ) ^ 2 * wf N i j := by
      intro j; ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hs]
    ring
  rw [this, h1, h2]; ring

end Rhone.MarkovChain
