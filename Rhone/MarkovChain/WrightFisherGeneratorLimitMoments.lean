/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.WrightFisher
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# One-step moments of the Wright–Fisher allele frequency

Source: ewens2004, sec. 3.2, ch. 4; karlin_taylor1981, ch. 15. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

theorem sum_binomRow_cube (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * (j : ℝ) ^ 3 =
      n * p * (1 + 3 * (n - 1) * p + (n - 1) * (n - 2) * p ^ 2) := by
  cases n with
  | zero => simp [binomRow]
  | succ n =>
    have h := sum_binomRow_shift n p (fun j => (j : ℝ) ^ 2)
    have h1 : ∑ k ∈ range (n + 1), binomRow n p k * ((k + 1 : ℕ) : ℝ) ^ 2 =
        (n * p * (1 - p) + (n * p) ^ 2) + 2 * (n * p) + 1 := by
      have e : ∀ k : ℕ, binomRow n p k * ((k + 1 : ℕ) : ℝ) ^ 2 =
          binomRow n p k * ((k : ℝ) * k) + 2 * (binomRow n p k * k) + binomRow n p k := by
        intro k
        push_cast
        ring
      simp only [e, sum_add_distrib, ← mul_sum, sum_binomRow_mul_mul, sum_binomRow_mul,
        sum_binomRow]
    rw [h1] at h
    have e3 : ∀ j : ℕ, binomRow (n + 1) p j * (j : ℝ) ^ 3 =
        binomRow (n + 1) p j * ((j : ℝ) * (j : ℝ) ^ 2) := fun j => by ring
    simp only [e3]
    rw [h]
    push_cast
    ring

theorem sum_binomRow_pow_four (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * (j : ℝ) ^ 4 =
      n * p * (1 + 7 * (n - 1) * p + 6 * (n - 1) * (n - 2) * p ^ 2
        + (n - 1) * (n - 2) * (n - 3) * p ^ 3) := by
  cases n with
  | zero => simp [binomRow]
  | succ n =>
    have h := sum_binomRow_shift n p (fun j => (j : ℝ) ^ 3)
    have h1 : ∑ k ∈ range (n + 1), binomRow n p k * ((k + 1 : ℕ) : ℝ) ^ 3 =
        n * p * (1 + 3 * (n - 1) * p + (n - 1) * (n - 2) * p ^ 2)
          + 3 * (n * p * (1 - p) + (n * p) ^ 2) + 3 * (n * p) + 1 := by
      have e : ∀ k : ℕ, binomRow n p k * ((k + 1 : ℕ) : ℝ) ^ 3 =
          binomRow n p k * (k : ℝ) ^ 3 + 3 * (binomRow n p k * ((k : ℝ) * k))
            + 3 * (binomRow n p k * k) + binomRow n p k := by
        intro k
        push_cast
        ring
      simp only [e, sum_add_distrib, ← mul_sum, sum_binomRow_cube, sum_binomRow_mul_mul,
        sum_binomRow_mul, sum_binomRow]
    rw [h1] at h
    have e4 : ∀ j : ℕ, binomRow (n + 1) p j * (j : ℝ) ^ 4 =
        binomRow (n + 1) p j * ((j : ℝ) * (j : ℝ) ^ 3) := fun j => by ring
    simp only [e4]
    rw [h]
    push_cast
    ring

theorem sum_binomRow_central (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * ((j : ℝ) - n * p) = 0 := by
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_binomRow_mul, sum_binomRow]
  ring

theorem sum_binomRow_central_sq (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * ((j : ℝ) - n * p) ^ 2 = n * p * (1 - p) := by
  have e : ∀ j : ℕ, binomRow n p j * ((j : ℝ) - n * p) ^ 2 =
      binomRow n p j * ((j : ℝ) * j) - 2 * (n * p) * (binomRow n p j * j)
        + (n * p) ^ 2 * binomRow n p j := fun j => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_binomRow_mul_mul,
    sum_binomRow_mul, sum_binomRow]
  ring

theorem sum_binomRow_central_cube (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * ((j : ℝ) - n * p) ^ 3 =
      n * p * (1 - p) * (1 - 2 * p) := by
  have e : ∀ j : ℕ, binomRow n p j * ((j : ℝ) - n * p) ^ 3 =
      binomRow n p j * (j : ℝ) ^ 3 - 3 * (n * p) * (binomRow n p j * ((j : ℝ) * j))
        + 3 * (n * p) ^ 2 * (binomRow n p j * j) - (n * p) ^ 3 * binomRow n p j :=
    fun j => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_binomRow_cube,
    sum_binomRow_mul_mul, sum_binomRow_mul, sum_binomRow]
  ring

theorem sum_binomRow_central_pow_four (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomRow n p j * ((j : ℝ) - n * p) ^ 4 =
      n * p * (1 - p) * (1 + 3 * (n - 2) * p * (1 - p)) := by
  have e : ∀ j : ℕ, binomRow n p j * ((j : ℝ) - n * p) ^ 4 =
      binomRow n p j * (j : ℝ) ^ 4 - 4 * (n * p) * (binomRow n p j * (j : ℝ) ^ 3)
        + 6 * (n * p) ^ 2 * (binomRow n p j * ((j : ℝ) * j))
        - 4 * (n * p) ^ 3 * (binomRow n p j * j) + (n * p) ^ 4 * binomRow n p j :=
    fun j => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_binomRow_pow_four,
    sum_binomRow_cube, sum_binomRow_mul_mul, sum_binomRow_mul, sum_binomRow]
  ring

theorem sum_binomRow_freq_sub_pow {N : ℕ} (hN : 1 ≤ N) (p : ℝ) (k : ℕ) :
    ∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N - p) ^ k =
      (∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) - N * p) ^ k) / (N : ℝ) ^ k := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  have e : (j : ℝ) / N - p = ((j : ℝ) - N * p) / N := by field_simp
  rw [e, div_pow, mul_div_assoc]

theorem sum_binomRow_freq_sub_pow_four_le {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (h0 : 0 ≤ p)
    (h1 : p ≤ 1) :
    ∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N - p) ^ 4 ≤ 3 / (16 * (N : ℝ) ^ 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  rw [sum_binomRow_freq_sub_pow hN, sum_binomRow_central_pow_four]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = p * (1 - p) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg h0 (by linarith)
  have ht4 : t ≤ 1 / 4 := by rw [ht]; nlinarith [sq_nonneg (p - 1 / 2)]
  have h16 : 0 ≤ 1 / 16 - t ^ 2 := by nlinarith
  have key : t * (1 + 3 * ((N : ℝ) - 2) * t) ≤ 3 * N / 16 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hN1) h16, sq_nonneg (t - 1 / 6)]
  have e : (N : ℝ) * p * (1 - p) * (1 + 3 * ((N : ℝ) - 2) * p * (1 - p)) =
      N * (t * (1 + 3 * ((N : ℝ) - 2) * t)) := by rw [ht]; ring
  rw [e]
  calc (N : ℝ) * (t * (1 + 3 * ((N : ℝ) - 2) * t)) / (N : ℝ) ^ 4
      ≤ (N : ℝ) * (3 * N / 16) / (N : ℝ) ^ 4 := by gcongr
    _ = 3 / (16 * (N : ℝ) ^ 2) := by field_simp

theorem sum_binomRow_abs_freq_sub_cube_le {N : ℕ} (hN : 1 ≤ N) {p : ℝ} (h0 : 0 ≤ p)
    (h1 : p ≤ 1) :
    ∑ j ∈ range (N + 1), binomRow N p j * |(j : ℝ) / N - p| ^ 3 ≤
      7 / (32 * (N * √(N : ℝ))) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √(N : ℝ) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hNpos
  have hrr : r * r = N := by rw [hr]; exact Real.mul_self_sqrt hNpos.le
  rw [← hr]
  have hpt : ∀ h : ℝ, |h| ^ 3 ≤ (h ^ 2 / r + r * h ^ 4) / 2 := by
    intro h
    have h2 : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
    have h4 : h ^ 4 = |h| ^ 4 := by
      rw [show h ^ 4 = (h ^ 2) ^ 2 by ring, h2]
      ring
    rw [h2, h4]
    have key : (|h| ^ 2 / r + r * |h| ^ 4) / 2 - |h| ^ 3 =
        |h| ^ 2 * (1 - r * |h|) ^ 2 / (2 * r) := by
      field_simp
      ring
    have hnn : 0 ≤ |h| ^ 2 * (1 - r * |h|) ^ 2 / (2 * r) := by positivity
    linarith
  have hS2 : ∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N - p) ^ 2 ≤ 1 / (4 * N) := by
    rw [sum_binomRow_freq_sub_pow hN, sum_binomRow_central_sq]
    have ht4 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    calc (N : ℝ) * p * (1 - p) / (N : ℝ) ^ 2 = p * (1 - p) / N := by field_simp
      _ ≤ (1 / 4) / N := by gcongr
      _ = 1 / (4 * N) := by field_simp
  have hS4 := sum_binomRow_freq_sub_pow_four_le hN h0 h1
  calc ∑ j ∈ range (N + 1), binomRow N p j * |(j : ℝ) / N - p| ^ 3
      ≤ ∑ j ∈ range (N + 1), binomRow N p j *
          ((((j : ℝ) / N - p) ^ 2 / r + r * ((j : ℝ) / N - p) ^ 4) / 2) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpt _) (binomRow_nonneg h0 h1 j)
    _ = ((∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N - p) ^ 2) / r
          + r * ∑ j ∈ range (N + 1), binomRow N p j * ((j : ℝ) / N - p) ^ 4) / 2 := by
        rw [sum_div, mul_sum, ← sum_add_distrib, sum_div]
        exact sum_congr rfl fun j _ => by ring
    _ ≤ (1 / (4 * N) / r + r * (3 / (16 * (N : ℝ) ^ 2))) / 2 := by gcongr
    _ = 7 / (32 * (N * r)) := by
        rw [← hrr]
        field_simp
        ring

theorem freq_mem_Icc {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    ((i : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hNpos]
  exact_mod_cast Nat.lt_succ_iff.1 i.2

theorem wf_expect_freq_sub {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => (j : ℝ) / N - (i : ℝ) / N) i = 0 := by
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range (fun j => binomRow N ((i : ℝ) / N) j * ((j : ℝ) / N - (i : ℝ) / N))]
  have h := sum_binomRow_freq_sub_pow hN ((i : ℝ) / N) 1
  simp only [pow_one] at h
  rw [h, sum_binomRow_central, zero_div]

theorem wf_expect_freq_sub_sq {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N) / N := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range
    (fun j => binomRow N ((i : ℝ) / N) j * ((j : ℝ) / N - (i : ℝ) / N) ^ 2),
    sum_binomRow_freq_sub_pow hN, sum_binomRow_central_sq]
  field_simp

theorem wf_expect_freq_sub_cube {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 3) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N) * (1 - 2 * ((i : ℝ) / N)) / (N : ℝ) ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range
    (fun j => binomRow N ((i : ℝ) / N) j * ((j : ℝ) / N - (i : ℝ) / N) ^ 3),
    sum_binomRow_freq_sub_pow hN, sum_binomRow_central_cube]
  field_simp

theorem wf_expect_freq_sub_pow_four {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 4) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N)
        * (1 + 3 * ((N : ℝ) - 2) * ((i : ℝ) / N) * (1 - (i : ℝ) / N)) / (N : ℝ) ^ 3 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range
    (fun j => binomRow N ((i : ℝ) / N) j * ((j : ℝ) / N - (i : ℝ) / N) ^ 4),
    sum_binomRow_freq_sub_pow hN, sum_binomRow_central_pow_four]
  field_simp

theorem wf_expect_freq_sub_pow_four_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 4) i ≤ 3 / (16 * (N : ℝ) ^ 2) := by
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range
    (fun j => binomRow N ((i : ℝ) / N) j * ((j : ℝ) / N - (i : ℝ) / N) ^ 4)]
  exact sum_binomRow_freq_sub_pow_four_le hN (freq_mem_Icc hN i).1 (freq_mem_Icc hN i).2

theorem wf_expect_abs_freq_sub_cube_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => |(j : ℝ) / N - (i : ℝ) / N| ^ 3) i ≤
      7 / (32 * (N * √(N : ℝ))) := by
  simp only [CountKernel.expect, wf_apply, wfRow]
  rw [sum_fin_eq_range
    (fun j => binomRow N ((i : ℝ) / N) j * |(j : ℝ) / N - (i : ℝ) / N| ^ 3)]
  exact sum_binomRow_abs_freq_sub_cube_le hN (freq_mem_Icc hN i).1 (freq_mem_Icc hN i).2

end Rhone.MarkovChain
