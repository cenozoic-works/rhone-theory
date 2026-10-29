/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Factorial.Basic

/-! # Merger rates of Λ-coalescents -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Set

noncomputable def lambdaRate (Λ : Measure ℝ) (b k : ℕ) : ℝ :=
  ∫ x in Icc (0 : ℝ) 1, x ^ (k - 2) * (1 - x) ^ (b - k) ∂Λ

variable {Λ : Measure ℝ}

theorem lambdaIntegrand_mem {m n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ x ^ m * (1 - x) ^ n ∧ x ^ m * (1 - x) ^ n ≤ 1 := by
  obtain ⟨h0, h1⟩ := hx
  have hb : 0 ≤ (1 - x) ^ n := pow_nonneg (by linarith) n
  refine ⟨mul_nonneg (pow_nonneg h0 m) hb, ?_⟩
  have h2 := pow_le_one₀ h0 h1 (n := m)
  have h3 := pow_le_one₀ (by linarith : 0 ≤ 1 - x) (by linarith : 1 - x ≤ 1) (n := n)
  calc x ^ m * (1 - x) ^ n ≤ 1 * 1 := mul_le_mul h2 h3 hb zero_le_one
    _ = 1 := by norm_num

theorem integrableOn_lambdaIntegrand (hΛ : Λ (Icc 0 1) ≠ ⊤) (m n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ m * (1 - x) ^ n) (Icc 0 1) Λ := by
  refine Measure.integrableOn_of_bounded (M := 1) hΛ ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ => x ^ m * (1 - x) ^ n).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    obtain ⟨h0, h1⟩ := lambdaIntegrand_mem (m := m) (n := n) hx
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1

theorem lambdaRate_nonneg (b k : ℕ) : 0 ≤ lambdaRate Λ b k :=
  setIntegral_nonneg measurableSet_Icc fun _ hx => (lambdaIntegrand_mem hx).1

theorem lambdaRate_le (hΛ : Λ (Icc 0 1) ≠ ⊤) (b k : ℕ) :
    lambdaRate Λ b k ≤ Λ.real (Icc 0 1) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := Λ) (s := Icc (0 : ℝ) 1) (C := 1)
    (f := fun x : ℝ => x ^ (k - 2) * (1 - x) ^ (b - k)) (lt_top_iff_ne_top.2 hΛ)
    (fun x hx => by
      obtain ⟨h0, h1⟩ := lambdaIntegrand_mem (m := k - 2) (n := b - k) hx
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  rw [one_mul] at h
  exact (le_abs_self _).trans h

/-- Source: pitman1999, Lemma 18, eq. (22). -/
theorem lambdaRate_consistency (hΛ : Λ (Icc 0 1) ≠ ⊤) {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    lambdaRate Λ b k = lambdaRate Λ (b + 1) k + lambdaRate Λ (b + 1) (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = m + 2 + n := ⟨b - (m + 2), by omega⟩
  unfold lambdaRate
  have e1 : m + 2 + n - (m + 2) = n := by omega
  have e2 : m + 2 + n + 1 - (m + 2) = n + 1 := by omega
  have e3 : m + 2 + n + 1 - (m + 2 + 1) = n := by omega
  have e4 : m + 2 + 1 - 2 = m + 1 := by omega
  simp only [e1, e2, e3, e4, Nat.add_sub_cancel]
  rw [← integral_add (integrableOn_lambdaIntegrand hΛ m (n + 1))
    (integrableOn_lambdaIntegrand hΛ (m + 1) n)]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  ring

theorem lambdaRate_dirac_zero (b k : ℕ) :
    lambdaRate (Measure.dirac 0) b k = (0 : ℝ) ^ (k - 2) := by
  unfold lambdaRate
  rw [setIntegral_dirac]
  simp

theorem lambdaRate_dirac_zero_two (b : ℕ) : lambdaRate (Measure.dirac 0) b 2 = 1 := by
  simp [lambdaRate_dirac_zero]

theorem lambdaRate_dirac_zero_of_three_le (b : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    lambdaRate (Measure.dirac 0) b k = 0 := by
  rw [lambdaRate_dirac_zero, zero_pow (by omega)]

theorem integral_pow_one_sub_pow (m n : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, x ^ m * (1 - x) ^ n =
      (m.factorial * n.factorial : ℝ) / ((m + n + 1).factorial : ℝ) := by
  induction n generalizing m with
  | zero =>
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp only [pow_zero, mul_one, integral_pow]
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, add_zero, Nat.factorial_succ]
    push_cast
    field_simp
    simp
  | succ n ih =>
    have hint := fun a b : ℕ => integrableOn_lambdaIntegrand
      (Λ := volume) (by simp) a b
    have h : ∫ x in Icc (0 : ℝ) 1, x ^ m * (1 - x) ^ n =
        (∫ x in Icc (0 : ℝ) 1, x ^ m * (1 - x) ^ (n + 1)) +
          ∫ x in Icc (0 : ℝ) 1, x ^ (m + 1) * (1 - x) ^ n := by
      rw [← integral_add (hint m (n + 1)) (hint (m + 1) n)]
      refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
      ring
    have h1 := ih m
    have h2 := ih (m + 1)
    have h3 : (∫ x in Icc (0 : ℝ) 1, x ^ m * (1 - x) ^ (n + 1)) =
        (∫ x in Icc (0 : ℝ) 1, x ^ m * (1 - x) ^ n) -
          ∫ x in Icc (0 : ℝ) 1, x ^ (m + 1) * (1 - x) ^ n := by linarith
    rw [h3, h1, h2]
    have e1 : m + 1 + n + 1 = m + n + 2 := by ring
    have e2 : m + (n + 1) + 1 = m + n + 2 := by ring
    rw [e1, e2]
    have hf : ((m + n + 2).factorial : ℝ) = ((m : ℝ) + n + 2) * ((m + n + 1).factorial : ℝ) := by
      rw [show m + n + 2 = (m + n + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      ring
    rw [hf]
    simp only [Nat.factorial_succ]
    push_cast
    have : ((m + n + 1).factorial : ℝ) ≠ 0 := by positivity
    have h4 : (0 : ℝ) < (m : ℝ) + n + 2 := by positivity
    field_simp
    ring

/-- Source: bolthausen_sznitman1998, Prop. 1.3, eq. (1.33). -/
theorem lambdaRate_lebesgue {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    lambdaRate (volume.restrict (Icc 0 1)) b k =
      ((k - 2).factorial * (b - k).factorial : ℝ) / ((b - 1).factorial : ℝ) := by
  unfold lambdaRate
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_self,
    integral_pow_one_sub_pow]
  have : k - 2 + (b - k) + 1 = b - 1 := by omega
  rw [this]

theorem choose_mul_lambdaRate_lebesgue {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    (b.choose k : ℝ) * lambdaRate (volume.restrict (Icc 0 1)) b k =
      (b : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
  rw [lambdaRate_lebesgue hk hkb]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = j + 2 + c := ⟨b - (j + 2), by omega⟩
  have hch := Nat.choose_mul_factorial_mul_factorial hkb
  have e1 : j + 2 - 2 = j := by omega
  have e2 : j + 2 + c - (j + 2) = c := by omega
  have e3 : j + 2 + c - 1 = j + c + 1 := by omega
  rw [e2] at hch
  rw [e1, e2, e3]
  have hb : ((j + 2 + c).factorial : ℝ) = ((j : ℝ) + c + 2) * ((j + c + 1).factorial : ℝ) := by
    rw [show j + 2 + c = (j + c + 1) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring
  have hk2 : ((j + 2).factorial : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hch' : ((j + 2 + c).choose (j + 2) : ℝ) * ((j + 2).factorial : ℝ) * (c.factorial : ℝ) =
      ((j + 2 + c).factorial : ℝ) := by exact_mod_cast hch
  rw [hb, hk2] at hch'
  have hf : ((j + c + 1).factorial : ℝ) ≠ 0 := by positivity
  have h1 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  push_cast
  rw [mul_div_assoc', div_eq_div_iff hf (by nlinarith)]
  have h3 : ((j : ℝ) + 2) * ((j : ℝ) + 2 - 1) = ((j : ℝ) + 2) * ((j : ℝ) + 1) := by ring
  rw [h3]
  linear_combination hch'

theorem sum_Icc_inv_sub (b : ℕ) (hb : 1 ≤ b) :
    ∑ k ∈ Finset.Icc 2 b, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 - 1 / (b : ℝ) := by
  induction b, hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hb0 : (b : ℝ) ≠ 0 := by positivity
    have h1 : (b : ℝ) + 1 - 1 = b := by ring
    push_cast
    rw [h1]
    field_simp
    ring

theorem sum_choose_mul_lambdaRate_lebesgue (b : ℕ) (hb : 1 ≤ b) :
    ∑ k ∈ Finset.Icc 2 b, (b.choose k : ℝ) * lambdaRate (volume.restrict (Icc 0 1)) b k =
      (b : ℝ) - 1 := by
  have h : ∀ k ∈ Finset.Icc 2 b, (b.choose k : ℝ) * lambdaRate (volume.restrict (Icc 0 1)) b k =
      (b : ℝ) * (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hk
    rw [choose_mul_lambdaRate_lebesgue h1 h2]
    have : (2 : ℝ) ≤ k := by exact_mod_cast h1
    have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_Icc_inv_sub b hb]
  have : (b : ℝ) ≠ 0 := by positivity
  field_simp

end Rhone.Coalescent
