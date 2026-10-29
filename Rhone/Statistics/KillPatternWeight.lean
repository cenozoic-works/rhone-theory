/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.TreeLengthLaplace

/-! # Kill-pattern weights: recursion, splitting, and integral -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain

noncomputable def killPatternWeight (β : ℝ) (d s : ℕ) : ℝ :=
  (d.factorial : ℝ) * β ^ d / ∏ i ∈ range (d + 1), (1 + β * ((s : ℝ) + i))

theorem one_add_mul_pos {β : ℝ} (hβ : 0 ≤ β) {x : ℝ} (hx : 0 ≤ x) : 0 < 1 + β * x := by
  have := mul_nonneg hβ hx
  linarith

theorem prod_one_add_mul_pos {β : ℝ} (hβ : 0 ≤ β) (d s : ℕ) :
    0 < ∏ i ∈ range d, (1 + β * ((s : ℝ) + i)) :=
  Finset.prod_pos fun i _ => one_add_mul_pos hβ (by positivity)

theorem killPatternWeight_zero (β : ℝ) (s : ℕ) :
    killPatternWeight β 0 s = 1 / (1 + β * s) := by
  simp [killPatternWeight]

theorem killPatternWeight_succ {β : ℝ} (hβ : 0 ≤ β) (d s : ℕ) :
    killPatternWeight β (d + 1) s =
      ((d : ℝ) + 1) * β / (1 + β * ((s : ℝ) + d + 1)) * killPatternWeight β d s := by
  have hP := (prod_one_add_mul_pos hβ (d + 1) s).ne'
  have hq : (1 + β * ((s : ℝ) + d + 1)) ≠ 0 := (one_add_mul_pos hβ (by positivity)).ne'
  unfold killPatternWeight
  rw [Finset.prod_range_succ _ (d + 1), Nat.factorial_succ]
  push_cast
  rw [show (s : ℝ) + ((d : ℝ) + 1) = (s : ℝ) + d + 1 by ring]
  field_simp
  ring

theorem killPatternWeight_split {β : ℝ} (hβ : 0 ≤ β) (d s : ℕ) :
    killPatternWeight β d s = killPatternWeight β (d + 1) s + killPatternWeight β d (s + 1) := by
  have hQ := (prod_one_add_mul_pos hβ d (s + 1)).ne'
  have hq : (1 + β * ((s : ℝ) + d + 1)) ≠ 0 := (one_add_mul_pos hβ (by positivity)).ne'
  have hs : (1 + β * (s : ℝ)) ≠ 0 := (one_add_mul_pos hβ (by positivity)).ne'
  have hshift : ∏ i ∈ range d, (1 + β * ((s : ℝ) + ((i + 1 : ℕ) : ℝ))) =
      ∏ i ∈ range d, (1 + β * (((s + 1 : ℕ) : ℝ) + i)) := by
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have h1 : ∏ i ∈ range (d + 1), (1 + β * ((s : ℝ) + i)) =
      (∏ i ∈ range d, (1 + β * (((s + 1 : ℕ) : ℝ) + i))) * (1 + β * (s : ℝ)) := by
    rw [Finset.prod_range_succ', hshift]
    simp
  have h2 : ∏ i ∈ range (d + 1), (1 + β * (((s + 1 : ℕ) : ℝ) + i)) =
      (∏ i ∈ range d, (1 + β * (((s + 1 : ℕ) : ℝ) + i))) * (1 + β * ((s : ℝ) + d + 1)) := by
    rw [Finset.prod_range_succ]
    congr 2
    push_cast
    ring
  rw [killPatternWeight_succ hβ]
  unfold killPatternWeight
  rw [h1, h2]
  field_simp
  ring

theorem integral_killPattern {β : ℝ} (hβ : 0 ≤ β) (d s : ℕ) :
    ∫ t, (1 - Real.exp (-(β * max 0 t))) ^ d * Real.exp (-(β * max 0 t)) ^ s ∂expMeasure 1 =
      killPatternWeight β d s := by
  induction d generalizing s with
  | zero =>
    rw [killPatternWeight_zero]
    have h := integral_pow_mul_exp_expMeasure_one (a := β * s) (by positivity) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h
    rw [← h]
    apply integral_congr_ae
    refine ae_of_all _ fun t => ?_
    change 1 * Real.exp (-(β * max 0 t)) ^ s = Real.exp (-(β * s * max 0 t))
    rw [one_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  | succ d ih =>
    have hbound : ∀ (d s : ℕ) (t : ℝ),
        ‖(1 - Real.exp (-(β * max 0 t))) ^ d * Real.exp (-(β * max 0 t)) ^ s‖ ≤ 1 := by
      intro d s t
      have he0 : 0 < Real.exp (-(β * max 0 t)) := Real.exp_pos _
      have he1 : Real.exp (-(β * max 0 t)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hβ (le_max_left _ _)))
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg he0.le _))]
      calc (1 - Real.exp (-(β * max 0 t))) ^ d * Real.exp (-(β * max 0 t)) ^ s
          ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (by linarith) (by linarith))
            (pow_le_one₀ he0.le he1) (pow_nonneg he0.le _) zero_le_one
        _ = 1 := one_mul 1
    have hint : ∀ d s : ℕ, Integrable (fun t : ℝ =>
        (1 - Real.exp (-(β * max 0 t))) ^ d * Real.exp (-(β * max 0 t)) ^ s) (expMeasure 1) :=
      fun d s => Integrable.of_bound (by fun_prop) 1 (ae_of_all _ (hbound d s))
    have hpt : ∀ t : ℝ,
        (1 - Real.exp (-(β * max 0 t))) ^ (d + 1) * Real.exp (-(β * max 0 t)) ^ s =
          (1 - Real.exp (-(β * max 0 t))) ^ d * Real.exp (-(β * max 0 t)) ^ s -
            (1 - Real.exp (-(β * max 0 t))) ^ d * Real.exp (-(β * max 0 t)) ^ (s + 1) := by
      intro t
      ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub (hint d s) (hint d (s + 1)), ih, ih,
      killPatternWeight_split hβ d s]
    ring

end Rhone.Statistics
