/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Algebraic bounds for the dominating second-recombination race -/
@[expose] public section
noncomputable section
namespace Rhone.Coalescent.SmcBound

def raceBound (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => raceBound h n + h n * (1 - raceBound h n)

theorem raceBound_product (h : ℕ → ℝ) (n : ℕ) :
    1 - raceBound h n = ∏ j ∈ Finset.range n, (1 - h j) := by
  induction n with
  | zero => simp [raceBound]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp only [raceBound]
    ring

def raceSum (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => raceSum h n + h n

theorem raceBound_nonneg_le_one (h : ℕ → ℝ)
    (hh : ∀ j, 0 ≤ h j ∧ h j ≤ 1) (n : ℕ) :
    0 ≤ raceBound h n ∧ raceBound h n ≤ 1 := by
  induction n with
  | zero => simp [raceBound]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := hh n
    simp only [raceBound]
    constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.mpr ih.2),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr ih.2)]

theorem raceBound_le_sum (h : ℕ → ℝ)
    (hh : ∀ j, 0 ≤ h j ∧ h j ≤ 1) (n : ℕ) :
    raceBound h n ≤ raceSum h n := by
  induction n with
  | zero => simp [raceBound, raceSum]
  | succ n ih =>
    have hp := (raceBound_nonneg_le_one h hh n).1
    have h0 := (hh n).1
    simp only [raceBound, raceSum]
    nlinarith [mul_nonneg h0 hp]

def hazard (R : ℝ) (j : ℕ) : ℝ := R / ((j : ℝ) + 1 + R)

def harmonic : ℕ → ℝ
  | 0 => 0
  | n + 1 => harmonic n + 1 / ((n : ℝ) + 1)

theorem hazard_bounds (R : ℝ) (hR : 0 ≤ R) (j : ℕ) :
    0 ≤ hazard R j ∧ hazard R j ≤ 1 := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  unfold hazard
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℝ) < (j : ℝ) + 1 + R)).2
    linarith

theorem hazard_le_linear (R : ℝ) (hR : 0 ≤ R) (j : ℕ) :
    hazard R j ≤ R * (1 / ((j : ℝ) + 1)) := by
  unfold hazard
  rw [mul_one_div]
  apply div_le_div_of_nonneg_left hR (by positivity)
  linarith

theorem raceSum_hazard_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    raceSum (hazard R) n ≤ R * harmonic n := by
  induction n with
  | zero => simp [raceSum, harmonic]
  | succ n ih =>
    simp only [raceSum, harmonic, mul_add]
    exact add_le_add ih (hazard_le_linear R hR n)

theorem second_race_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    raceBound (hazard R) n ≤ R * harmonic n := by
  exact (raceBound_le_sum (hazard R) (hazard_bounds R hR) n).trans
    (raceSum_hazard_le R hR n)

theorem weighted_quadratic_bound (ι : Type*) (s : Finset ι)
    (w b : ι → ℝ) (R A B : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : ∑ i ∈ s, w i ≤ R * A)
    (hb : ∀ i ∈ s, b i ≤ R * B) :
    ∑ i ∈ s, w i * b i ≤ R ^ 2 * A * B := by
  calc
    ∑ i ∈ s, w i * b i ≤ ∑ i ∈ s, w i * (R * B) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hb i hi) (hw i hi)
    _ = (∑ i ∈ s, w i) * (R * B) := by
      classical
      clear hw hmass hb
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [ih]
        ring
    _ ≤ (R * A) * (R * B) :=
      mul_le_mul_of_nonneg_right hmass (mul_nonneg hR hB)
    _ = R ^ 2 * A * B := by ring

theorem first_weights_sum (h : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, h j * (1 - raceBound h j) = raceBound h n := by
  induction n with
  | zero => simp [raceBound]
  | succ n ih => rw [Finset.sum_range_succ, ih, raceBound]

theorem harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih => simp only [harmonic]; positivity

theorem first_second_quadratic (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (b : ℕ → ℝ)
    (hb : ∀ j ∈ Finset.range n, b j ≤ R * harmonic (n + 1)) :
    ∑ j ∈ Finset.range n, hazard R j * (1 - raceBound (hazard R) j) * b j
      ≤ R ^ 2 * harmonic n * harmonic (n + 1) := by
  apply weighted_quadratic_bound ℕ (Finset.range n)
    (fun j => hazard R j * (1 - raceBound (hazard R) j)) b
    R (harmonic n) (harmonic (n + 1)) hR (harmonic_nonneg (n + 1))
  · intro j _
    exact mul_nonneg (hazard_bounds R hR j).1
      (sub_nonneg.mpr (raceBound_nonneg_le_one (hazard R) (hazard_bounds R hR) j).2)
  · rw [first_weights_sum]
    exact second_race_bound R hR n
  · exact hb

end Rhone.Coalescent.SmcBound
