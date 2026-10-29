/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Moran
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite Green summands for the neutral Moran Poisson equation

Source: ewens2004, sec. 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain.MoranAbsorptionSupport

open Finset

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def green (N i j : ℕ) : ℝ :=
  (N : ℝ) * (min i j : ℕ) * ((N : ℝ) - (max i j : ℕ)) /
    ((j : ℝ) * ((N : ℝ) - j))

/-- Source: ewens2004, sec. 3.4. -/
theorem green_zero (N j : ℕ) : green N 0 j = 0 := by simp [green]

/-- Source: ewens2004, sec. 3.4. -/
theorem green_self (N j : ℕ) (hj : j ≤ N) : green N N j = 0 := by
  simp [green, max_eq_left hj]

/-- Source: ewens2004, sec. 3.4. -/
theorem green_poisson {N i j : ℕ} (hi0 : 0 < i) (hiN : i < N)
    (hj0 : 0 < j) (hjN : j < N) :
    moranUp N 1 i * (green N (i + 1) j + green N (i - 1) j - 2 * green N i j) =
      if j = i then -1 else 0 := by
  have hpred : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hN : 0 < N := lt_trans hi0 hiN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hjr : (j : ℝ) ≠ 0 := by positivity
  have hdiff : (N : ℝ) - j ≠ 0 := by
    have : (j : ℝ) < N := by exact_mod_cast hjN
    linarith
  rw [moranUp_one]
  rcases lt_trichotomy i j with hij | hij | hij
  · have h1 : i + 1 ≤ j := by omega
    have h2 : i - 1 ≤ j := by omega
    have h3 : i ≤ j := by omega
    have hji : j ≠ i := by omega
    simp only [green, min_eq_left h1, max_eq_right h1,
      min_eq_left h2, max_eq_right h2, min_eq_left h3, max_eq_right h3,
      hpred, Nat.cast_add, Nat.cast_one, ite_eq_right hji]
    ring
  · subst j
    have h1 : i ≤ i + 1 := by omega
    have h2 : i - 1 ≤ i := by omega
    simp only [green, min_eq_right h1, max_eq_left h1,
      min_eq_left h2, max_eq_right h2, min_self, max_self,
      hpred, Nat.cast_add, Nat.cast_one, ite_true]
    field_simp [hN0, hjr, hdiff]
    ring
  · have h1 : j ≤ i + 1 := by omega
    have h2 : j ≤ i - 1 := by omega
    have h3 : j ≤ i := by omega
    have hji : j ≠ i := by omega
    simp only [green, min_eq_right h1, max_eq_left h1,
      min_eq_right h2, max_eq_left h2, min_eq_right h3, max_eq_left h3,
      hpred, Nat.cast_add, Nat.cast_one, ite_eq_right hji]
    ring

/-- Source: ewens2004, sec. 3.4. -/
theorem green_of_lt {N i j : ℕ} (hj0 : 0 < j) (hjN : j < N) (hji : j < i) :
    green N i j = (N : ℝ) * ((N : ℝ) - i) * (1 / ((N : ℝ) - j)) := by
  have hjr : (j : ℝ) ≠ 0 := by positivity
  have hd : (N : ℝ) - j ≠ 0 := by
    have : (j : ℝ) < N := by exact_mod_cast hjN
    linarith
  simp only [green, min_eq_right hji.le, max_eq_left hji.le]
  field_simp [hjr, hd]

/-- Source: ewens2004, sec. 3.4. -/
theorem green_of_le {N i j : ℕ} (hj0 : 0 < j) (hjN : j < N) (hij : i ≤ j) :
    green N i j = (N : ℝ) * i * (1 / (j : ℝ)) := by
  have hjr : (j : ℝ) ≠ 0 := by positivity
  have hd : (N : ℝ) - j ≠ 0 := by
    have : (j : ℝ) < N := by exact_mod_cast hjN
    linarith
  simp only [green, min_eq_left hij, max_eq_right hij]
  field_simp [hjr, hd]

end Rhone.MarkovChain.MoranAbsorptionSupport
