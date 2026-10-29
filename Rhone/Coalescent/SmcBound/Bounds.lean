/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcBound.Race

/-! # Explicit two-split count bounds and their quadratic coefficient -/
@[expose] public section
noncomputable section
namespace Rhone.Coalescent.SmcBound

def doubleBound (R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - hazard R n) * doubleBound R n +
      hazard R n * raceBound (hazard R) (n + 2)

def quadraticCoefficient : ℕ → ℝ
  | 0 => 0
  | n + 1 => quadraticCoefficient n + harmonic (n + 2) / ((n : ℝ) + 1)

theorem quadraticCoefficient_sum (n : ℕ) :
    quadraticCoefficient n =
      ∑ j ∈ Finset.range n, harmonic (j + 2) / ((j : ℝ) + 1) := by
  induction n with
  | zero => simp [quadraticCoefficient]
  | succ n ih => rw [quadraticCoefficient, Finset.sum_range_succ, ih]

theorem doubleBound_nonneg (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ doubleBound R n := by
  induction n with
  | zero => simp [doubleBound]
  | succ n ih =>
    have hh := hazard_bounds R hR n
    have hb := (raceBound_nonneg_le_one (hazard R) (hazard_bounds R hR) (n + 2)).1
    simp only [doubleBound]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hh.2) ih) (mul_nonneg hh.1 hb)

theorem doubleBound_le_one (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    doubleBound R n ≤ 1 := by
  induction n with
  | zero => simp [doubleBound]
  | succ n ih =>
    have hh := hazard_bounds R hR n
    have hb := (raceBound_nonneg_le_one (hazard R) (hazard_bounds R hR) (n + 2)).2
    have hp := mul_nonneg (sub_nonneg.mpr hh.2) (sub_nonneg.mpr ih)
    have hq := mul_nonneg hh.1 (sub_nonneg.mpr hb)
    simp only [doubleBound]
    nlinarith

theorem doubleBound_quadratic (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    doubleBound R n ≤ R ^ 2 * quadraticCoefficient n := by
  induction n with
  | zero => simp [doubleBound, quadraticCoefficient]
  | succ n ih =>
    have hd := doubleBound_nonneg R hR n
    have hh := hazard_bounds R hR n
    have hb := (raceBound_nonneg_le_one (hazard R) (hazard_bounds R hR) (n + 2)).1
    have hprod := mul_le_mul (hazard_le_linear R hR n)
      (second_race_bound R hR (n + 2)) hb
      (mul_nonneg hR (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1)))
    calc
      doubleBound R (n + 1) ≤ doubleBound R n +
          (R * (1 / ((n : ℝ) + 1))) * (R * harmonic (n + 2)) := by
        simp only [doubleBound]
        have hdrop : (1 - hazard R n) * doubleBound R n ≤ doubleBound R n := by
          nlinarith [mul_nonneg hh.1 hd]
        exact add_le_add hdrop hprod
      _ ≤ R ^ 2 * quadraticCoefficient n +
          (R * (1 / ((n : ℝ) + 1))) * (R * harmonic (n + 2)) :=
        add_le_add ih le_rfl
      _ = R ^ 2 * quadraticCoefficient (n + 1) := by
        simp only [quadraticCoefficient]
        ring

theorem harmonic_mono : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [harmonic]
  have hp : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem quadraticCoefficient_le_harmonic_product (n : ℕ) :
    quadraticCoefficient n ≤ harmonic n * harmonic (n + 1) := by
  induction n with
  | zero => simp [quadraticCoefficient, harmonic]
  | succ n ih =>
    have hm : harmonic (n + 1) ≤ harmonic (n + 2) :=
      harmonic_mono (Nat.le_succ (n + 1))
    have hp := mul_le_mul_of_nonneg_left hm (harmonic_nonneg n)
    calc
      quadraticCoefficient (n + 1) ≤ harmonic n * harmonic (n + 2) +
          harmonic (n + 2) / ((n : ℝ) + 1) := by
        simp only [quadraticCoefficient]
        exact add_le_add (ih.trans hp) le_rfl
      _ = harmonic (n + 1) * harmonic (n + 2) := by
        simp only [harmonic]
        ring

theorem doubleBound_harmonic_product (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    doubleBound R n ≤ R ^ 2 * harmonic n * harmonic (n + 1) := by
  calc
    doubleBound R n ≤ R ^ 2 * quadraticCoefficient n := doubleBound_quadratic R hR n
    _ ≤ R ^ 2 * (harmonic n * harmonic (n + 1)) :=
      mul_le_mul_of_nonneg_left (quadraticCoefficient_le_harmonic_product n) (sq_nonneg R)
    _ = R ^ 2 * harmonic n * harmonic (n + 1) := by ring

def harmonicSquare : ℕ → ℝ
  | 0 => 0
  | n + 1 => harmonicSquare n + 1 / (((n : ℝ) + 1) ^ 2)

theorem quadraticCoefficient_closed (n : ℕ) :
    quadraticCoefficient n =
      (harmonic n ^ 2 + harmonicSquare n) / 2 + 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [quadraticCoefficient, harmonic, harmonicSquare]
  | succ n ih =>
    rw [quadraticCoefficient, ih]
    simp only [harmonic, harmonicSquare, Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [h1, h2]
    ring

theorem hazard_survival (R : ℝ) (hR : 0 ≤ R) (j : ℕ) :
    1 - hazard R j = ((j : ℝ) + 1) / ((j : ℝ) + 1 + R) := by
  unfold hazard
  have hd : (j : ℝ) + 1 + R ≠ 0 := ne_of_gt (by positivity)
  field_simp [hd]
  ring

theorem raceBound_hazard_product (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    raceBound (hazard R) n =
      1 - ∏ j ∈ Finset.range n, ((j : ℝ) + 1) / ((j : ℝ) + 1 + R) := by
  have hp := raceBound_product (hazard R) n
  have he : (∏ j ∈ Finset.range n, (1 - hazard R j)) =
      ∏ j ∈ Finset.range n, ((j : ℝ) + 1) / ((j : ℝ) + 1 + R) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hazard_survival R hR j
  rw [he] at hp
  linarith

theorem doubleBound_le_min (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    doubleBound R n ≤ min 1 (R ^ 2 * quadraticCoefficient n) := by
  exact le_min (doubleBound_le_one R hR n) (doubleBound_quadratic R hR n)

end Rhone.Coalescent.SmcBound
