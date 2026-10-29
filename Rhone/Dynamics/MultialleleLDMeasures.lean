/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.MultialleleLD
public import Rhone.Dynamics.LDMeasures

/-!
# Entrywise signed Lewontin normalization for finite allele arrays

Source: lewontin1964, pp. 54–55. -/

@[expose] public section
namespace Rhone.Dynamics.MultialleleLD
open Finset

/-- Source: lewontin1964, pp. 54–55. -/
noncomputable def indicatorGametes {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (a : A) (b : B) : Rhone.Dynamics.Gametes ℝ :=
  ⟨x a b, row x a - x a b, col x b - x a b,
    1 - row x a - col x b + x a b⟩

/-- Source: lewontin1964, pp. 54–55. -/
noncomputable def normalizedLD {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (a : A) (b : B) : ℝ :=
  Rhone.Dynamics.Gametes.lewontinD' (row x a) (col x b) (ld x a b)

/-- Source: lewontin1964, pp. 54–55. -/
theorem indicator_gametes_distribution
    {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (a : A) (b : B)
    (hx : ∀ i j, 0 ≤ x i j) (ht : ∑ i, ∑ j, x i j = 1) :
    (indicatorGametes x a b).IsDist := by
  classical
  have hr : row x a = x a b + ∑ j ∈ univ.erase b, x a j := by
    rw [row, ← sum_erase_add _ _ (mem_univ b)]
    ring
  have hc : col x b = x a b + ∑ i ∈ univ.erase a, x i b := by
    rw [col, ← sum_erase_add _ _ (mem_univ a)]
    ring
  have ht' : (∑ i, ∑ j, x i j) = row x a +
      ∑ i ∈ univ.erase a, x i b +
      ∑ i ∈ univ.erase a, ∑ j ∈ univ.erase b, x i j := by
    rw [← sum_erase_add (f := fun i => ∑ j, x i j) _ (mem_univ a)]
    simp_rw [← sum_erase_add (f := fun j => x _ j) _ (mem_univ b)]
    simp only [sum_add_distrib]
    rw [hr]
    ring
  constructor
  · exact hx a b
  · change 0 ≤ row x a - x a b
    rw [hr]
    have : 0 ≤ ∑ j ∈ univ.erase b, x a j := sum_nonneg fun j _ => hx a j
    linarith
  · change 0 ≤ col x b - x a b
    rw [hc]
    have : 0 ≤ ∑ i ∈ univ.erase a, x i b := sum_nonneg fun i _ => hx i b
    linarith
  · change 0 ≤ 1 - row x a - col x b + x a b
    rw [ht] at ht'
    have : 0 ≤ ∑ i ∈ univ.erase a, ∑ j ∈ univ.erase b, x i j :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => hx i j
    linarith [hc]
  · simp only [indicatorGametes, Gametes.total]
    ring

/-- Source: lewontin1964, pp. 54–55. -/
theorem normalized_ld_abs_le_one
    {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (a : A) (b : B)
    (hx : ∀ i j, 0 ≤ x i j) (ht : ∑ i, ∑ j, x i j = 1) :
    |normalizedLD x a b| ≤ 1 := by
  have h := Gametes.abs_lewontinD'_le_one (indicator_gametes_distribution x a b hx ht)
  have hD : (indicatorGametes x a b).D = ld x a b := by
    simp only [indicatorGametes, Gametes.D, ld]
    ring
  have hA : (indicatorGametes x a b).pA = row x a := by
    simp [indicatorGametes, Gametes.pA]
  have hB : (indicatorGametes x a b).pB = col x b := by
    simp [indicatorGametes, Gametes.pB]
  simpa only [normalizedLD, hD, hA, hB] using h

/-- Source: lewontin1964, pp. 50, 54–55. -/
theorem normalized_ld_recombine
    {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ℝ) (a : A) (b : B) (c : ℝ)
    (ht : ∑ i, ∑ j, x i j = 1) (hc : c ≤ 1) :
    normalizedLD (recombine c x) a b = (1-c)*normalizedLD x a b := by
  unfold normalizedLD
  rw [row_recombine c x ht, col_recombine c x ht, ld_recombine c x ht]
  exact Gametes.lewontinD'_mul (sub_nonneg.mpr hc)

end Rhone.Dynamics.MultialleleLD
