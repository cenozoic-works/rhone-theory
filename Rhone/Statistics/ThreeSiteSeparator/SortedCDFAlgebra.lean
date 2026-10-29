/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.KernelAlgebra

/-! # Symmetry and ordering properties of the sorted CDF of three pattern values -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ThreeSiteSeparator

def below (x a : ℝ) : ℝ := if a ≤ x then 1 else 0

def sortedCDF (x y a b c : ℝ) : ℝ :=
  let hi := max a (max b c)
  let lo := min a (min b c)
  ((if hi ≤ x ∧ lo ≤ y then 1 else 0) +
    (if hi ≤ x ∧ a+b+c-hi-lo ≤ y then 1 else 0))/2

def cdfTripleExpr (x y a b c : ℝ) : ℝ :=
  (below x a*below x b*below y c + below x a*below y b*below x c +
    below y a*below x b*below x c - below y a*below y b*below y c)/2

lemma sortedCDF_swap_first (x y a b c : ℝ) : sortedCDF x y a b c = sortedCDF x y b a c := by
  unfold sortedCDF
  rw [max_left_comm a b c, min_left_comm a b c, add_comm a b]

lemma sortedCDF_swap_last (x y a b c : ℝ) : sortedCDF x y a b c = sortedCDF x y a c b := by
  unfold sortedCDF
  rw [max_comm b c, min_comm b c]
  have he : a+b+c = a+c+b := by ring
  rw [he]

lemma cdfTripleExpr_swap_first (x y a b c : ℝ) :
    cdfTripleExpr x y a b c = cdfTripleExpr x y b a c := by unfold cdfTripleExpr; ring

lemma cdfTripleExpr_swap_last (x y a b c : ℝ) :
    cdfTripleExpr x y a b c = cdfTripleExpr x y a c b := by unfold cdfTripleExpr; ring

lemma sortedCDF_ordered {x y a b c : ℝ} (hyx : y ≤ x) (hab : a ≤ b) (hbc : b ≤ c) :
    sortedCDF x y a b c = cdfTripleExpr x y a b c := by
  have hac := hab.trans hbc
  unfold sortedCDF cdfTripleExpr
  rw [max_eq_right hbc, min_eq_left hbc, max_eq_right hac, min_eq_left hab]
  dsimp only
  rw [show a+b+c-c-a = b by ring]
  by_cases hcx : c ≤ x
  · have hbx := hbc.trans hcx
    have hax := hab.trans hbx
    simp only [hcx, true_and, below, hax, hbx, ite_true, one_mul, mul_one]
    by_cases hcy : c ≤ y
    · have hby := hbc.trans hcy
      have hay := hab.trans hby
      simp [hcy, hby, hay]
    · by_cases hby : b ≤ y
      · have hay := hab.trans hby
        simp [hcy, hby, hay]
      · by_cases hay : a ≤ y <;> simp [hcy, hby, hay]
  · have hcy : ¬c ≤ y := fun h => hcx (h.trans hyx)
    simp [below, hcx, hcy]

theorem sortedCDF_polynomial {x y : ℝ} (hyx : y ≤ x) (a b c : ℝ) :
    sortedCDF x y a b c = cdfTripleExpr x y a b c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact sortedCDF_ordered hyx hab hbc
    · rcases le_total a c with hac | hca
      · rw [sortedCDF_swap_last, cdfTripleExpr_swap_last]
        exact sortedCDF_ordered hyx hac hcb
      · rw [sortedCDF_swap_last, cdfTripleExpr_swap_last,
          sortedCDF_swap_first, cdfTripleExpr_swap_first]
        exact sortedCDF_ordered hyx hca hab
  · rcases le_total a c with hac | hca
    · rw [sortedCDF_swap_first, cdfTripleExpr_swap_first]
      exact sortedCDF_ordered hyx hba hac
    · rcases le_total b c with hbc | hcb
      · rw [sortedCDF_swap_first, cdfTripleExpr_swap_first,
          sortedCDF_swap_last, cdfTripleExpr_swap_last]
        exact sortedCDF_ordered hyx hbc hca
      · rw [sortedCDF_swap_first, cdfTripleExpr_swap_first,
          sortedCDF_swap_last, cdfTripleExpr_swap_last,
          sortedCDF_swap_first, cdfTripleExpr_swap_first]
        exact sortedCDF_ordered hyx hcb hba

lemma below_max (x a b : ℝ) : below x (max a b) = below x a*below x b := by
  unfold below
  simp only [max_le_iff]
  by_cases ha : a ≤ x <;> by_cases hb : b ≤ x <;> simp [ha, hb]

lemma middle_le_high (a b c : ℝ) :
    a+b+c-max a (max b c)-min a (min b c) ≤ max a (max b c) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma sortedCDF_above {x y : ℝ} (hxy : x ≤ y) (a b c : ℝ) :
    sortedCDF x y a b c = below x a*below x b*below x c := by
  have he : sortedCDF x y a b c = below x (max a (max b c)) := by
    by_cases hx : max a (max b c) ≤ x
    · have hlo : min a (min b c) ≤ y :=
        (min_le_left a _).trans ((le_max_left a _).trans (hx.trans hxy))
      have hmid := (middle_le_high a b c).trans (hx.trans hxy)
      simp [sortedCDF, below, hx, hlo, hmid]
    · simp [sortedCDF, below, hx]
  rw [he, below_max, below_max]
  ring

end Rhone.Statistics.ThreeSiteSeparator
