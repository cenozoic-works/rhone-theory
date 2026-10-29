/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SiteScores

/-! # Five equality categories for a full labelled four-state site -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcretePatternMoments
open ThreeTipSites ThreeSiteSeparator SingleSiteChannel

abbrev Row := Fin 5 × Fin 5 × Fin 5

def category (x : Triple 4) : Fin 5 :=
  if x.1 = x.2.1 ∧ x.1 = x.2.2 then 0 else if x.1 = x.2.1 then 1
  else if x.1 = x.2.2 then 2 else if x.2.1 = x.2.2 then 3 else 4

def orientCategory (q : Fin 3) (i : Fin 5) : Fin 5 :=
  if q = 0 then i else if q = 1 then ![0, 2, 3, 1, 4] i else ![0, 3, 1, 2, 4] i

def single (i : Fin 5) (A B C : ℝ) : ℝ :=
  ![(1 + 3 * A + 6 * B + 6 * C) / 64, (1 + 3 * A - 2 * B - 2 * C) / 64,
    (1 - A + 2 * B - 2 * C) / 64, (1 - A + 2 * B - 2 * C) / 64,
    (1 - A - 2 * B + 2 * C) / 64] i

theorem category_orientation (q : Fin 3) (x : Triple 4) :
    category (orientation 4 q x) = orientCategory q (category x) := by
  rcases x with ⟨a, b, c⟩
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c
  all_goals fin_cases q <;> simp_all [category, orientation, cycle, orientCategory, eq_comm]

theorem pattern_mass_category (A B C : ℝ) (x : Triple 4) :
    patternMass 4 A B C x.1 x.2.1 x.2.2 = single (category x) A B C := by
  rcases x with ⟨a, b, c⟩
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c
  all_goals simp_all [patternMass, category, single, eq_comm]
  all_goals ring

theorem site_category (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) (x : Triple 4) :
    site 4 (fun _ => 1 / 4) k t (orientation 4 q x) =
      single (orientCategory q (category x)) (Real.exp (-k * t.1))
        (Real.exp (-k * (t.1 + t.2))) (secondMomentKernel k t) := by
  have h := site_patternMass (K := 4) (by norm_num) k t
    (orientation 4 q x).1 (orientation 4 q x).2.1 (orientation 4 q x).2.2
  rw [pattern_mass_category, category_orientation] at h
  exact h

def rowOf (x : Panel 4 3) : Row := (category (x 0), category (x 1), category (x 2))

def rowPolynomial (r : Row) (X Y : ℝ) : ℝ :=
  (∑ q : Fin 3, single (orientCategory q r.1) (X ^ 2) (Y ^ 2) (X * Y ^ 2) *
    single (orientCategory q r.2.1) (X ^ 2) (Y ^ 2) (X * Y ^ 2) *
    single (orientCategory q r.2.2) (X ^ 2) (Y ^ 2) (X * Y ^ 2)) / 3

end Rhone.Statistics.ConcretePatternMoments
