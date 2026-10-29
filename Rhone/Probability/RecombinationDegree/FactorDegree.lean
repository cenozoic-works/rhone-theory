/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Tactic

/-! # Degree deficits of factors, for the recombination-degree transfer -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [NoZeroDivisors R]

theorem degreeOf_eq_totalDegree_of_dvd {P F : MvPolynomial σ R} (x : σ)
    (hP : P ≠ 0) (hF : F ∣ P) (hx : P.degreeOf x = P.totalDegree) :
    F.degreeOf x = F.totalDegree := by
  obtain ⟨G, rfl⟩ := hF
  have hf : F ≠ 0 := left_ne_zero_of_mul hP
  have hg : G ≠ 0 := right_ne_zero_of_mul hP
  rw [degreeOf_mul_eq hf hg, totalDegree_mul_of_isDomain hf hg] at hx
  have := degreeOf_le_totalDegree F x
  have := degreeOf_le_totalDegree G x
  omega

theorem factor_degree_deficit_le {P F : MvPolynomial σ R} (y : σ) (d : ℕ)
    (hP : P ≠ 0) (hF : F ∣ P) (hy : P.totalDegree ≤ P.degreeOf y + d) :
    F.totalDegree ≤ F.degreeOf y + d := by
  obtain ⟨G, rfl⟩ := hF
  have hf : F ≠ 0 := left_ne_zero_of_mul hP
  have hg : G ≠ 0 := right_ne_zero_of_mul hP
  rw [degreeOf_mul_eq hf hg, totalDegree_mul_of_isDomain hf hg] at hy
  have := degreeOf_le_totalDegree G y
  omega

theorem factor_degree_transfer {P F : MvPolynomial σ R} (x y : σ) (d : ℕ)
    (hP : P ≠ 0) (hF : F ∣ P) (hy : P.totalDegree ≤ P.degreeOf y + d) :
    F.degreeOf x ≤ F.degreeOf y + d :=
  (degreeOf_le_totalDegree F x).trans (factor_degree_deficit_le y d hP hF hy)

theorem factor_degree_gt {P F : MvPolynomial σ R} (x y : σ) (D d : ℕ)
    (hP : P ≠ 0) (hF : F ∣ P) (hy : P.totalDegree ≤ P.degreeOf y + d)
    (hx : D + d < F.degreeOf x) : D < F.degreeOf y := by
  have := factor_degree_transfer x y d hP hF hy
  omega

end Rhone.Probability.RecombinationDegree
