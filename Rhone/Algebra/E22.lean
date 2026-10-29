/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Tower

/-! # The block determinant `E_{2,2}` and its irreducibility -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

noncomputable def E22a : Fuv := uu + 2
noncomputable def E22b : Fuv := (uu + 2) * (3 * uu + 13)
noncomputable def E22c : Fuv := 2 * (uu + 1) * (uu + 3) * (uu + 6)

noncomputable def E22 : P := C E22a * X ^ 2 + C E22b * X + C E22c

noncomputable def T22 : Matrix (Fin 3) (Fin 3) P :=
  !![C (2 * uu) + 12, -8, 0;
     -X, C (2 * uu) + 6 + X, -2;
     0, -2 * X, C (2 * uu) + 2 + 2 * X]

theorem T22_det : T22.det = 4 * E22 := by
  simp [T22, Matrix.det_fin_three, E22, E22a, E22b, E22c, map_add, map_mul, map_ofNat]
  ring

theorem E22a_ne_zero : E22a ≠ 0 := uu_add_two_ne_zero

theorem E22_natDegree : E22.natDegree = 2 := Polynomial.natDegree_quadratic E22a_ne_zero

theorem E22_ne_zero : E22 ≠ 0 := by
  intro h
  have h2 := E22_natDegree
  rw [h, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

noncomputable def B₁ : Polynomial Fv := (X + 2) * (3 * X + 13)

noncomputable def AC₁ : Polynomial Fv := (X + 2) * (2 * (X + 1) * (X + 3) * (X + 6))

theorem map_B₁ : algebraMap (Polynomial Fv) Fuv B₁ = E22b := by
  simp [B₁, E22b, uu, map_ofNat, RatFunc.algebraMap_X]

theorem map_AC₁ : algebraMap (Polynomial Fv) Fuv AC₁ = E22a * E22c := by
  simp only [AC₁, E22a, E22c, uu, map_mul, map_add, map_ofNat, map_one,
    RatFunc.algebraMap_X]

theorem no_int_root (m : ℤ) : m ^ 2 + 48 * m + 336 ≠ 0 := by
  intro h
  have h2 : (m + 24) ^ 2 = 240 := by linear_combination h
  have h3 : (m + 24).natAbs ^ 2 = 240 := by
    have h' := congrArg Int.natAbs h2
    simpa [Int.natAbs_pow] using h'
  rcases Nat.lt_or_ge (m + 24).natAbs 16 with hlt | hge
  · have h4 : (m + 24).natAbs ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [h3] at h4; norm_num at h4
  · have h4 : 16 ^ 2 ≤ (m + 24).natAbs ^ 2 := Nat.pow_le_pow_left hge 2
    rw [h3] at h4; norm_num at h4

theorem E22_no_root (r : Fuv) : ¬ E22.IsRoot r := by
  intro hr
  have hquad : E22a * (r * r) + E22b * r + E22c = 0 := by
    have h := hr
    simp only [Polynomial.IsRoot, E22, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at h
    linear_combination h
  have h1 : (E22a * r) ^ 2 + algebraMap (Polynomial Fv) Fuv B₁ * (E22a * r)
      + algebraMap (Polynomial Fv) Fuv AC₁ = 0 := by
    rw [map_B₁, map_AC₁]
    linear_combination E22a * hquad
  obtain ⟨Y, hY⟩ := descend B₁ AC₁ (E22a * r) h1
  have hB : B₁.eval (1 : Fv) = 48 := by norm_num [B₁]
  have hAC : AC₁.eval (1 : Fv) = 336 := by norm_num [AC₁]
  have h3 : (Y.eval (1 : Fv)) ^ 2
      + algebraMap (Polynomial ℚ) Fv 48 * (Y.eval (1 : Fv))
      + algebraMap (Polynomial ℚ) Fv 336 = 0 := by
    have h := congrArg (Polynomial.eval (1 : Fv)) hY
    simpa [hB, hAC, map_ofNat] using h
  obtain ⟨Z, hZ⟩ := descend (48 : Polynomial ℚ) 336 (Y.eval (1 : Fv)) h3
  have h5 : (Z.eval (0 : ℚ)) ^ 2 + algebraMap ℤ ℚ 48 * (Z.eval (0 : ℚ))
      + algebraMap ℤ ℚ 336 = 0 := by
    have h := congrArg (Polynomial.eval (0 : ℚ)) hZ
    simpa [map_ofNat] using h
  obtain ⟨m, hm⟩ := descend (48 : ℤ) 336 (Z.eval (0 : ℚ)) h5
  exact no_int_root m hm

theorem E22_irreducible : Irreducible E22 := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [E22_natDegree]; decide
  · exact E22_no_root

theorem E22_prime : Prime E22 := E22_irreducible.prime

theorem T22_det_ne_zero : T22.det ≠ 0 := by
  rw [T22_det]
  exact mul_ne_zero (by norm_num) E22_ne_zero

end Rhone.Algebra
