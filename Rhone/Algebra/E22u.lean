/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.E22

/-! # `Ẽ₂` read as a cubic in `u`, and its irreducibility over `ℚ(v, ρ)` -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

noncomputable abbrev rhoM : Fuv := uu

theorem descend3 {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K] (b c d : A) (x : K)
    (hx : x ^ 3 + algebraMap A K b * x ^ 2 + algebraMap A K c * x + algebraMap A K d = 0) :
    ∃ y : A, y ^ 3 + b * y ^ 2 + c * y + d = 0 := by
  have hmonic : (X ^ 3 + (C b * X ^ 2 + C c * X + C d) : Polynomial A).Monic := by
    apply Polynomial.monic_X_pow_add
    exact lt_of_le_of_lt Polynomial.degree_quadratic_le (by norm_num)
  have hint : IsIntegral A x := by
    refine ⟨X ^ 3 + (C b * X ^ 2 + C c * X + C d), hmonic, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    linear_combination hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  apply IsFractionRing.injective A K
  rw [map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hy, map_zero]
  exact hx

noncomputable def E22u : P :=
  C 2 * X ^ 3 + C (3 * rhoM + 20) * X ^ 2 + C (rhoM ^ 2 + 19 * rhoM + 54) * X
    + C (2 * rhoM ^ 2 + 26 * rhoM + 36)

theorem E22u_natDegree : E22u.natDegree = 3 :=
  Polynomial.natDegree_cubic (by norm_num)

theorem E22u_ne_zero : E22u ≠ 0 := by
  intro h
  have h2 := E22u_natDegree
  rw [h, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

noncomputable def B₂ : Polynomial Fv := 3 * X + 20
noncomputable def C₂ : Polynomial Fv := 2 * (X ^ 2 + 19 * X + 54)
noncomputable def D₂ : Polynomial Fv := 4 * (2 * X ^ 2 + 26 * X + 36)

theorem map_B₂ : algebraMap (Polynomial Fv) Fuv B₂ = 3 * rhoM + 20 := by
  simp [B₂, uu, map_ofNat, RatFunc.algebraMap_X]

theorem map_C₂ : algebraMap (Polynomial Fv) Fuv C₂ = 2 * (rhoM ^ 2 + 19 * rhoM + 54) := by
  simp [C₂, uu, map_ofNat, RatFunc.algebraMap_X]

theorem map_D₂ : algebraMap (Polynomial Fv) Fuv D₂ = 4 * (2 * rhoM ^ 2 + 26 * rhoM + 36) := by
  simp [D₂, uu, map_ofNat, RatFunc.algebraMap_X]

theorem no_int_root_cubic (m : ℤ) : m ^ 3 + 23 * m ^ 2 + 148 * m + 256 ≠ 0 := by
  intro h
  have h7 : ((m : ZMod 7) ^ 3 + 23 * (m : ZMod 7) ^ 2 + 148 * (m : ZMod 7) + 256) = 0 := by
    have h' := congrArg (fun z : ℤ => (z : ZMod 7)) h
    push_cast at h'
    exact h'
  revert h7
  have hall : ∀ x : ZMod 7, x ^ 3 + 23 * x ^ 2 + 148 * x + 256 ≠ 0 := by decide
  exact hall _

theorem E22u_no_root (r : Fuv) : ¬ E22u.IsRoot r := by
  intro hr
  have hcub : 2 * r ^ 3 + (3 * rhoM + 20) * r ^ 2 + (rhoM ^ 2 + 19 * rhoM + 54) * r
      + (2 * rhoM ^ 2 + 26 * rhoM + 36) = 0 := by
    have h := hr
    simp only [Polynomial.IsRoot, E22u, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at h
    linear_combination h
  have h1 : (2 * r) ^ 3 + algebraMap (Polynomial Fv) Fuv B₂ * (2 * r) ^ 2
      + algebraMap (Polynomial Fv) Fuv C₂ * (2 * r)
      + algebraMap (Polynomial Fv) Fuv D₂ = 0 := by
    rw [map_B₂, map_C₂, map_D₂]
    linear_combination 4 * hcub
  obtain ⟨Y, hY⟩ := descend3 B₂ C₂ D₂ (2 * r) h1
  have hB : B₂.eval (1 : Fv) = 23 := by norm_num [B₂]
  have hC : C₂.eval (1 : Fv) = 148 := by norm_num [C₂]
  have hD : D₂.eval (1 : Fv) = 256 := by norm_num [D₂]
  have h3 : (Y.eval (1 : Fv)) ^ 3
      + algebraMap (Polynomial ℚ) Fv 23 * (Y.eval (1 : Fv)) ^ 2
      + algebraMap (Polynomial ℚ) Fv 148 * (Y.eval (1 : Fv))
      + algebraMap (Polynomial ℚ) Fv 256 = 0 := by
    have h := congrArg (Polynomial.eval (1 : Fv)) hY
    simpa [hB, hC, hD, map_ofNat] using h
  obtain ⟨Z, hZ⟩ := descend3 (23 : Polynomial ℚ) 148 256 (Y.eval (1 : Fv)) h3
  have h5 : (Z.eval (0 : ℚ)) ^ 3 + algebraMap ℤ ℚ 23 * (Z.eval (0 : ℚ)) ^ 2
      + algebraMap ℤ ℚ 148 * (Z.eval (0 : ℚ)) + algebraMap ℤ ℚ 256 = 0 := by
    have h := congrArg (Polynomial.eval (0 : ℚ)) hZ
    simpa [map_ofNat] using h
  obtain ⟨m, hm⟩ := descend3 (23 : ℤ) 148 256 (Z.eval (0 : ℚ)) h5
  exact no_int_root_cubic m hm

theorem E22u_irreducible : Irreducible E22u := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [E22u_natDegree]; decide
  · exact E22u_no_root

theorem E22u_prime : Prime E22u := E22u_irreducible.prime

theorem middle_monic_quadratic_ne_zero (b c : Fv) :
    uu ^ 2 + algebraMap Fv Fuv b * uu + algebraMap Fv Fuv c ≠ 0 := by
  have hm : (X ^ 2 + (C b * X + C c) : Polynomial Fv).Monic :=
    Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))
  have h : algebraMap (Polynomial Fv) Fuv (X ^ 2 + (C b * X + C c))
      = uu ^ 2 + algebraMap Fv Fuv b * uu + algebraMap Fv Fuv c := by
    simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, uu]
    exact (add_assoc _ _ _).symm
  rw [← h]
  exact algebraMap_ne_zero hm.ne_zero

end Rhone.Algebra
