/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BoundedDenominator

/-! # The ambient tower, and the integral-closure descent lemma -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

abbrev Fv := RatFunc ℚ
abbrev Fuv := RatFunc Fv
abbrev P := Polynomial Fuv
abbrev L := RatFunc Fuv

theorem descend {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K] (b c : A) (x : K)
    (hx : x ^ 2 + algebraMap A K b * x + algebraMap A K c = 0) :
    ∃ y : A, y ^ 2 + b * y + c = 0 := by
  have hmonic : (X ^ 2 + (C b * X + C c) : Polynomial A).Monic := by
    apply Polynomial.monic_X_pow_add
    exact lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num)
  have hint : IsIntegral A x := by
    refine ⟨X ^ 2 + (C b * X + C c), hmonic, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    linear_combination hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  apply IsFractionRing.injective A K
  rw [map_add, map_add, map_mul, map_pow, hy, map_zero]
  exact hx

noncomputable def uu : Fuv := RatFunc.X

noncomputable def vv : Fuv := algebraMap Fv Fuv RatFunc.X

theorem uu_add_ne_zero (c : Fv) : uu + algebraMap Fv Fuv c ≠ 0 := by
  have h : algebraMap (Polynomial Fv) Fuv (X + C c) = uu + algebraMap Fv Fuv c := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]; rfl
  rw [← h]
  exact algebraMap_ne_zero (Polynomial.X_add_C_ne_zero c)

theorem uu_add_two_ne_zero : uu + 2 ≠ 0 := by
  have := uu_add_ne_zero (2 : Fv); simpa [map_ofNat] using this

theorem uu_add_vv_ne_zero : uu + vv ≠ 0 := uu_add_ne_zero _

theorem uu_sub_vv_ne_zero : uu - vv ≠ 0 := by
  have := uu_add_ne_zero (-RatFunc.X : Fv)
  simpa [vv, sub_eq_add_neg] using this

theorem uu_add_vv_add_two_ne_zero : uu + vv + 2 ≠ 0 := by
  have := uu_add_ne_zero (RatFunc.X + 2 : Fv)
  simpa [vv, add_assoc, map_ofNat] using this

theorem uu_sub_vv_add_two_ne_zero : uu - vv + 2 ≠ 0 := by
  have := uu_add_ne_zero (-RatFunc.X + 2 : Fv)
  simpa [vv, sub_eq_add_neg, add_assoc, map_ofNat] using this

noncomputable def thA : L := algebraMap Fuv L ((uu + vv) / 2)
noncomputable def thB : L := algebraMap Fuv L ((uu - vv) / 2)
noncomputable def rhoL : L := RatFunc.X

theorem boundedDen_thA (D : ℕ) : BoundedDen D thA := boundedDen_coeff D _
theorem boundedDen_thB (D : ℕ) : BoundedDen D thB := boundedDen_coeff D _

theorem boundedDen_rhoL (D : ℕ) : BoundedDen D rhoL := by
  have : rhoL = algebraMap P L X := (RatFunc.algebraMap_X).symm
  rw [this]; exact boundedDen_of_poly D _

end Rhone.Algebra
