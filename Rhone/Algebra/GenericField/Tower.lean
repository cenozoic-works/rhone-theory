/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Tower

/-! # The tower over an arbitrary coefficient field -/

@[expose] public section

namespace Rhone.Algebra.GenericField

open Polynomial

abbrev Fv (K : Type*) [Field K] := RatFunc K
abbrev Fuv (K : Type*) [Field K] := RatFunc (Fv K)
abbrev P (K : Type*) [Field K] := Polynomial (Fuv K)
abbrev L (K : Type*) [Field K] := RatFunc (Fuv K)

variable (K : Type*) [Field K]

noncomputable def uu : Fuv K := RatFunc.X

noncomputable def vv : Fuv K := algebraMap (Fv K) (Fuv K) RatFunc.X

noncomputable def thA : L K := algebraMap (Fuv K) (L K) ((uu K + vv K) / 2)

noncomputable def thB : L K := algebraMap (Fuv K) (L K) ((uu K - vv K) / 2)

noncomputable def rhoL : L K := RatFunc.X

theorem uu_rat : uu ℚ = _root_.Rhone.Algebra.uu := rfl
theorem vv_rat : vv ℚ = _root_.Rhone.Algebra.vv := rfl
theorem thA_rat : thA ℚ = _root_.Rhone.Algebra.thA := rfl
theorem thB_rat : thB ℚ = _root_.Rhone.Algebra.thB := rfl
theorem rhoL_rat : rhoL ℚ = _root_.Rhone.Algebra.rhoL := rfl

theorem uu_add_ne_zero (c : Fv K) : uu K + algebraMap (Fv K) (Fuv K) c ≠ 0 := by
  have h : algebraMap (Polynomial (Fv K)) (Fuv K) (X + C c)
      = uu K + algebraMap (Fv K) (Fuv K) c := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]; rfl
  rw [← h]
  exact _root_.Rhone.Algebra.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero c)

theorem uu_add_two_ne_zero : uu K + 2 ≠ 0 := by
  have := uu_add_ne_zero K (2 : Fv K); simpa [map_ofNat] using this

theorem boundedDen_thA (D : ℕ) : _root_.Rhone.Algebra.BoundedDen D (thA K) :=
  _root_.Rhone.Algebra.boundedDen_coeff D _

theorem boundedDen_thB (D : ℕ) : _root_.Rhone.Algebra.BoundedDen D (thB K) :=
  _root_.Rhone.Algebra.boundedDen_coeff D _

theorem boundedDen_rhoL (D : ℕ) : _root_.Rhone.Algebra.BoundedDen D (rhoL K) := by
  have h : rhoL K = algebraMap (P K) (L K) X := (RatFunc.algebraMap_X).symm
  rw [h]; exact _root_.Rhone.Algebra.boundedDen_of_poly D _

end Rhone.Algebra.GenericField
