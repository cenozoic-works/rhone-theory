/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GenericField.E22

/-! # The coefficient field `ℚ(π_A, π_B)` and the nonvanishing lemmas over it -/

@[expose] public section

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

variable (K : Type*) [Field K]

theorem uu_add_vv_ne_zero : GenericField.uu K + GenericField.vv K ≠ 0 := GenericField.uu_add_ne_zero
    K _

theorem uu_sub_vv_ne_zero : GenericField.uu K - GenericField.vv K ≠ 0 := by
  have := GenericField.uu_add_ne_zero K (-RatFunc.X : GenericField.Fv K)
  simpa [GenericField.vv, sub_eq_add_neg] using this

theorem uu_add_vv_add_two_ne_zero : GenericField.uu K + GenericField.vv K + 2 ≠ 0 := by
  have := GenericField.uu_add_ne_zero K (RatFunc.X + 2 : GenericField.Fv K)
  simpa [GenericField.vv, add_assoc, map_ofNat] using this

theorem uu_sub_vv_add_two_ne_zero : GenericField.uu K - GenericField.vv K + 2 ≠ 0 := by
  have := GenericField.uu_add_ne_zero K (-RatFunc.X + 2 : GenericField.Fv K)
  simpa [GenericField.vv, sub_eq_add_neg, add_assoc, map_ofNat] using this

noncomputable def kToFuv : K →+* GenericField.Fuv K :=
  (algebraMap (GenericField.Fv K) (GenericField.Fuv K)).comp (algebraMap K (GenericField.Fv K))

theorem kToFuv_injective : Function.Injective (kToFuv K) := (kToFuv K).injective

variable {K}

theorem kToFuv_ne_zero {x : K} (hx : x ≠ 0) : kToFuv K x ≠ 0 := by
  intro h
  exact hx (kToFuv_injective K (by rw [h, map_zero]))

theorem kToFuv_sub_one_ne_zero {x : K} (hx : x - 1 ≠ 0) : kToFuv K x - 1 ≠ 0 := by
  intro h
  refine hx (kToFuv_injective K ?_)
  rw [map_sub, map_one, map_zero, h]

theorem ratFunc_X_sub_one_ne_zero (F : Type*) [Field F] : (RatFunc.X : RatFunc F) - 1 ≠ 0 := by
  have h : algebraMap (Polynomial F) (RatFunc F) (X - C 1) = RatFunc.X - 1 := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_one]
  rw [← h]
  exact _root_.Rhone.Algebra.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)

abbrev Kpi : Type := RatFunc (RatFunc ℚ)

theorem two_ne_zero_Kpi : (2 : Kpi) ≠ 0 :=
  GenericField.two_ne_zero_ratFunc _ (GenericField.two_ne_zero_ratFunc ℚ (by norm_num))

noncomputable def piA : Kpi := algebraMap (RatFunc ℚ) Kpi RatFunc.X

noncomputable def piB : Kpi := RatFunc.X

noncomputable def piA2 : Kpi := 1 - piA

noncomputable def piB2 : Kpi := 1 - piB

theorem inner_ne_zero {x : RatFunc ℚ} (hx : x ≠ 0) : algebraMap (RatFunc ℚ) Kpi x ≠ 0 :=
  fun h => hx ((algebraMap (RatFunc ℚ) Kpi).injective (by rw [h, map_zero]))

theorem piA_ne_zero : piA ≠ 0 := inner_ne_zero RatFunc.X_ne_zero

theorem piB_ne_zero : piB ≠ 0 := RatFunc.X_ne_zero

theorem piA_sub_one_ne_zero : piA - 1 ≠ 0 := by
  have h : piA - 1 = algebraMap (RatFunc ℚ) Kpi (RatFunc.X - 1) := by
    rw [map_sub, map_one]; rfl
  rw [h]
  exact inner_ne_zero (ratFunc_X_sub_one_ne_zero ℚ)

theorem piB_sub_one_ne_zero : piB - 1 ≠ 0 := ratFunc_X_sub_one_ne_zero (RatFunc ℚ)

noncomputable def piAF : GenericField.Fuv Kpi := kToFuv Kpi piA

noncomputable def piBF : GenericField.Fuv Kpi := kToFuv Kpi piB

theorem piAF_ne_zero : piAF ≠ 0 := kToFuv_ne_zero piA_ne_zero
theorem piBF_ne_zero : piBF ≠ 0 := kToFuv_ne_zero piB_ne_zero
theorem piAF_sub_one_ne_zero : piAF - 1 ≠ 0 := kToFuv_sub_one_ne_zero piA_sub_one_ne_zero
theorem piBF_sub_one_ne_zero : piBF - 1 ≠ 0 := kToFuv_sub_one_ne_zero piB_sub_one_ne_zero

end Rhone.Algebra.SymbolicFrequencies
