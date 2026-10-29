/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Tower

/-! # The class `E₁` contains the ESF idiom -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

theorem uu_add_vv_add_ratCast_ne_zero (k : ℚ) : uu + vv + (k : Fuv) ≠ 0 := by
  have h := uu_add_ne_zero ((RatFunc.X : Fv) + (k : Fv))
  rwa [map_add, map_ratCast, ← add_assoc] at h

theorem uu_sub_vv_add_ratCast_ne_zero (k : ℚ) : uu - vv + (k : Fuv) ≠ 0 := by
  have h := uu_add_ne_zero (-(RatFunc.X : Fv) + (k : Fv))
  rwa [map_add, map_neg, map_ratCast, ← add_assoc, ← sub_eq_add_neg] at h

theorem thA_coeff_ne_zero (k : ℚ) : (uu + vv) / 2 + (k : Fuv) ≠ 0 := by
  intro h
  refine uu_add_vv_add_ratCast_ne_zero (2 * k) ?_
  have h2 : uu + vv + ((2 * k : ℚ) : Fuv) = 2 * ((uu + vv) / 2 + (k : Fuv)) := by
    push_cast; ring
  rw [h2, h, mul_zero]

theorem thB_coeff_ne_zero (k : ℚ) : (uu - vv) / 2 + (k : Fuv) ≠ 0 := by
  intro h
  refine uu_sub_vv_add_ratCast_ne_zero (2 * k) ?_
  have h2 : uu - vv + ((2 * k : ℚ) : Fuv) = 2 * ((uu - vv) / 2 + (k : Fuv)) := by
    push_cast; ring
  rw [h2, h, mul_zero]

theorem algebraMap_C_eq (x : Fuv) : algebraMap P L (C x) = algebraMap Fuv L x := by
  rw [RatFunc.algebraMap_C]; rfl

theorem eval_thA_add (k : ℚ) :
    Expr.eval thA thB rhoL (.add .thA (.const k))
      = algebraMap P L (C ((uu + vv) / 2 + (k : Fuv))) := by
  rw [algebraMap_C_eq, map_add, map_ratCast]; rfl

theorem eval_thB_add (k : ℚ) :
    Expr.eval thA thB rhoL (.add .thB (.const k))
      = algebraMap P L (C ((uu - vv) / 2 + (k : Fuv))) := by
  rw [algebraMap_C_eq, map_add, map_ratCast]; rfl

theorem eval_rho_add (k : ℚ) :
    Expr.eval thA thB rhoL (.add .rho (.const k)) = algebraMap P L (X + C (k : Fuv)) := by
  rw [map_add, RatFunc.algebraMap_X, algebraMap_C_eq, map_ratCast]; rfl

theorem dadm_div_thA_add {x : Expr Fuv} (hx : DAdm thA thB rhoL 1 x) (k : ℚ) :
    DAdm thA thB rhoL 1 (.div x (.add .thA (.const k))) :=
  .div hx (.add .thA (.const k)) (C ((uu + vv) / 2 + (k : Fuv)))
    (fun h => thA_coeff_ne_zero k (Polynomial.C_eq_zero.mp h))
    (by rw [Polynomial.natDegree_C]; exact Nat.zero_le 1) (eval_thA_add k)

theorem dadm_div_thB_add {x : Expr Fuv} (hx : DAdm thA thB rhoL 1 x) (k : ℚ) :
    DAdm thA thB rhoL 1 (.div x (.add .thB (.const k))) :=
  .div hx (.add .thB (.const k)) (C ((uu - vv) / 2 + (k : Fuv)))
    (fun h => thB_coeff_ne_zero k (Polynomial.C_eq_zero.mp h))
    (by rw [Polynomial.natDegree_C]; exact Nat.zero_le 1) (eval_thB_add k)

theorem dadm_div_rho_add {x : Expr Fuv} (hx : DAdm thA thB rhoL 1 x) (k : ℚ) :
    DAdm thA thB rhoL 1 (.div x (.add .rho (.const k))) :=
  .div hx (.add .rho (.const k)) (X + C (k : Fuv))
    (Polynomial.X_add_C_ne_zero _)
    (le_of_eq (Polynomial.natDegree_X_add_C _)) (eval_rho_add k)

noncomputable def pochA (m : ℕ) : Expr Fuv :=
  Expr.finsetProd (Finset.range m) fun r => .add .thA (.const (r : ℚ))

theorem dadm_pochA (m : ℕ) : DAdm thA thB rhoL 1 (pochA m) :=
  DAdm.finsetProd fun _ _ => .add .thA (.const _)

theorem eval_pochA (m : ℕ) :
    Expr.eval thA thB rhoL (pochA m)
      = algebraMap P L (C (∏ r ∈ Finset.range m, ((uu + vv) / 2 + ((r : ℚ) : Fuv)))) := by
  rw [pochA, Expr.eval_finsetProd, algebraMap_C_eq, map_prod]
  exact Finset.prod_congr rfl fun r _ => by
    rw [← algebraMap_C_eq, ← eval_thA_add (r : ℚ)]

theorem pochA_coeff_ne_zero (m : ℕ) :
    (∏ r ∈ Finset.range m, ((uu + vv) / 2 + ((r : ℚ) : Fuv))) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r _ => thA_coeff_ne_zero (r : ℚ)

theorem dadm_recip_pochA (m : ℕ) :
    DAdm thA thB rhoL 1 (.div (.const 1) (pochA m)) :=
  .div (.const 1) (dadm_pochA m)
    (C (∏ r ∈ Finset.range m, ((uu + vv) / 2 + ((r : ℚ) : Fuv))))
    (fun h => pochA_coeff_ne_zero m (Polynomial.C_eq_zero.mp h))
    (by rw [Polynomial.natDegree_C]; exact Nat.zero_le 1) (eval_pochA m)

end Rhone.Algebra
