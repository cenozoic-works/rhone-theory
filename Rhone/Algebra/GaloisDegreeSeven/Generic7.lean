/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisDegreeSeven.E77
public import Mathlib.FieldTheory.RatFunc.Basic

/-! # The generic statement at `m = 7`: `Ẽ₇` is irreducible over `ℚ(u)` -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial

theorem E77gen_lc_ne_zero : (35280 * Polynomial.X + 423360 : Polynomial ℚ) ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
  simp at this

theorem natDegree_E77gen : E77gen.natDegree = 7 := by
  rw [E77gen_eq]
  compute_degree!
  exact E77gen_lc_ne_zero

theorem leadingCoeff_E77gen :
    E77gen.leadingCoeff = 35280 * Polynomial.X + 423360 := by
  rw [Polynomial.leadingCoeff, natDegree_E77gen, E77gen_coeff7]

theorem isPrimitive_of_coeff7_of_coeff0 (P : Polynomial (Polynomial ℚ))
    (h7c : P.coeff 7 = 35280 * Polynomial.X + 423360)
    (h0c : (P.coeff 0).eval (-12 : ℚ) = -745612148736) : P.IsPrimitive := by
  intro r hr
  by_contra hru
  rw [C_dvd_iff_dvd_coeff] at hr
  have he : (C (1 / 35280 : ℚ)) * (35280 * Polynomial.X + 423360)
      = (Polynomial.X - C (-12 : ℚ)) := by
    rw [show ((35280 : Polynomial ℚ)) = C (35280 : ℚ) from (map_ofNat C 35280).symm,
      show ((423360 : Polynomial ℚ)) = C (423360 : ℚ) from (map_ofNat C 423360).symm,
      mul_add, ← mul_assoc, ← C_mul, ← C_mul, map_neg, sub_neg_eq_add]
    norm_num
  have hd : r ∣ 35280 * Polynomial.X + 423360 := by
    have h1 := hr 7
    rw [h7c] at h1
    exact h1
  have h7 : r ∣ (Polynomial.X - C (-12 : ℚ)) := by
    have hd' := hd.mul_left (C (1 / 35280 : ℚ))
    rwa [he] at hd'
  obtain ⟨t, ht⟩ := h7
  rcases (irreducible_X_sub_C (-12 : ℚ)).isUnit_or_isUnit ht with h | h
  · exact hru h
  · obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp h
    have hdvd : (Polynomial.X - C (-12 : ℚ)) ∣ r := ⟨w, by rw [ht, mul_assoc, hw, mul_one]⟩
    have hcn : (Polynomial.X - C (-12 : ℚ)) ∣ P.coeff 0 := hdvd.trans (hr 0)
    have hroot : (P.coeff 0).eval (-12 : ℚ) = 0 := dvd_iff_isRoot.mp hcn
    rw [h0c] at hroot
    norm_num at hroot

theorem E77gen_isPrimitive : E77gen.IsPrimitive :=
  isPrimitive_of_coeff7_of_coeff0 E77gen E77gen_coeff7 E77gen_coeff0_at_bad

theorem E77gen_lc_spec_ne_zero :
    (Polynomial.evalRingHom (-88 / 7 : ℚ)) E77gen.leadingCoeff ≠ 0 := by
  rw [leadingCoeff_E77gen]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_ofNat, eval_X]
  norm_num

theorem E77gen_irreducible : Irreducible E77gen :=
  irreducible_of_specialization (Polynomial.evalRingHom (-88 / 7 : ℚ)) E77gen_isPrimitive
    E77gen_lc_spec_ne_zero (by rw [E77gen_map_spec]; exact E77pt_irreducible)

theorem E77gen_irreducible_ratFunc :
    Irreducible (E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) :=
  irreducible_ratFunc_of_specialization (Polynomial.evalRingHom (-88 / 7 : ℚ))
    E77gen_isPrimitive E77gen_lc_spec_ne_zero
    (by rw [E77gen_map_spec]; exact E77pt_irreducible)

end Rhone.Algebra.GaloisDegreeSeven
