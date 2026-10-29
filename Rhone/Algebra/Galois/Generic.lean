/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.E55
public import Mathlib.FieldTheory.RatFunc.Basic

/-! # The generic statement: `E_{5,5}` is irreducible over `ℚ(θ_A, θ_B)` -/

@[expose] public section

namespace Rhone.Algebra.Galois

open Polynomial

theorem E55gen_lc_ne_zero : (600 * Polynomial.X + 4800 : Polynomial ℚ) ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
  simp at this

theorem E55gen_natDegree : E55gen.natDegree = 5 := by
  rw [E55gen_eq]
  compute_degree!
  exact E55gen_lc_ne_zero

set_option maxRecDepth 8000 in
theorem E55gen_isPrimitive : E55gen.IsPrimitive := by
  intro r hr
  by_contra hru
  rw [C_dvd_iff_dvd_coeff] at hr
  have he : (C (1 / 600 : ℚ)) * (600 * Polynomial.X + 4800)
      = (Polynomial.X - C (-8 : ℚ)) := by
    rw [show ((600 : Polynomial ℚ)) = C (600 : ℚ) from (map_ofNat C 600).symm,
      show ((4800 : Polynomial ℚ)) = C (4800 : ℚ) from (map_ofNat C 4800).symm,
      mul_add, ← mul_assoc, ← C_mul, ← C_mul, map_neg, sub_neg_eq_add]
    norm_num
  have h5 : r ∣ (Polynomial.X - C (-8 : ℚ)) := by
    have hd := (hr 5).mul_left (C (1 / 600 : ℚ))
    rw [E55gen_coeff5, he] at hd
    exact hd
  obtain ⟨t, ht⟩ := h5
  rcases (irreducible_X_sub_C (-8 : ℚ)).isUnit_or_isUnit ht with h | h
  · exact hru h
  · obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp h
    have hdvd : (Polynomial.X - C (-8 : ℚ)) ∣ r := ⟨w, by rw [ht, mul_assoc, hw, mul_one]⟩
    have hz : E55gen.map (Polynomial.evalRingHom (-8 : ℚ)) = 0 := by
      ext n
      rw [coeff_map, coeff_zero]
      have hcn : (Polynomial.X - C (-8 : ℚ)) ∣ E55gen.coeff n := hdvd.trans (hr n)
      simpa using dvd_iff_isRoot.mp hcn
    have h0 : (E55gen.map (Polynomial.evalRingHom (-8 : ℚ))).coeff 0 = 10240000 := by
      rw [coeff_map, E55gen_coeff0]
      simp
      norm_num
    rw [hz] at h0
    norm_num at h0

theorem E55gen_map_spec :
    E55gen.map (Polynomial.evalRingHom (-43 / 5 : ℚ)) = E55pt := by
  rw [E55gen_eq, E55pt_eq]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, coe_evalRingHom, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  norm_num [map_ofNat]
  ring

theorem E55gen_irreducible : Irreducible E55gen := by
  refine irreducible_of_map_of_isPrimitive (Polynomial.evalRingHom (-43 / 5 : ℚ))
    E55gen_isPrimitive ?_ ?_
  · rw [E55gen_map_spec, natDegree_E55pt, E55gen_natDegree]
  · rw [E55gen_map_spec]; exact E55pt_irreducible

theorem E55gen_irreducible_ratFunc :
    Irreducible (E55gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) :=
  (E55gen_isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp E55gen_irreducible

end Rhone.Algebra.Galois
