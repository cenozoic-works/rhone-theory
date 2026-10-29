/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisDegreeSeven.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

/-! # A primitive quartic irreducible modulo 7 -/

@[expose] public section

namespace Rhone.Algebra.DiagonalIrreducibility
open Polynomial

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

noncomputable def quartic : Polynomial ℤ := 3 * X^4 + 86 * X^3 + 863 * X^2 + 3576 * X + 5136

noncomputable def modSeven : Polynomial (ZMod 7) := 3 * X^4 + 2 * X^3 + 2 * X^2 + 6 * X + 5

theorem quartic_degree : quartic.natDegree = 4 := by unfold quartic; compute_degree!
theorem modSeven_degree : modSeven.natDegree = 4 := by unfold modSeven; compute_degree!

theorem quartic_primitive : quartic.IsPrimitive := by
  apply Rhone.Algebra.Galois.isPrimitive_of_bezout (i := 4) (j := 2) (u := -575) (v := 2)
  norm_num [quartic, coeff_X_pow, coeff_X, coeff_C]

theorem quartic_map : quartic.map (Int.castRingHom (ZMod 7)) = modSeven := by
  have e86 : (86 : (ZMod 7)[X]) = 2 := by
    rw [← map_ofNat C 86, ← map_ofNat C 2, C_inj]; decide
  have e863 : (863 : (ZMod 7)[X]) = 2 := by
    rw [← map_ofNat C 863, ← map_ofNat C 2, C_inj]; decide
  have e3576 : (3576 : (ZMod 7)[X]) = 6 := by
    rw [← map_ofNat C 3576, ← map_ofNat C 6, C_inj]; decide
  have e5136 : (5136 : (ZMod 7)[X]) = 5 := by
    rw [← map_ofNat C 5136, ← map_ofNat C 5, C_inj]; decide
  simp only [quartic, modSeven, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat]
  rw [e86, e863, e3576, e5136]

theorem modSeven_no_root (z : ZMod 7) : modSeven.eval z ≠ 0 := by
  revert z
  simp only [modSeven, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

theorem modSeven_div (b c : ZMod 7) :
    modSeven = (X^2 + C b * X + C c) *
      (3 * X^2 + C (2 - 3*b) * X + C (2 - 2*b + 3*b^2 - 3*c)) +
      C (6 - (2 - 3*b)*c - b*(2 - 2*b + 3*b^2 - 3*c)) * X +
      C (5 - c*(2 - 2*b + 3*b^2 - 3*c)) := by
  unfold modSeven
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem modSeven_no_quad (b c : ZMod 7) : ¬ (X^2 + C b * X + C c ∣ modSeven) := by
  apply Rhone.Algebra.Galois.not_dvd_of_rem_pair (modSeven_div b c) (by compute_degree!)
  revert b c
  decide

theorem modSeven_irreducible : Irreducible modSeven := by
  have h0 : modSeven ≠ 0 := by intro h; simpa [h] using modSeven_degree
  have hu : ¬ IsUnit modSeven := by
    intro h
    have := natDegree_eq_zero_of_isUnit h
    rw [modSeven_degree] at this
    contradiction
  rw [irreducible_iff_lt_natDegree_lt h0 hu]
  intro q hq hd hdiv
  rw [modSeven_degree] at hd
  simp only [Finset.mem_Ioc] at hd
  rcases (show q.natDegree = 1 ∨ q.natDegree = 2 by omega) with h | h
  · exact Rhone.Algebra.GaloisDegreeSeven.no_monic_dvd_one modSeven_no_root q hq h hdiv
  · exact Rhone.Algebra.GaloisDegreeSeven.no_monic_dvd_two modSeven_no_quad q hq h hdiv

theorem quartic_irreducible : Irreducible quartic := by
  apply Rhone.Algebra.Galois.irreducible_of_map_of_isPrimitive
    (Int.castRingHom (ZMod 7)) quartic_primitive
  · rw [quartic_map, modSeven_degree, quartic_degree]
  · rw [quartic_map]; exact modSeven_irreducible

theorem quartic_rat_irreducible : Irreducible (quartic.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast quartic_primitive).mp
    quartic_irreducible

end Rhone.Algebra.DiagonalIrreducibility
