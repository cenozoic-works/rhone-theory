/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.Basic
public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Prime

/-! # Numeric input of the Galois obstruction (generated) -/

@[expose] public section

namespace Rhone.Algebra.Galois

open Polynomial LinearAlgebra.Tridiag

section Universal

variable {R : Type*} [CommRing R]

theorem E_two_two_s (a b ρ s : R) (hs : a * 2 + b * 2 = s) :
    E R 2 2 a b ρ =
      (2 * s + 8) * ρ ^ 2
      + (3 * s ^ 2 + 38 * s + 104) * ρ
      + (s ^ 3 + 20 * s ^ 2 + 108 * s + 144) := by
  subst hs
  rw [E_eq_cont]
  simp [cont, dcoef, bcoef, ccoef]
  ring

theorem E_three_three_s (a b ρ s : R) (hs : a * 3 + b * 3 = s) :
    E R 3 3 a b ρ =
      (6 * s + 72) * ρ ^ 3
      + (11 * s ^ 2 + 354 * s + 2664) * ρ ^ 2
      + (6 * s ^ 3 + 306 * s ^ 2 + 4812 * s + 23184) * ρ
      + (s ^ 4 + 68 * s ^ 3 + 1572 * s ^ 2 + 14400 * s + 43200) := by
  subst hs
  rw [E_eq_cont]
  simp [cont, dcoef, bcoef, ccoef]
  ring

theorem E_five_five_s (a b ρ s : R) (hs : a * 5 + b * 5 = s) :
    E R 5 5 a b ρ =
      (120 * s + 4800) * ρ ^ 5
      + (274 * s ^ 2 + 26720 * s + 630400) * ρ ^ 4
      + (225 * s ^ 3 + 34658 * s ^ 2 + 1725640 * s + 27780800) * ρ ^ 3
      + (85 * s ^ 4 + 17730 * s ^ 3 + 1339728 * s ^ 2 + 43408640 * s + 508172800) * ρ ^ 2
      + (15 * s ^ 5 + 3910 * s ^ 4 + 391956 * s ^ 3 + 18842552 * s ^ 2 + 433277280 * s
          + 3801888000) * ρ
      + (s ^ 6 + 310 * s ^ 5 + 38308 * s ^ 4 + 2407464 * s ^ 3 + 80868960 * s ^ 2
          + 1371686400 * s + 9144576000) := by
  subst hs
  rw [E_eq_cont]
  simp [cont, dcoef, bcoef, ccoef]
  ring

end Universal

section Points

def thA22 : ℚ := -3

def thB22 : ℚ := 1 / 2

noncomputable def E22pt : ℚ[X] := E ℚ[X] 2 2 (C thA22) (C thB22) X

theorem hs22 : (C thA22 : ℚ[X]) * 2 + (C thB22 : ℚ[X]) * 2 = -5 := by
  rw [show ((-5 : ℚ[X])) = C (-5 : ℚ) by rw [map_neg, map_ofNat],
    show ((2 : ℚ[X])) = C (2 : ℚ) from (map_ofNat C 2).symm,
    ← C_mul, ← C_mul, ← C_add, C_inj, thA22, thB22]
  norm_num

theorem E22pt_eq : E22pt = -2 * X ^ 2 - 11 * X - 21 := by
  rw [E22pt, E_two_two_s (C thA22) (C thB22) X (-5) hs22]
  ring

noncomputable def G22 : ℤ[X] := -2 * X ^ 2 - 11 * X - 21

theorem G22_map_rat : G22.map (Int.castRingHom ℚ) = -2 * X ^ 2 - 11 * X - 21 := by
  simp [G22, Polynomial.map_ofNat]

theorem E22pt_eq_map : E22pt = G22.map (Int.castRingHom ℚ) := by
  rw [E22pt_eq, G22_map_rat]

theorem G22_coeff_fst : G22.coeff 2 = -2 := by
  simp [G22, coeff_X_pow, coeff_X]

theorem G22_coeff_snd : G22.coeff 1 = -11 := by
  simp [G22, coeff_X_pow, coeff_X]

theorem G22_bezout : (-2 : ℤ) * (5) + (-11 : ℤ) * (-1) = 1 := by norm_num

theorem G22_isPrimitive : G22.IsPrimitive :=
  isPrimitive_of_bezout (i := 2) (j := 1) (u := 5) (v := -1)
    (by rw [G22_coeff_fst, G22_coeff_snd]; exact G22_bezout)

def thA33 : ℚ := -5

def thB33 : ℚ := 2 / 3

noncomputable def E33pt : ℚ[X] := E ℚ[X] 3 3 (C thA33) (C thB33) X

theorem hs33 : (C thA33 : ℚ[X]) * 3 + (C thB33 : ℚ[X]) * 3 = -13 := by
  rw [show ((-13 : ℚ[X])) = C (-13 : ℚ) by rw [map_neg, map_ofNat],
    show ((3 : ℚ[X])) = C (3 : ℚ) from (map_ofNat C 3).symm,
    ← C_mul, ← C_mul, ← C_add, C_inj, thA33, thB33]
  norm_num

theorem E33pt_eq : E33pt = -6 * X ^ 3 - 79 * X ^ 2 - 840 * X + 833 := by
  rw [E33pt, E_three_three_s (C thA33) (C thB33) X (-13) hs33]
  ring

noncomputable def G33 : ℤ[X] := -6 * X ^ 3 - 79 * X ^ 2 - 840 * X + 833

theorem G33_map_rat : G33.map (Int.castRingHom ℚ) = -6 * X ^ 3 - 79 * X ^ 2 - 840 * X
    + 833 := by
  simp [G33, Polynomial.map_ofNat]

theorem E33pt_eq_map : E33pt = G33.map (Int.castRingHom ℚ) := by
  rw [E33pt_eq, G33_map_rat]

theorem G33_coeff_fst : G33.coeff 3 = -6 := by
  simp [G33, coeff_X_pow, coeff_X]

theorem G33_coeff_snd : G33.coeff 2 = -79 := by
  simp [G33, coeff_X_pow, coeff_X]

theorem G33_bezout : (-6 : ℤ) * (13) + (-79 : ℤ) * (-1) = 1 := by norm_num

theorem G33_isPrimitive : G33.IsPrimitive :=
  isPrimitive_of_bezout (i := 3) (j := 2) (u := 13) (v := -1)
    (by rw [G33_coeff_fst, G33_coeff_snd]; exact G33_bezout)

instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

noncomputable def F11 : (ZMod 11)[X] := -6 * X ^ 3 - 2 * X ^ 2 - 4 * X + 8

theorem G33_map11 : G33.map (Int.castRingHom (ZMod 11)) = F11 := by
  have e79 : ((79 : (ZMod 11)[X])) = 2 := by
    rw [← map_ofNat C 79, ← map_ofNat C 2, C_inj]; decide
  have e840 : ((840 : (ZMod 11)[X])) = 4 := by
    rw [← map_ofNat C 840, ← map_ofNat C 4, C_inj]; decide
  have e833 : ((833 : (ZMod 11)[X])) = 8 := by
    rw [← map_ofNat C 833, ← map_ofNat C 8, C_inj]; decide
  simp only [G33, F11, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_neg]
  rw [e79, e840, e833]

theorem F11_no_root (x : ZMod 11) : F11.eval x ≠ 0 := by
  revert x
  simp only [F11, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat,
    eval_neg]
  decide

def thA55 : ℚ := -9

def thB55 : ℚ := 2 / 5

noncomputable def E55pt : ℚ[X] := E ℚ[X] 5 5 (C thA55) (C thB55) X

theorem hs55 : (C thA55 : ℚ[X]) * 5 + (C thB55 : ℚ[X]) * 5 = -43 := by
  rw [show ((-43 : ℚ[X])) = C (-43 : ℚ) by rw [map_neg, map_ofNat],
    show ((5 : ℚ[X])) = C (5 : ℚ) from (map_ofNat C 5).symm,
    ← C_mul, ← C_mul, ← C_add, C_inj, thA55, thB55]
  norm_num

theorem E55pt_eq : E55pt = -360 * X ^ 5 - 11934 * X ^ 4 - 228153 * X ^ 3 - 302673 * X ^ 2
    + 9983181 * X - 5297981 := by
  rw [E55pt, E_five_five_s (C thA55) (C thB55) X (-43) hs55]
  ring

noncomputable def G55 : ℤ[X] := -360 * X ^ 5 - 11934 * X ^ 4 - 228153 * X ^ 3
    - 302673 * X ^ 2 + 9983181 * X - 5297981

theorem G55_map_rat : G55.map (Int.castRingHom ℚ) = -360 * X ^ 5 - 11934 * X ^ 4
    - 228153 * X ^ 3 - 302673 * X ^ 2 + 9983181 * X - 5297981 := by
  simp [G55, Polynomial.map_ofNat]

theorem E55pt_eq_map : E55pt = G55.map (Int.castRingHom ℚ) := by
  rw [E55pt_eq, G55_map_rat]

theorem G55_coeff_fst : G55.coeff 5 = -360 := by
  simp [G55, coeff_X_pow, coeff_X]

theorem G55_coeff_snd : G55.coeff 0 = -5297981 := by
  simp [G55, coeff_X_pow, coeff_X]

theorem G55_bezout : (-360 : ℤ) * (1486378) + (-5297981 : ℤ) * (-101) = 1 := by norm_num

theorem G55_isPrimitive : G55.IsPrimitive :=
  isPrimitive_of_bezout (i := 5) (j := 0) (u := 1486378) (v := -101)
    (by rw [G55_coeff_fst, G55_coeff_snd]; exact G55_bezout)

instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

noncomputable def F7 : (ZMod 7)[X] := -3 * X ^ 5 - 6 * X ^ 4 - 2 * X ^ 3 + 5 * X - 3

theorem G55_map7 : G55.map (Int.castRingHom (ZMod 7)) = F7 := by
  have e360 : ((360 : (ZMod 7)[X])) = 3 := by
    rw [← map_ofNat C 360, ← map_ofNat C 3, C_inj]; decide
  have e11934 : ((11934 : (ZMod 7)[X])) = 6 := by
    rw [← map_ofNat C 11934, ← map_ofNat C 6, C_inj]; decide
  have e228153 : ((228153 : (ZMod 7)[X])) = 2 := by
    rw [← map_ofNat C 228153, ← map_ofNat C 2, C_inj]; decide
  have e302673 : ((302673 : (ZMod 7)[X])) = 0 := by
    rw [← map_ofNat C 302673, ← C_0, C_inj]; decide
  have e9983181 : ((9983181 : (ZMod 7)[X])) = 5 := by
    rw [← map_ofNat C 9983181, ← map_ofNat C 5, C_inj]; decide
  have e5297981 : ((5297981 : (ZMod 7)[X])) = 3 := by
    rw [← map_ofNat C 5297981, ← map_ofNat C 3, C_inj]; decide
  simp only [G55, F7, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_neg]
  rw [e360, e11934, e228153, e302673, e9983181, e5297981]
  ring

theorem F7_no_root (x : ZMod 7) : F7.eval x ≠ 0 := by
  revert x
  simp only [F7, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat,
    eval_neg]
  decide

theorem F7_rem_ne (b c : ZMod 7) :
    -3 * b ^ 4 + 6 * b ^ 3 + 9 * b ^ 2 * c - 2 * b ^ 2 - 12 * b * c - 3 * c ^ 2 + 2 * c
      + 5 ≠ 0 ∨
    -3 * b ^ 3 * c + 6 * b ^ 2 * c + 6 * b * c ^ 2 - 2 * b * c - 6 * c ^ 2 - 3 ≠ 0 := by
  revert b c
  decide

noncomputable def S7 (b c : ZMod 7) : (ZMod 7)[X] :=
  C (-3) * X ^ 3
    + C (3 * b - 6) * X ^ 2
    + C (-3 * b ^ 2 + 6 * b + 3 * c - 2) * X
    + C (3 * b ^ 3 - 6 * b ^ 2 - 6 * b * c + 2 * b + 6 * c)

theorem F7_div (b c : ZMod 7) :
    F7 = (X ^ 2 + C b * X + C c) * S7 b c
      + C (-3 * b ^ 4 + 6 * b ^ 3 + 9 * b ^ 2 * c - 2 * b ^ 2 - 12 * b * c - 3 * c ^ 2
          + 2 * c + 5) * X
      + C (-3 * b ^ 3 * c + 6 * b ^ 2 * c + 6 * b * c ^ 2 - 2 * b * c - 6 * c ^ 2 - 3) := by
  simp only [F7, S7, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_neg]
  ring

def thA55pos : ℚ := 1

def thB55pos : ℚ := 1

noncomputable def E55pospt : ℚ[X] := E ℚ[X] 5 5 (C thA55pos) (C thB55pos) X

theorem hs55pos : (C thA55pos : ℚ[X]) * 5 + (C thB55pos : ℚ[X]) * 5 = 10 := by
  rw [show ((10 : ℚ[X])) = C (10 : ℚ) from (map_ofNat C 10).symm,
    show ((5 : ℚ[X])) = C (5 : ℚ) from (map_ofNat C 5).symm,
    ← C_mul, ← C_mul, ← C_add, C_inj, thA55pos, thB55pos]
  norm_num

theorem E55pospt_eq : E55pospt = 6000 * X ^ 5 + 925000 * X ^ 4 + 48728000 * X ^ 3
    + 1094812000 * X ^ 2 + 10451472000 * X + 33770880000 := by
  rw [E55pospt, E_five_five_s (C thA55pos) (C thB55pos) X (10) hs55pos]
  ring

noncomputable def G55pos : ℤ[X] := 6 * X ^ 5 + 925 * X ^ 4 + 48728 * X ^ 3 + 1094812 * X ^ 2
    + 10451472 * X + 33770880

theorem G55pos_map_rat : G55pos.map (Int.castRingHom ℚ) = 6 * X ^ 5 + 925 * X ^ 4
    + 48728 * X ^ 3 + 1094812 * X ^ 2 + 10451472 * X + 33770880 := by
  simp [G55pos, Polynomial.map_ofNat]

theorem E55pospt_eq_map :
    E55pospt = C (1000 : ℚ) * G55pos.map (Int.castRingHom ℚ) := by
  rw [E55pospt_eq, G55pos_map_rat]
  simp only [map_ofNat]
  ring

theorem G55pos_coeff_fst : G55pos.coeff 5 = 6 := by
  simp [G55pos, coeff_X_pow, coeff_X]

theorem G55pos_coeff_snd : G55pos.coeff 4 = 925 := by
  simp [G55pos, coeff_X_pow, coeff_X]

theorem G55pos_bezout : (6 : ℤ) * (-154) + (925 : ℤ) * (1) = 1 := by norm_num

theorem G55pos_isPrimitive : G55pos.IsPrimitive :=
  isPrimitive_of_bezout (i := 5) (j := 4) (u := -154) (v := 1)
    (by rw [G55pos_coeff_fst, G55pos_coeff_snd]; exact G55pos_bezout)

instance factPrime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

noncomputable def F17 : (ZMod 17)[X] := 6 * X ^ 5 + 7 * X ^ 4 + 6 * X ^ 3 + 12 * X ^ 2
    + 8 * X + 6

theorem G55pos_map17 : G55pos.map (Int.castRingHom (ZMod 17)) = F17 := by
  have e925 : ((925 : (ZMod 17)[X])) = 7 := by
    rw [← map_ofNat C 925, ← map_ofNat C 7, C_inj]; decide
  have e48728 : ((48728 : (ZMod 17)[X])) = 6 := by
    rw [← map_ofNat C 48728, ← map_ofNat C 6, C_inj]; decide
  have e1094812 : ((1094812 : (ZMod 17)[X])) = 12 := by
    rw [← map_ofNat C 1094812, ← map_ofNat C 12, C_inj]; decide
  have e10451472 : ((10451472 : (ZMod 17)[X])) = 8 := by
    rw [← map_ofNat C 10451472, ← map_ofNat C 8, C_inj]; decide
  have e33770880 : ((33770880 : (ZMod 17)[X])) = 6 := by
    rw [← map_ofNat C 33770880, ← map_ofNat C 6, C_inj]; decide
  simp only [G55pos, F17, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_X]
  rw [e925, e48728, e1094812, e10451472, e33770880]

theorem F17_no_root (x : ZMod 17) : F17.eval x ≠ 0 := by
  revert x
  simp only [F17, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

theorem F17_rem_ne (b c : ZMod 17) :
    6 * b ^ 4 - 7 * b ^ 3 - 18 * b ^ 2 * c + 6 * b ^ 2 + 14 * b * c + 6 * c ^ 2 - 12 * b
      - 6 * c + 8 ≠ 0 ∨
    6 * b ^ 3 * c - 7 * b ^ 2 * c - 12 * b * c ^ 2 + 6 * b * c + 7 * c ^ 2 - 12 * c
      + 6 ≠ 0 := by
  revert b c
  decide

noncomputable def S17 (b c : ZMod 17) : (ZMod 17)[X] :=
  C (6) * X ^ 3
    + C (-6 * b + 7) * X ^ 2
    + C (6 * b ^ 2 - 7 * b - 6 * c + 6) * X
    + C (-6 * b ^ 3 + 7 * b ^ 2 + 12 * b * c - 6 * b - 7 * c + 12)

theorem F17_div (b c : ZMod 17) :
    F17 = (X ^ 2 + C b * X + C c) * S17 b c
      + C (6 * b ^ 4 - 7 * b ^ 3 - 18 * b ^ 2 * c + 6 * b ^ 2 + 14 * b * c + 6 * c ^ 2
          - 12 * b - 6 * c + 8) * X
      + C (6 * b ^ 3 * c - 7 * b ^ 2 * c - 12 * b * c ^ 2 + 6 * b * c + 7 * c ^ 2 - 12 * c
          + 6) := by
  simp only [F17, S17, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_neg]
  ring

end Points

section Generic

noncomputable def E55gen : (Polynomial ℚ)[X] :=
  E ((Polynomial ℚ)[X]) 5 5 (C (Polynomial.X : Polynomial ℚ)) 0 X

theorem hsgen :
    (C (Polynomial.X : Polynomial ℚ) : (Polynomial ℚ)[X]) * 5 + 0 * 5
      = C (5 * Polynomial.X : Polynomial ℚ) := by
  rw [zero_mul, add_zero, show ((5 : (Polynomial ℚ)[X])) = C (5 : Polynomial ℚ) from
    (map_ofNat C 5).symm, ← C_mul]
  ring_nf

theorem E55gen_eq : E55gen =
    C (600 * Polynomial.X + 4800) * X ^ 5
    + C (6850 * Polynomial.X ^ 2 + 133600 * Polynomial.X + 630400) * X ^ 4
    + C (28125 * Polynomial.X ^ 3 + 866450 * Polynomial.X ^ 2 + 8628200 * Polynomial.X
        + 27780800) * X ^ 3
    + C (53125 * Polynomial.X ^ 4 + 2216250 * Polynomial.X ^ 3 + 33493200 * Polynomial.X ^ 2
        + 217043200 * Polynomial.X + 508172800) * X ^ 2
    + C (46875 * Polynomial.X ^ 5 + 2443750 * Polynomial.X ^ 4 + 48994500 * Polynomial.X ^ 3
        + 471063800 * Polynomial.X ^ 2 + 2166386400 * Polynomial.X + 3801888000) * X
    + C (15625 * Polynomial.X ^ 6 + 968750 * Polynomial.X ^ 5 + 23942500 * Polynomial.X ^ 4
        + 300933000 * Polynomial.X ^ 3 + 2021724000 * Polynomial.X ^ 2
        + 6858432000 * Polynomial.X + 9144576000) := by
  rw [E55gen, E_five_five_s (C (Polynomial.X : Polynomial ℚ)) 0 X
    (C (5 * Polynomial.X : Polynomial ℚ)) hsgen]
  simp only [map_add, map_mul, map_ofNat, map_pow]
  ring

theorem E55gen_coeff5 : E55gen.coeff 5 = 600 * Polynomial.X + 4800 := by
  rw [E55gen_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem E55gen_coeff0 : E55gen.coeff 0 = 15625 * Polynomial.X ^ 6
    + 968750 * Polynomial.X ^ 5 + 23942500 * Polynomial.X ^ 4 + 300933000 * Polynomial.X ^ 3
    + 2021724000 * Polynomial.X ^ 2 + 6858432000 * Polynomial.X + 9144576000 := by
  rw [E55gen_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

end Generic

end Rhone.Algebra.Galois
