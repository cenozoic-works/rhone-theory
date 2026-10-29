/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.Basic
public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Prime

/-! # Numeric input of the `m = 7` Galois computation (generated) -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial LinearAlgebra.Tridiag

section Universal

variable {R : Type*} [CommRing R]

set_option maxRecDepth 20000 in
theorem E_seven_seven_s (a b ρ s : R) (hs : a * 7 + b * 7 = s) :
    E R 7 7 a b ρ =
      (5040 * s + 423360) * ρ ^ 7
      + (13068 * s ^ 2 + 2583504 * s + 124806528) * ρ ^ 6
      + (13132 * s ^ 3 + 4086792 * s ^ 2 + 415976400 * s + 13853439936) * ρ ^ 5
      + (6769 * s ^ 4 + 2863404 * s ^ 3 + 445291452 * s ^ 2 + 30167634672 * s
          + 751179840768) * ρ ^ 4
      + (1960 * s ^ 5 + 1043196 * s ^ 4 + 217330464 * s ^ 3 + 22141116144 * s ^ 2
          + 1102464381312 * s + 21451318608384) * ρ ^ 3
      + (322 * s ^ 6 + 205548 * s ^ 5 + 53389716 * s ^ 4 + 7216583840 * s ^ 3
          + 534906581328 * s ^ 2 + 20595604776768 * s + 321509264380416) * ρ ^ 2
      + (28 * s ^ 7 + 20748 * s ^ 6 + 6421128 * s ^ 5 + 1074706400 * s ^ 4
          + 104940412512 * s ^ 3 + 5971222911168 * s ^ 2 + 183108462485760 * s
          + 2331552477284352) * ρ
      + (s ^ 8 + 840 * s ^ 7 + 300216 * s ^ 6 + 59549408 * s ^ 5 + 7160537424 * s ^ 4
          + 533762786304 * s ^ 3 + 24054423918336 * s ^ 2 + 598391790796800 * s
          + 6283113803366400) := by
  subst hs
  rw [E_eq_cont]
  simp [cont, dcoef, bcoef, ccoef]
  ring

end Universal

section Point

def thA77 : ℚ := -13

def thB77 : ℚ := 3 / 7

noncomputable def E77pt : ℚ[X] := E ℚ[X] 7 7 (C thA77) (C thB77) X

theorem hs77 : (C thA77 : ℚ[X]) * 7 + (C thB77 : ℚ[X]) * 7 = -88 := by
  rw [show ((-88 : ℚ[X])) = C (-88 : ℚ) by rw [map_neg, map_ofNat],
    show ((7 : ℚ[X])) = C (7 : ℚ) from (map_ofNat C 7).symm,
    ← C_mul, ← C_mul, ← C_add, C_inj, thA77, thB77]
  norm_num

theorem E77pt_eq : E77pt = -20160 * X ^ 7 - 1343232 * X ^ 6 - 53456320 * X ^ 5
    - 630867584 * X ^ 4 + 7065016832 * X ^ 3 + 64998508544 * X ^ 2 - 328200347648 * X
    - 291453927424 := by
  rw [E77pt, E_seven_seven_s (C thA77) (C thB77) X (-88) hs77]
  ring

noncomputable def G77 : ℤ[X] := 315 * X ^ 7 + 20988 * X ^ 6 + 835255 * X ^ 5
    + 9857306 * X ^ 4 - 110390888 * X ^ 3 - 1015601696 * X ^ 2 + 5128130432 * X + 4553967616

theorem G77_map_rat : G77.map (Int.castRingHom ℚ) = 315 * X ^ 7 + 20988 * X ^ 6
    + 835255 * X ^ 5 + 9857306 * X ^ 4 - 110390888 * X ^ 3 - 1015601696 * X ^ 2
    + 5128130432 * X + 4553967616 := by
  simp [G77, Polynomial.map_ofNat]

theorem E77pt_eq_map :
    E77pt = C (-64 : ℚ) * G77.map (Int.castRingHom ℚ) := by
  rw [E77pt_eq, G77_map_rat]
  simp only [map_neg, map_ofNat]
  ring

theorem G77_coeff_fst : G77.coeff 7 = 315 := by
  simp [G77, coeff_X_pow, coeff_X]

theorem G77_coeff_snd : G77.coeff 4 = 9857306 := by
  simp [G77, coeff_X_pow, coeff_X]

theorem G77_bezout : (315 : ℤ) * (-2691201) + (9857306 : ℤ) * (86) = 1 := by norm_num

theorem G77_isPrimitive : G77.IsPrimitive :=
  Rhone.Algebra.Galois.isPrimitive_of_bezout (i := 7) (j := 4) (u := -2691201) (v := 86)
    (by rw [G77_coeff_fst, G77_coeff_snd]; exact G77_bezout)

instance factPrime37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

noncomputable def F37 : (ZMod 37)[X] := 19 * X ^ 7 + 9 * X ^ 6 + 17 * X ^ 5 + 25 * X ^ 4
    - 19 * X ^ 3 - 18 * X ^ 2 + 29 * X + 31

theorem G77_map37 : G77.map (Int.castRingHom (ZMod 37)) = F37 := by
  have e315 : ((315 : (ZMod 37)[X])) = 19 := by
    rw [← map_ofNat C 315, ← map_ofNat C 19, C_inj]; decide
  have e20988 : ((20988 : (ZMod 37)[X])) = 9 := by
    rw [← map_ofNat C 20988, ← map_ofNat C 9, C_inj]; decide
  have e835255 : ((835255 : (ZMod 37)[X])) = 17 := by
    rw [← map_ofNat C 835255, ← map_ofNat C 17, C_inj]; decide
  have e9857306 : ((9857306 : (ZMod 37)[X])) = 25 := by
    rw [← map_ofNat C 9857306, ← map_ofNat C 25, C_inj]; decide
  have e110390888 : ((110390888 : (ZMod 37)[X])) = 19 := by
    rw [← map_ofNat C 110390888, ← map_ofNat C 19, C_inj]; decide
  have e1015601696 : ((1015601696 : (ZMod 37)[X])) = 18 := by
    rw [← map_ofNat C 1015601696, ← map_ofNat C 18, C_inj]; decide
  have e5128130432 : ((5128130432 : (ZMod 37)[X])) = 29 := by
    rw [← map_ofNat C 5128130432, ← map_ofNat C 29, C_inj]; decide
  have e4553967616 : ((4553967616 : (ZMod 37)[X])) = 31 := by
    rw [← map_ofNat C 4553967616, ← map_ofNat C 31, C_inj]; decide
  simp only [G77, F37, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_X]
  rw [e315, e20988, e835255, e9857306, e110390888, e1015601696, e5128130432, e4553967616]

theorem F37_no_root (x : ZMod 37) : F37.eval x ≠ 0 := by
  revert x
  simp only [F37, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

instance factPrime11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

noncomputable def F11 : (ZMod 11)[X] := 7 * X ^ 7 + 3 * X ^ 5 + 8 * X ^ 4 - 3 * X ^ 3
    - 10 * X ^ 2 + 7 * X

theorem G77_map11 : G77.map (Int.castRingHom (ZMod 11)) = F11 := by
  have e315 : ((315 : (ZMod 11)[X])) = 7 := by
    rw [← map_ofNat C 315, ← map_ofNat C 7, C_inj]; decide
  have e20988 : ((20988 : (ZMod 11)[X])) = 0 := by
    rw [← map_ofNat C 20988, ← C_0, C_inj]; decide
  have e835255 : ((835255 : (ZMod 11)[X])) = 3 := by
    rw [← map_ofNat C 835255, ← map_ofNat C 3, C_inj]; decide
  have e9857306 : ((9857306 : (ZMod 11)[X])) = 8 := by
    rw [← map_ofNat C 9857306, ← map_ofNat C 8, C_inj]; decide
  have e110390888 : ((110390888 : (ZMod 11)[X])) = 3 := by
    rw [← map_ofNat C 110390888, ← map_ofNat C 3, C_inj]; decide
  have e1015601696 : ((1015601696 : (ZMod 11)[X])) = 10 := by
    rw [← map_ofNat C 1015601696, ← map_ofNat C 10, C_inj]; decide
  have e5128130432 : ((5128130432 : (ZMod 11)[X])) = 7 := by
    rw [← map_ofNat C 5128130432, ← map_ofNat C 7, C_inj]; decide
  have e4553967616 : ((4553967616 : (ZMod 11)[X])) = 0 := by
    rw [← map_ofNat C 4553967616, ← C_0, C_inj]; decide
  simp only [G77, F11, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_X]
  rw [e315, e20988, e835255, e9857306, e110390888, e1015601696, e5128130432, e4553967616]
  ring

set_option maxRecDepth 40000 in
theorem F11_rem2_ne (b c : ZMod 11) :
    7 * b ^ 6 - 35 * c * b ^ 4 + 42 * c ^ 2 * b ^ 2 + 3 * b ^ 4 - 7 * c ^ 3 - 9 * c * b ^ 2
      - 8 * b ^ 3 + 3 * c ^ 2 + 16 * c * b - 3 * b ^ 2 + 3 * c + 10 * b + 7 ≠ 0 ∨
    7 * c * b ^ 5 - 28 * c ^ 2 * b ^ 3 + 21 * c ^ 3 * b + 3 * c * b ^ 3 - 6 * c ^ 2 * b
      - 8 * c * b ^ 2 + 8 * c ^ 2 - 3 * c * b + 10 * c ≠ 0 := by
  revert b c
  decide

noncomputable def S11q2 (b c : ZMod 11) : (ZMod 11)[X] :=
  C (7) * X ^ 5
    + C (-7 * b) * X ^ 4
    + C (7 * b ^ 2 - 7 * c + 3) * X ^ 3
    + C (-7 * b ^ 3 + 14 * c * b - 3 * b + 8) * X ^ 2
    + C (7 * b ^ 4 - 21 * c * b ^ 2 + 7 * c ^ 2 + 3 * b ^ 2 - 3 * c - 8 * b - 3) * X
    + C (-7 * b ^ 5 + 28 * c * b ^ 3 - 21 * c ^ 2 * b - 3 * b ^ 3 + 6 * c * b + 8 * b ^ 2
        - 8 * c + 3 * b - 10)

theorem F11_div2 (b c : ZMod 11) :
    F11 = (X ^ 2 + C b * X + C c) * S11q2 b c
      + C (7 * b ^ 6 - 35 * c * b ^ 4 + 42 * c ^ 2 * b ^ 2 + 3 * b ^ 4 - 7 * c ^ 3
          - 9 * c * b ^ 2 - 8 * b ^ 3 + 3 * c ^ 2 + 16 * c * b - 3 * b ^ 2 + 3 * c + 10 * b
          + 7) * X
      + C (7 * c * b ^ 5 - 28 * c ^ 2 * b ^ 3 + 21 * c ^ 3 * b + 3 * c * b ^ 3
          - 6 * c ^ 2 * b - 8 * c * b ^ 2 + 8 * c ^ 2 - 3 * c * b + 10 * c) := by
  simp only [F11, S11q2, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_neg]
  ring

set_option maxRecDepth 40000 in
theorem F11_rem3_ne (b c d : ZMod 11) :
    -7 * b ^ 5 + 28 * c * b ^ 3 - 21 * d * b ^ 2 - 21 * c ^ 2 * b - 3 * b ^ 3 + 14 * d * c
      + 6 * c * b + 8 * b ^ 2 - 3 * d - 8 * c + 3 * b - 10 ≠ 0 ∨
    -7 * c * b ^ 4 + 7 * d * b ^ 3 + 21 * c ^ 2 * b ^ 2 - 28 * d * c * b - 7 * c ^ 3
      - 3 * c * b ^ 2 + 7 * d ^ 2 + 3 * d * b + 3 * c ^ 2 + 8 * c * b - 8 * d + 3 * c
      + 7 ≠ 0 ∨
    -7 * d * b ^ 4 + 21 * d * c * b ^ 2 - 14 * d ^ 2 * b - 7 * d * c ^ 2 - 3 * d * b ^ 2
      + 3 * d * c + 8 * d * b + 3 * d ≠ 0 := by
  revert b c d
  decide

noncomputable def S11q3 (b c d : ZMod 11) : (ZMod 11)[X] :=
  C (7) * X ^ 4
    + C (-7 * b) * X ^ 3
    + C (7 * b ^ 2 - 7 * c + 3) * X ^ 2
    + C (-7 * b ^ 3 + 14 * c * b - 7 * d - 3 * b + 8) * X
    + C (7 * b ^ 4 - 21 * c * b ^ 2 + 14 * d * b + 7 * c ^ 2 + 3 * b ^ 2 - 3 * c - 8 * b
        - 3)

theorem F11_div3 (b c d : ZMod 11) :
    F11 = (X ^ 3 + C b * X ^ 2 + C c * X + C d) * S11q3 b c d
      + C (-7 * b ^ 5 + 28 * c * b ^ 3 - 21 * d * b ^ 2 - 21 * c ^ 2 * b - 3 * b ^ 3
          + 14 * d * c + 6 * c * b + 8 * b ^ 2 - 3 * d - 8 * c + 3 * b - 10) * X ^ 2
      + C (-7 * c * b ^ 4 + 7 * d * b ^ 3 + 21 * c ^ 2 * b ^ 2 - 28 * d * c * b - 7 * c ^ 3
          - 3 * c * b ^ 2 + 7 * d ^ 2 + 3 * d * b + 3 * c ^ 2 + 8 * c * b - 8 * d + 3 * c
          + 7) * X
      + C (-7 * d * b ^ 4 + 21 * d * c * b ^ 2 - 14 * d ^ 2 * b - 7 * d * c ^ 2
          - 3 * d * b ^ 2 + 3 * d * c + 8 * d * b + 3 * d) := by
  simp only [F11, S11q3, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_neg]
  ring

theorem aeval_E77pt (x : ℝ) : aeval x E77pt = -20160 * x ^ 7 - 1343232 * x ^ 6
    - 53456320 * x ^ 5 - 630867584 * x ^ 4 + 7065016832 * x ^ 3 + 64998508544 * x ^ 2
    - 328200347648 * x - 291453927424 := by
  simp [E77pt_eq, map_ofNat]

theorem derivative5_E77pt :
    derivative (derivative (derivative (derivative (derivative E77pt)))) =
      -50803200 * X ^ 2 - 967127040 * X - 6414758400 := by
  rw [E77pt_eq]
  simp [derivative_add, derivative_sub, derivative_mul, map_ofNat]
  ring

theorem derivative5_E77pt_no_real_root (z : ℝ) :
    aeval z (derivative (derivative (derivative (derivative
      (derivative E77pt))))) ≠ 0 := by
  rw [derivative5_E77pt]
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_neg]
  nlinarith [sq_nonneg (z + 2332 / 245)]

theorem E77pt_sign0 :
    aeval (-25 : ℝ) E77pt > 0 ∧ aeval (-24 : ℝ) E77pt < 0 := by
  constructor <;> rw [aeval_E77pt] <;> norm_num

theorem E77pt_sign1 :
    aeval (-11 : ℝ) E77pt < 0 ∧ aeval (-10 : ℝ) E77pt > 0 := by
  constructor <;> rw [aeval_E77pt] <;> norm_num

theorem E77pt_sign2 :
    aeval (-1 : ℝ) E77pt > 0 ∧ aeval (0 : ℝ) E77pt < 0 := by
  constructor <;> rw [aeval_E77pt] <;> norm_num

theorem E77pt_sign3 :
    aeval (5 : ℝ) E77pt < 0 ∧ aeval (6 : ℝ) E77pt > 0 := by
  constructor <;> rw [aeval_E77pt] <;> norm_num

theorem E77pt_sign4 :
    aeval (8 : ℝ) E77pt > 0 ∧ aeval (9 : ℝ) E77pt < 0 := by
  constructor <;> rw [aeval_E77pt] <;> norm_num

end Point

section Generic

noncomputable def E77gen : (Polynomial ℚ)[X] :=
  E ((Polynomial ℚ)[X]) 7 7 (C (Polynomial.X : Polynomial ℚ)) 0 X

theorem hsgen7 :
    (C (Polynomial.X : Polynomial ℚ) : (Polynomial ℚ)[X]) * 7 + 0 * 7
      = C (7 * Polynomial.X : Polynomial ℚ) := by
  rw [zero_mul, add_zero, show ((7 : (Polynomial ℚ)[X])) = C (7 : Polynomial ℚ)
    from (map_ofNat C 7).symm, ← C_mul]
  ring_nf

set_option maxRecDepth 20000 in
theorem E77gen_eq : E77gen =
    C (35280 * Polynomial.X + 423360) * X ^ 7
    + C (640332 * Polynomial.X ^ 2 + 18084528 * Polynomial.X + 124806528) * X ^ 6
    + C (4504276 * Polynomial.X ^ 3 + 200252808 * Polynomial.X ^ 2
        + 2911834800 * Polynomial.X + 13853439936) * X ^ 5
    + C (16252369 * Polynomial.X ^ 4 + 982147572 * Polynomial.X ^ 3
        + 21819281148 * Polynomial.X ^ 2 + 211173442704 * Polynomial.X
        + 751179840768) * X ^ 4
    + C (32941720 * Polynomial.X ^ 5 + 2504713596 * Polynomial.X ^ 4
        + 74544349152 * Polynomial.X ^ 3 + 1084914691056 * Polynomial.X ^ 2
        + 7717250669184 * Polynomial.X + 21451318608384) * X ^ 3
    + C (37882978 * Polynomial.X ^ 6 + 3454645236 * Polynomial.X ^ 5
        + 128188708116 * Polynomial.X ^ 4 + 2475288257120 * Polynomial.X ^ 3
        + 26210422485072 * Polynomial.X ^ 2 + 144169233437376 * Polynomial.X
        + 321509264380416) * X ^ 2
    + C (23059204 * Polynomial.X ^ 7 + 2440981452 * Polynomial.X ^ 6
        + 107919898296 * Polynomial.X ^ 5 + 2580370066400 * Polynomial.X ^ 4
        + 35994561491616 * Polynomial.X ^ 3 + 292589922647232 * Polynomial.X ^ 2
        + 1281759237400320 * Polynomial.X + 2331552477284352) * X
    + C (5764801 * Polynomial.X ^ 8 + 691776120 * Polynomial.X ^ 7
        + 35320112184 * Polynomial.X ^ 6 + 1000846900256 * Polynomial.X ^ 5
        + 17192450355024 * Polynomial.X ^ 4 + 183080635702272 * Polynomial.X ^ 3
        + 1178666771998464 * Polynomial.X ^ 2 + 4188742535577600 * Polynomial.X
        + 6283113803366400) := by
  rw [E77gen, E_seven_seven_s (C (Polynomial.X : Polynomial ℚ)) 0 X
    (C (7 * Polynomial.X : Polynomial ℚ)) hsgen7]
  simp only [map_add, map_mul, map_ofNat, map_pow]
  ring

theorem E77gen_coeff7 : E77gen.coeff 7 = 35280 * Polynomial.X + 423360 := by
  rw [E77gen_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem E77gen_coeff0 : E77gen.coeff 0 = 5764801 * Polynomial.X ^ 8
    + 691776120 * Polynomial.X ^ 7 + 35320112184 * Polynomial.X ^ 6
    + 1000846900256 * Polynomial.X ^ 5 + 17192450355024 * Polynomial.X ^ 4
    + 183080635702272 * Polynomial.X ^ 3 + 1178666771998464 * Polynomial.X ^ 2
    + 4188742535577600 * Polynomial.X + 6283113803366400 := by
  rw [E77gen_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem E77gen_coeff0_at_bad :
    (E77gen.coeff 0).eval (-12 : ℚ) = -745612148736 := by
  rw [E77gen_coeff0]
  norm_num

theorem E77gen_map_spec :
    E77gen.map (Polynomial.evalRingHom (-88 / 7 : ℚ)) = E77pt := by
  rw [E77gen_eq, E77pt_eq]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, coe_evalRingHom, eval_add, eval_mul, eval_pow,
    eval_X, eval_ofNat]
  norm_num [map_ofNat]
  ring

end Generic

end Rhone.Algebra.GaloisDegreeSeven
