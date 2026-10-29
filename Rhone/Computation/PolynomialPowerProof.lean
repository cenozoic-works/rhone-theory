/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialMultiplyProof
import Init.Data.Range.Lemmas
import Mathlib.Data.List.Range

/-! # Sparse powers and repeated factors -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

@[simp] theorem reflect_one : reflect #[((0, 0, 0), 1)] = 1 := by
  simp [reflect, reflectList, exponent, Rhone.Probability.Closure.mono3]

theorem reflect_repeat (g a : Poly) (n : Nat) :
    reflect ((List.range n).foldl (fun out _ => mulPoly out a) g) =
      reflect g * reflect a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    change reflect (mulPoly ((List.range n).foldl (fun out _ => mulPoly out a) g) a) = _
    rw [reflect_mulPoly, ih, pow_succ, mul_assoc]

theorem powPoly_eq_fold (a : Poly) (n : Nat) :
    powPoly a n = (List.range n).foldl (fun out _ => mulPoly out a)
      #[((0, 0, 0), 1)] := by
  simp [powPoly, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

theorem reflect_powPoly (a : Poly) (n : Nat) :
    reflect (powPoly a n) = reflect a ^ n := by
  rw [powPoly_eq_fold, reflect_repeat, reflect_one, one_mul]

end Rhone.Computation.PolynomialEncoding
