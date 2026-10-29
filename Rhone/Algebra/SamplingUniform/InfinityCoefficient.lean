/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SamplingUniform.RegularAtZero
public import Mathlib.Algebra.Polynomial.Reverse

/-! # Reflected polynomials as regular rational functions: degree and coefficients -/

@[expose] public section

namespace Rhone.Algebra.SamplingUniform

open Polynomial

variable {K : Type*} [Field K]

noncomputable def evalAtInverse : K[X] →+* RatFunc K :=
  Polynomial.eval₂RingHom RatFunc.C RatFunc.X⁻¹

noncomputable def regularPolynomial : K[X] →+* RegularAtZero K :=
  Polynomial.eval₂RingHom regularC regularZ

@[simp] theorem coe_regularPolynomial (f : K[X]) :
    (regularPolynomial f : RatFunc K) = f.eval₂ RatFunc.C RatFunc.X := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp_all
  | monomial n a => simp [regularPolynomial, Polynomial.eval₂_monomial]

@[simp] theorem residue_regularPolynomial (f : K[X]) :
    residueAtZero (regularPolynomial f) = f.eval 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp_all
  | monomial n a => simp [regularPolynomial, Polynomial.eval₂_monomial]

theorem coe_regular_reflect (f : K[X]) {d : ℕ} (hf : f.natDegree ≤ d) :
    (regularPolynomial (f.reflect d) : RatFunc K) =
      RatFunc.X ^ d * evalAtInverse f := by
  let : Invertible (RatFunc.X⁻¹ : RatFunc K) :=
    invertibleOfNonzero (inv_ne_zero RatFunc.X_ne_zero)
  have h := Polynomial.eval₂_reflect_mul_pow RatFunc.C
    (RatFunc.X⁻¹ : RatFunc K) d f hf
  simp only [invOf_eq_inv, inv_inv, ← coe_regularPolynomial] at h
  change _ = RatFunc.X ^ d * f.eval₂ RatFunc.C RatFunc.X⁻¹
  rw [← h]
  rw [mul_left_comm, ← mul_pow,
    mul_inv_cancel₀ (RatFunc.X_ne_zero (K := K)), one_pow, mul_one]

@[simp] theorem residue_regular_reflect (f : K[X]) (d : ℕ) :
    residueAtZero (regularPolynomial (f.reflect d)) = f.coeff d := by
  rw [residue_regularPolynomial, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_reflect, Polynomial.revAt_zero]

theorem regular_reflect_equation (f g : K[X]) (r : RegularAtZero K)
    {d : ℕ} (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (h : evalAtInverse g * (r : RatFunc K) = evalAtInverse f) :
    regularPolynomial (g.reflect d) * r = regularPolynomial (f.reflect d) := by
  apply Subtype.ext
  simp only [Subring.coe_mul, coe_regular_reflect _ hg, coe_regular_reflect _ hf]
  rw [mul_assoc, h]

theorem degree_le_of_regular_inverse_equation (f g : K[X]) (r : RegularAtZero K)
    {d : ℕ} (hg : g.natDegree ≤ d)
    (h : evalAtInverse g * (r : RatFunc K) = evalAtInverse f) :
    f.natDegree ≤ d := by
  by_contra hn
  have hd : d < f.natDegree := Nat.lt_of_not_ge hn
  have he := regular_reflect_equation f g r (le_refl _) (hg.trans hd.le) h
  have hr := congrArg residueAtZero he
  simp only [map_mul, residue_regular_reflect] at hr
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hg.trans_lt hd), zero_mul] at hr
  have hf : f ≠ 0 := by
    intro hz
    simp [hz] at hd
  exact (Polynomial.leadingCoeff_ne_zero.mpr hf) (by
    simpa only [Polynomial.coeff_natDegree] using hr.symm)

theorem coeff_eq_of_regular_inverse_equation (f g : K[X]) (r : RegularAtZero K)
    {d : ℕ} (hg : g.natDegree ≤ d)
    (h : evalAtInverse g * (r : RatFunc K) = evalAtInverse f) :
    f.coeff d = g.coeff d * residueAtZero r := by
  have hf := degree_le_of_regular_inverse_equation f g r hg h
  have he := congrArg residueAtZero (regular_reflect_equation f g r hf hg h)
  simpa only [map_mul, residue_regular_reflect] using he.symm

end Rhone.Algebra.SamplingUniform
