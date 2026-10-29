/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic

/-! # The coefficient obstruction used by the two-root collision argument -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

open PowerSeries

variable {R : Type*}

theorem coeff_mul_of_lower_left_zero [CommSemiring R] (f g : R⟦X⟧) (d : ℕ)
    (hf : ∀ i < d, coeff i f = 0) :
    coeff d (f * g) = coeff d f * constantCoeff g := by
  rw [coeff_mul, Finset.sum_eq_single (d, 0)]
  · rw [coeff_zero_eq_constantCoeff]
  · intro ij hij hne
    have hij' : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
    have hlt : ij.1 < d := by
      by_contra h
      have hfst : ij.1 = d := by omega
      have hsnd : ij.2 = 0 := by omega
      exact hne (Prod.ext hfst hsnd)
    rw [hf ij.1 hlt, zero_mul]
  · simp

theorem order_left_of_mul_eq_X_pow_mul [CommRing R] [IsDomain R]
    (f g u : R⟦X⟧) (d : ℕ)
    (hg : constantCoeff g ≠ 0) (hu : constantCoeff u ≠ 0)
    (h : f * g = X ^ d * u) : f.order = d := by
  have hg' : g.order = 0 := by
    by_contra hn
    exact hg (order_ne_zero_iff_constCoeff_eq_zero.mp hn)
  have hu' : u.order = 0 := by
    by_contra hn
    exact hu (order_ne_zero_iff_constCoeff_eq_zero.mp hn)
  have ho := congrArg PowerSeries.order h
  simpa only [order_mul, hg', hu', order_X_pow, add_zero] using ho

theorem constantCoeff_isUnit_of_mul_eq_X_pow_mul [CommRing R] [IsDomain R]
    (f g u : R⟦X⟧) (d : ℕ)
    (hg : constantCoeff g ≠ 0) (hu : IsUnit (constantCoeff u))
    (h : f * g = X ^ d * u) : IsUnit (constantCoeff g) := by
  have ho := order_left_of_mul_eq_X_pow_mul f g u d hg hu.ne_zero h
  have hf : ∀ i < d, coeff i f = 0 := by
    intro i hi
    apply coeff_of_lt_order
    rw [ho]
    exact_mod_cast hi
  have hc := congrArg (coeff d) h
  rw [coeff_mul_of_lower_left_zero f g d hf] at hc
  have hr : coeff d (X ^ d * u) = constantCoeff u := by
    simpa only [Nat.zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul u d 0
  rw [hr] at hc
  exact isUnit_of_mul_isUnit_right (hc.symm ▸ hu)

theorem no_collision_product_over_domain [CommRing R] [IsDomain R]
    (f g u : R⟦X⟧) (d : ℕ)
    (hg : constantCoeff g ≠ 0) (hgn : ¬ IsUnit (constantCoeff g))
    (hu : IsUnit (constantCoeff u)) : f * g ≠ X ^ d * u := by
  intro h
  exact hgn (constantCoeff_isUnit_of_mul_eq_X_pow_mul f g u d hg hu h)

theorem exists_powerSeries_root_of_simple_constant_fiber [CommRing R]
    (f : Polynomial R⟦X⟧) (hf : f.Monic) (a : R)
    (ha : constantCoeff (f.eval (C a)) = 0)
    (hderiv : IsUnit (constantCoeff (f.derivative.eval (C a)))) :
    ∃ z : R⟦X⟧, f.IsRoot z ∧ constantCoeff z = a := by
  let I : Ideal R⟦X⟧ := Ideal.span {X}
  have hmem : f.eval (C a) ∈ I := by
    rw [Ideal.mem_span_singleton, X_dvd_iff]
    exact ha
  have hdunit : IsUnit (f.derivative.eval (C a)) :=
    isUnit_iff_constantCoeff.mpr hderiv
  obtain ⟨z, hz, hzmem⟩ := HenselianRing.is_henselian (I := I) f hf (C a) hmem
    (hdunit.map (Ideal.Quotient.mk I))
  refine ⟨z, hz, ?_⟩
  have hzsub : constantCoeff (z - C a) = 0 := by
    rwa [Ideal.mem_span_singleton, X_dvd_iff] at hzmem
  simpa only [map_sub, constantCoeff_C, sub_eq_zero] using hzsub

theorem constantCoeff_eval_eq_of_constantCoeff_eq [CommRing R]
    (f : Polynomial R⟦X⟧) {z w : R⟦X⟧}
    (h : constantCoeff z = constantCoeff w) :
    constantCoeff (f.eval z) = constantCoeff (f.eval w) := by
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, h]

theorem no_simple_factor_of_collision_schur_numerator [CommRing R] [IsDomain R]
    (q s t u : Polynomial R⟦X⟧) (d : ℕ) (a : R)
    (hq : q.Monic)
    (ha : constantCoeff (q.eval (C a)) = 0)
    (hderiv : IsUnit (constantCoeff (q.derivative.eval (C a))))
    (ht : constantCoeff (t.eval (C a)) ≠ 0)
    (htn : ¬ IsUnit (constantCoeff (t.eval (C a))))
    (hu : IsUnit (constantCoeff (u.eval (C a)))) :
    ¬ q ∣ s * t - Polynomial.C (X ^ d) * u := by
  intro hdiv
  obtain ⟨z, hz, hza⟩ :=
    exists_powerSeries_root_of_simple_constant_fiber q hq a ha hderiv
  have hc : constantCoeff z = constantCoeff (C a) := by
    simpa only [constantCoeff_C] using hza
  have htz := constantCoeff_eval_eq_of_constantCoeff_eq t hc
  have huz := constantCoeff_eval_eq_of_constantCoeff_eq u hc
  have heval : s.eval z * t.eval z = X ^ d * u.eval z := by
    have hroot := hz.dvd hdiv
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, sub_eq_zero] using hroot
  exact no_collision_product_over_domain (s.eval z) (t.eval z) (u.eval z) d
    (htz ▸ ht) (htz ▸ htn) (huz ▸ hu) heval

end Rhone.Algebra.DiagonalObstruction
