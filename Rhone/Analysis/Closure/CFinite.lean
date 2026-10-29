/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-! # C-finite two-root closed forms are not hypergeometric -/

@[expose] public section

namespace Rhone.Analysis.Closure

open Polynomial

variable {F : Type*} [Field F] [CharZero F]

def IsHypergeometric (q : ℕ → F) : Prop :=
  ∃ (P Q : F[X]) (N : ℕ), Q ≠ 0 ∧
    ∀ k : ℕ, N ≤ k → q (k + 1) * Q.eval (k : F) = q k * P.eval (k : F)

theorem infinite_natCast_tail (N : ℕ) :
    ((fun k : ℕ => (k : F)) '' {k : ℕ | N ≤ k}).Infinite :=
  Set.Infinite.image (Set.injOn_of_injective Nat.cast_injective) (Set.Ici_infinite N)

theorem eq_zero_of_eval_natCast_eq_zero {W : F[X]} {N : ℕ}
    (h : ∀ k : ℕ, N ≤ k → W.eval (k : F) = 0) : W = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot W ((infinite_natCast_tail (F := F) N).mono ?_)
  rintro _ ⟨k, hk, rfl⟩
  exact h k hk

noncomputable def shift (p : F[X]) : F[X] := p.comp (X + C 1)

omit [CharZero F] in
@[simp] theorem eval_shift (p : F[X]) (x : F) : (shift p).eval x = p.eval (x + 1) := by
  simp [shift]

omit [CharZero F] in
@[simp] theorem natDegree_shift (p : F[X]) : (shift p).natDegree = p.natDegree := by
  rw [shift, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]

omit [CharZero F] in
@[simp] theorem leadingCoeff_shift (p : F[X]) : (shift p).leadingCoeff = p.leadingCoeff := by
  rw [shift, Polynomial.leadingCoeff_comp
    (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
    (Polynomial.monic_X_add_C (1 : F)).leadingCoeff, one_pow, mul_one]

noncomputable def elim (r s : F) (U V : F[X]) : F[X] :=
  C s * (U * shift V) - C r * (shift U * V)

omit [CharZero F] in
theorem eval_elim (r s : F) (U V : F[X]) (x : F) :
    (elim r s U V).eval x
      = s * (U.eval x * V.eval (x + 1)) - r * (U.eval (x + 1) * V.eval x) := by
  simp [elim]

omit [CharZero F] in
theorem coeff_elim (r s : F) (U V : F[X]) :
    (elim r s U V).coeff (U.natDegree + V.natDegree)
      = (s - r) * (U.leadingCoeff * V.leadingCoeff) := by
  have h1 : (U * shift V).coeff (U.natDegree + V.natDegree)
      = U.leadingCoeff * V.leadingCoeff := by
    have h := Polynomial.coeff_mul_degree_add_degree U (shift V)
    rwa [natDegree_shift, leadingCoeff_shift] at h
  have h2 : (shift U * V).coeff (U.natDegree + V.natDegree)
      = U.leadingCoeff * V.leadingCoeff := by
    have h := Polynomial.coeff_mul_degree_add_degree (shift U) V
    rwa [natDegree_shift, leadingCoeff_shift] at h
  rw [elim, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, h1, h2]
  ring

omit [CharZero F] in
theorem elim_ne_zero {r s : F} (hrs : r ≠ s) {U V : F[X]} (hU : U ≠ 0) (hV : V ≠ 0) :
    elim r s U V ≠ 0 := by
  intro h
  have hc := coeff_elim r s U V
  rw [h, Polynomial.coeff_zero] at hc
  have h1 : U.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hU
  have h2 : V.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hV
  rcases mul_eq_zero.mp hc.symm with h' | h'
  · exact hrs (sub_eq_zero.mp h').symm
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact h1 h''
    · exact h2 h''

theorem not_isHypergeometric_two_roots {a b r s : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) :
    ¬ IsHypergeometric (fun k => a * r ^ k + b * s ^ k) := by
  rintro ⟨P, Q, N, hQ, hrel⟩
  set U : F[X] := C r * Q - P with hUdef
  set V : F[X] := C s * Q - P with hVdef
  have hkey : ∀ k : ℕ, N ≤ k →
      a * r ^ k * U.eval (k : F) + b * s ^ k * V.eval (k : F) = 0 := by
    intro k hk
    have h := hrel k hk
    simp only [pow_succ] at h
    simp only [hUdef, hVdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination h
  have hnotboth : ¬ (U = 0 ∧ V = 0) := by
    rintro ⟨h1, h2⟩
    rw [hUdef, sub_eq_zero] at h1
    rw [hVdef, sub_eq_zero] at h2
    have h3 : C (r - s) * Q = 0 := by
      rw [map_sub, sub_mul, h1, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact hrs (sub_eq_zero.mp (Polynomial.C_eq_zero.mp h))
    · exact hQ h
  have hU : U ≠ 0 := by
    intro hU0
    refine hnotboth ⟨hU0, ?_⟩
    refine eq_zero_of_eval_natCast_eq_zero (N := N) fun k hk => ?_
    have h := hkey k hk
    rw [hU0] at h
    simp only [Polynomial.eval_zero, mul_zero, zero_add] at h
    have hpow : s ^ k ≠ 0 := pow_ne_zero k hs
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hb
      · exact absurd h'' hpow
    · exact h'
  have hV : V ≠ 0 := by
    intro hV0
    refine hnotboth ⟨?_, hV0⟩
    refine eq_zero_of_eval_natCast_eq_zero (N := N) fun k hk => ?_
    have h := hkey k hk
    rw [hV0] at h
    simp only [Polynomial.eval_zero, mul_zero, add_zero] at h
    have hpow : r ^ k ≠ 0 := pow_ne_zero k hr
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' ha
      · exact absurd h'' hpow
    · exact h'
  have hW : elim r s U V = 0 := by
    refine eq_zero_of_eval_natCast_eq_zero (N := N) fun k hk => ?_
    have h1 := hkey k hk
    have h2 := hkey (k + 1) (by omega)
    have hcast : ((k + 1 : ℕ) : F) = (k : F) + 1 := by push_cast; ring
    rw [hcast, pow_succ, pow_succ] at h2
    have hz : a * r ^ k * (s * (U.eval (k : F) * V.eval ((k : F) + 1))
        - r * (U.eval ((k : F) + 1) * V.eval (k : F))) = 0 := by
      linear_combination s * V.eval ((k : F) + 1) * h1 - V.eval (k : F) * h2
    rw [eval_elim]
    have hane : a * r ^ k ≠ 0 := mul_ne_zero ha (pow_ne_zero k hr)
    rcases mul_eq_zero.mp hz with h' | h'
    · exact absurd h' hane
    · exact h'
  exact elim_ne_zero hrs hU hV hW

omit [CharZero F] in
theorem cfinite_two_closed_form {q : ℕ → F} {c₁ c₀ r s : F}
    (hrec : ∀ k, q (k + 2) = c₁ * q (k + 1) + c₀ * q k)
    (hsum : r + s = c₁) (hprod : r * s = -c₀) (hrs : r ≠ s) (k : ℕ) :
    q k = ((q 1 - s * q 0) / (r - s)) * r ^ k + ((r * q 0 - q 1) / (r - s)) * s ^ k := by
  have hne : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have hrec' : ∀ m : ℕ, q (m + 2) = (r + s) * q (m + 1) - (r * s) * q m := by
    intro m
    rw [hrec m, hsum, hprod]
    ring
  have main : ∀ m : ℕ,
      q m = ((q 1 - s * q 0) / (r - s)) * r ^ m + ((r * q 0 - q 1) / (r - s)) * s ^ m ∧
      q (m + 1)
        = ((q 1 - s * q 0) / (r - s)) * r ^ (m + 1)
          + ((r * q 0 - q 1) / (r - s)) * s ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · field_simp
        ring
      · field_simp
        ring
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec' m, ih.2, ih.1]
      ring
  exact (main k).1

theorem not_isHypergeometric_of_cfinite {q : ℕ → F} {c₁ c₀ r s : F}
    (hrec : ∀ k, q (k + 2) = c₁ * q (k + 1) + c₀ * q k)
    (hsum : r + s = c₁) (hprod : r * s = -c₀) (hrs : r ≠ s) (hr : r ≠ 0) (hs : s ≠ 0)
    (ha : q 1 ≠ s * q 0) (hb : q 1 ≠ r * q 0) : ¬ IsHypergeometric q := by
  have hne : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have hclosed : q = fun k => ((q 1 - s * q 0) / (r - s)) * r ^ k
      + ((r * q 0 - q 1) / (r - s)) * s ^ k :=
    funext fun k => cfinite_two_closed_form hrec hsum hprod hrs k
  rw [hclosed]
  refine not_isHypergeometric_two_roots ?_ ?_ hr hs hrs
  · exact div_ne_zero (sub_ne_zero.mpr ha) hne
  · exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hb)) hne

theorem not_exists_ratio_two_roots {a b r s : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) :
    ¬ ∃ (P Q : F[X]) (N : ℕ), Q ≠ 0 ∧ (∀ k : ℕ, N ≤ k → Q.eval (k : F) ≠ 0) ∧
      ∀ k : ℕ, N ≤ k →
        (a * r ^ (k + 1) + b * s ^ (k + 1))
          = P.eval (k : F) / Q.eval (k : F) * (a * r ^ k + b * s ^ k) := by
  rintro ⟨P, Q, N, hQ, hQne, hrel⟩
  refine not_isHypergeometric_two_roots ha hb hr hs hrs ⟨P, Q, N, hQ, fun k hk => ?_⟩
  have hQk := hQne k hk
  change (a * r ^ (k + 1) + b * s ^ (k + 1)) * Q.eval (k : F)
    = (a * r ^ k + b * s ^ k) * P.eval (k : F)
  rw [hrel k hk]
  field_simp

end Rhone.Analysis.Closure
