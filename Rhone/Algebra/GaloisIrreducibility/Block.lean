/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Why no small prime certifies irreducibility: `E_{i,j}` splits whenever a superdiagonal dies -/

@[expose] public section

namespace Rhone.Algebra.GaloisIrreducibility

open LinearAlgebra.Tridiag

variable {R : Type*} [CommRing R]

theorem cont_split (d b c : ℕ → R) (t : ℕ) (h : b t * c t = 0) (n : ℕ) :
    cont d b c (t + 1 + n) =
      cont d b c (t + 1) *
        cont (fun k => d (t + 1 + k)) (fun k => b (t + 1 + k)) (fun k => c (t + 1 + k)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [cont]
    | 1 =>
      have e : t + 1 + 1 = t + 2 := rfl
      rw [e, cont, cont, h, zero_mul, sub_zero]
      simp [mul_comm]
    | (k + 2) =>
      have e1 : t + 1 + (k + 2) = t + 1 + k + 2 := by omega
      have e2 : t + 1 + (k + 1) = t + 1 + k + 1 := by omega
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      rw [e2] at h1
      rw [e1, cont, cont, h1, h2]
      simp only [e2]
      ring

theorem E_split (i j : ℕ) (θA θB ρ : R) (t : ℕ) (ht : t ≤ min i j)
    (h : bcoef R i j t * ccoef R ρ t = 0) :
    E R i j θA θB ρ =
      cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (t + 1) *
        cont (fun k => dcoef R i j θA θB ρ (t + 1 + k)) (fun k => bcoef R i j (t + 1 + k))
          (fun k => ccoef R ρ (t + 1 + k)) (min i j - t) := by
  rw [E_eq_cont]
  have e : min i j + 1 = t + 1 + (min i j - t) := by omega
  rw [e]
  exact cont_split _ _ _ t h _

theorem E_split_diag (m : ℕ) (θA θB ρ : R) (t : ℕ) (ht : t ≤ m)
    (h : (((m - t) * (m - t) : ℕ) : R) = 0) :
    E R m m θA θB ρ =
      cont (dcoef R m m θA θB ρ) (bcoef R m m) (ccoef R ρ) (t + 1) *
        cont (fun k => dcoef R m m θA θB ρ (t + 1 + k)) (fun k => bcoef R m m (t + 1 + k))
          (fun k => ccoef R ρ (t + 1 + k)) (m - t) := by
  have hmin : min m m = m := min_self m
  have hb : bcoef R m m t = 0 := by
    rw [bcoef, h, mul_zero]
  have := E_split (R := R) m m θA θB ρ t (by omega) (by rw [hb, zero_mul])
  rwa [hmin] at this

theorem E_split_zmod (p m : ℕ) (hp : 0 < p) (hpm : p ≤ m) (θA θB ρ : ZMod p) :
    E (ZMod p) m m θA θB ρ =
      cont (dcoef (ZMod p) m m θA θB ρ) (bcoef (ZMod p) m m) (ccoef (ZMod p) ρ) (m - p + 1) *
        cont (fun k => dcoef (ZMod p) m m θA θB ρ (m - p + 1 + k))
          (fun k => bcoef (ZMod p) m m (m - p + 1 + k))
          (fun k => ccoef (ZMod p) ρ (m - p + 1 + k)) (m - (m - p)) := by
  refine E_split_diag (R := ZMod p) m θA θB ρ (m - p) (by omega) ?_
  have hmt : m - (m - p) = p := by omega
  rw [hmt, Nat.cast_mul, ZMod.natCast_self, mul_zero]

theorem not_isUnit_of_eval_ne {K : Type*} [Field K] {f : Polynomial K} {x y : K}
    (h : f.eval x ≠ f.eval y) : ¬ IsUnit f := by
  intro hu
  obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp hu
  exact h (by rw [← hc]; simp)

theorem not_irreducible_of_eq_mul {M : Type*} [CommMonoid M] {f a b : M} (hab : f = a * b)
    (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) : ¬ Irreducible f := fun h =>
  (h.isUnit_or_isUnit hab).elim ha hb

end Rhone.Algebra.GaloisIrreducibility
