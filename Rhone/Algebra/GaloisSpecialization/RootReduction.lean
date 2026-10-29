/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.FieldTheory.Separable

/-! # Separable specialization prevents collisions of roots -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S]

theorem linear_factors_dvd_of_distinct_roots {p : R[X]} {x y : R}
    (hx : p.IsRoot x) (hy : p.IsRoot y) (hxy : x ≠ y) :
    (X - C x) * (X - C y) ∣ p := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hx
  have hqy : q.IsRoot y := by
    have he := hy
    rw [IsRoot.def, hq, eval_mul, eval_sub, eval_X, eval_C] at he
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hxy.symm)
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqy
  exact ⟨r, by rw [hq, hr, mul_assoc]⟩

theorem roots_eq_of_separable_specialization (φ : R →+* S) {p : R[X]}
    (hsep : (p.map φ).Separable) {x y : R} (hx : p.IsRoot x) (hy : p.IsRoot y)
    (hφ : φ x = φ y) : x = y := by
  by_contra hxy
  have hd := Polynomial.map_dvd φ (linear_factors_dvd_of_distinct_roots hx hy hxy)
  simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, hφ] at hd
  exact not_isUnit_X_sub_C (φ y) (isUnit_of_self_mul_dvd_separable hsep hd)

theorem specialization_injective_on_roots (φ : R →+* S) {p : R[X]}
    (hsep : (p.map φ).Separable) :
    Set.InjOn φ {x : R | p.IsRoot x} := by
  intro x hx y hy hφ
  exact roots_eq_of_separable_specialization φ hsep hx hy hφ

def rootSpecialization (φ : R →+* S) (p : R[X]) :
    {x : R // p.IsRoot x} → {y : S // (p.map φ).IsRoot y} :=
  fun x => ⟨φ x, x.property.map⟩

omit [Nontrivial S] in
theorem rootSpecialization_bijective [IsDomain S] (φ : R →+* S) {p : R[X]}
    (hsplit : p.Splits) (hmap : p.map φ ≠ 0) (hsep : (p.map φ).Separable) :
    Function.Bijective (rootSpecialization φ p) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact roots_eq_of_separable_specialization φ hsep x.property y.property
      (congrArg Subtype.val hxy)
  · intro y
    have hroots : p.roots.map φ = (p.map φ).roots :=
      roots_map_of_map_ne_zero_of_card_eq_natDegree φ hmap
        hsplit.natDegree_eq_card_roots.symm
    have hy : y.val ∈ p.roots.map φ := by
      rw [hroots]
      exact (mem_roots hmap).mpr y.property
    obtain ⟨x, hx, hxy⟩ := Multiset.mem_map.mp hy
    exact ⟨⟨x, isRoot_of_mem_roots hx⟩, Subtype.ext hxy⟩

end Rhone.Algebra.GaloisSpecialization
