/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! # Coprimality from one degree-preserving specialization -/

@[expose] public section

namespace Rhone.Algebra.Sharpness
open Polynomial

theorem isCoprime_map_of_specialization
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    (ι : R →+* K) (s : R →+* L) (hι : Function.Injective ι)
    (f g : Polynomial R)
    (hf : (f.map s).natDegree = f.natDegree)
    (hg : (g.map s).natDegree = g.natDegree)
    (hcop : IsCoprime (f.map s) (g.map s)) :
    IsCoprime (f.map ι) (g.map ι) := by
  have hres : f.resultant g f.natDegree g.natDegree ≠ 0 := by
    intro h
    have hn := resultant_ne_zero (f.map s) (g.map s) hcop
    rw [hf, hg, resultant_map_map, h, map_zero] at hn
    exact hn rfl
  have hfg : f.map ι ≠ 0 ∨ g.map ι ≠ 0 := by
    by_contra hz
    obtain ⟨hf0, hg0⟩ := not_or.mp hz
    have hfz : f = 0 := (Polynomial.map_injective ι hι)
      (by simpa using not_not.mp hf0)
    have hgz : g = 0 := (Polynomial.map_injective ι hι)
      (by simpa using not_not.mp hg0)
    simp only [hfz, hgz, Polynomial.map_zero] at hcop
    exact not_isCoprime_zero_zero hcop
  by_contra h
  have hz := (resultant_eq_zero_iff).mpr ⟨hfg, h⟩
  rw [natDegree_map_eq_of_injective hι, natDegree_map_eq_of_injective hι,
    resultant_map_map] at hz
  exact hres (hι (by simpa using hz))

theorem isCoprime_map_of_specialization_leadingCoeff
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    (ι : R →+* K) (s : R →+* L) (hι : Function.Injective ι)
    (f g : Polynomial R)
    (hf : s f.leadingCoeff ≠ 0) (hg : s g.leadingCoeff ≠ 0)
    (hcop : IsCoprime (f.map s) (g.map s)) :
    IsCoprime (f.map ι) (g.map ι) :=
  isCoprime_map_of_specialization ι s hι f g
    (natDegree_map_of_leadingCoeff_ne_zero s hf)
    (natDegree_map_of_leadingCoeff_ne_zero s hg) hcop

theorem isCoprime_map_of_specialization_one_leadingCoeff
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    (ι : R →+* K) (s : R →+* L) (hι : Function.Injective ι)
    (f g : Polynomial R) (hf : s f.leadingCoeff ≠ 0)
    (hcop : IsCoprime (f.map s) (g.map s)) :
    IsCoprime (f.map ι) (g.map ι) := by
  have hm : (f.map s).natDegree = f.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero s hf
  have hcoeff : (f.map s).coeff f.natDegree ≠ 0 := by
    simpa only [coeff_map, coeff_natDegree] using hf
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (natDegree_map_le (p := g) (f := s))
  have hpadded : (f.map s).resultant (g.map s) f.natDegree g.natDegree ≠ 0 := by
    rw [hk, resultant_add_right_deg (f := f.map s) (g := g.map s)
      (m := f.natDegree) (n := (g.map s).natDegree) k le_rfl]
    apply mul_ne_zero (pow_ne_zero _ hcoeff)
    simpa only [hm] using resultant_ne_zero (f.map s) (g.map s) hcop
  have hres : f.resultant g f.natDegree g.natDegree ≠ 0 := by
    intro h
    rw [resultant_map_map, h, map_zero] at hpadded
    exact hpadded rfl
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hfι : f.map ι ≠ 0 := by
    intro h
    exact hf0 ((Polynomial.map_injective ι hι) (by simpa using h))
  by_contra h
  have hz := resultant_eq_zero_iff.mpr ⟨Or.inl hfι, h⟩
  rw [natDegree_map_eq_of_injective hι, natDegree_map_eq_of_injective hι,
    resultant_map_map] at hz
  exact hres (hι (by simpa using hz))

end Rhone.Algebra.Sharpness
