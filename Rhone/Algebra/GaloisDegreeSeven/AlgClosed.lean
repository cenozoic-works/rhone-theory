/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.Generic
public import Rhone.Algebra.GaloisDegreeSeven.Generic7
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! # `ℚ(u)` is algebraically closed in `ℚ(u)(v)`, and irreducibility survives -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial

section AlgClosed

variable {K : Type*} [Field K]

theorem exists_C_of_isAlgebraic {f : RatFunc K} (h : IsAlgebraic K f) :
    ∃ c : K, f = RatFunc.C c := by
  by_contra hc
  exact RatFunc.transcendental_of_ne_C f hc h

theorem isAlgebraic_iff_exists_C (f : RatFunc K) :
    IsAlgebraic K f ↔ ∃ c : K, f = RatFunc.C c := by
  refine ⟨exists_C_of_isAlgebraic, ?_⟩
  rintro ⟨c, rfl⟩
  rw [← RatFunc.algebraMap_eq_C]
  exact isAlgebraic_algebraMap c

end AlgClosed

section Transfer

variable {K : Type*} [Field K]

theorem isPrimitive_map_C {p : K[X]} (hp : p ≠ 0) :
    (p.map (Polynomial.C : K →+* K[X])).IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  have hk : p.coeff p.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hd := hr p.natDegree
  rw [coeff_map] at hd
  exact isUnit_of_dvd_unit hd (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk))

theorem algebraMap_comp_C :
    (algebraMap K[X] (RatFunc K)).comp (Polynomial.C : K →+* K[X])
      = algebraMap K (RatFunc K) :=
  (RatFunc.algebraMap_comp_C (K := K)).trans (RatFunc.algebraMap_eq_C (K := K)).symm

theorem irreducible_map_ratFunc {p : K[X]} (hp : Irreducible p) :
    Irreducible (p.map (algebraMap K (RatFunc K))) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hprim : (p.map (Polynomial.C : K →+* K[X])).IsPrimitive := isPrimitive_map_C hp0
  have hCne : (Polynomial.C p.leadingCoeff : K[X]) ≠ 0 := by
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hlcm : (p.map (Polynomial.C : K →+* K[X])).leadingCoeff
      = Polynomial.C p.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hCne
  have hlc : (Polynomial.evalRingHom (0 : K))
      (p.map (Polynomial.C : K →+* K[X])).leadingCoeff ≠ 0 := by
    rw [hlcm]
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hback : (p.map (Polynomial.C : K →+* K[X])).map (Polynomial.evalRingHom (0 : K)) = p := by
    rw [Polynomial.map_map]
    have : (Polynomial.evalRingHom (0 : K)).comp (Polynomial.C : K →+* K[X])
        = RingHom.id K := by ext a; simp
    rw [this, Polynomial.map_id]
  have hres := irreducible_ratFunc_of_specialization (K := RatFunc K)
    (Polynomial.evalRingHom (0 : K)) hprim hlc (by rw [hback]; exact hp)
  rwa [Polynomial.map_map, algebraMap_comp_C] at hres

end Transfer

section Instances

theorem E55gen_irreducible_two_var :
    Irreducible (((Rhone.Algebra.Galois.E55gen.map
        (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))))) :=
  irreducible_map_ratFunc Rhone.Algebra.Galois.E55gen_irreducible_ratFunc

theorem E77gen_irreducible_two_var :
    Irreducible (((E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))))) :=
  irreducible_map_ratFunc E77gen_irreducible_ratFunc

theorem E55gen_irreducible_three_var :
    Irreducible ((((Rhone.Algebra.Galois.E55gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
        (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)))).map
      (algebraMap (RatFunc (RatFunc ℚ)) (RatFunc (RatFunc (RatFunc ℚ)))))) :=
  irreducible_map_ratFunc E55gen_irreducible_two_var

theorem E77gen_irreducible_three_var :
    Irreducible ((((E77gen.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))).map
        (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)))).map
      (algebraMap (RatFunc (RatFunc ℚ)) (RatFunc (RatFunc (RatFunc ℚ)))))) :=
  irreducible_map_ratFunc E77gen_irreducible_two_var

end Instances

end Rhone.Algebra.GaloisDegreeSeven
