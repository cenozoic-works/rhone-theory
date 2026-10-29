/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Irreducibility survives adjoining an independent rational-function variable -/

@[expose] public section

namespace Rhone.Algebra.SamplingUniform

open Polynomial

variable {K : Type*} [Field K]

theorem irreducible_map_polynomial_C (f : K[X]) (hf : Irreducible f) :
    Irreducible (f.map (Polynomial.C : K →+* K[X])) := by
  have hc : Irreducible (Polynomial.C f : K[X][X]) :=
    (Polynomial.prime_C_iff.mpr hf.prime).irreducible
  let hs := (Polynomial.Bivariate.swap (R := K)).toRingEquiv.toMulEquiv
  rw [← Polynomial.Bivariate.swap_C]
  exact (MulEquiv.irreducible_iff hs).mpr hc

theorem isPrimitive_map_polynomial_C (f : K[X]) (hf : f ≠ 0) :
    (f.map (Polynomial.C : K →+* K[X])).IsPrimitive := by
  intro a ha
  obtain ⟨q, hq⟩ := ha
  have hc := congrArg (fun p : K[X][X] => p.coeff f.natDegree) hq
  simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hc
  have hu : IsUnit (Polynomial.C (f.coeff f.natDegree) : K[X]) := by
    apply Polynomial.isUnit_C.mpr
    rw [Polynomial.coeff_natDegree]
    exact isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf)
  exact isUnit_of_dvd_unit ⟨q.coeff f.natDegree, hc⟩ hu

theorem irreducible_map_ratFunc_C (f : K[X]) (hf : Irreducible f) :
    Irreducible (f.map (RatFunc.C : K →+* RatFunc K)) := by
  have hp := isPrimitive_map_polynomial_C f hf.ne_zero
  have hi := (hp.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc K)).mp (irreducible_map_polynomial_C f hf)
  have he : (algebraMap K[X] (RatFunc K)).comp Polynomial.C = RatFunc.C := by
    ext a
    exact RatFunc.algebraMap_C a
  simpa only [Polynomial.map_map, he] using hi

theorem map_ratFunc_C_dvd_iff (f : K[X]) (hf : f ≠ 0) (P : K[X][X]) :
    f.map (RatFunc.C : K →+* RatFunc K) ∣
        P.map (algebraMap K[X] (RatFunc K)) ↔
      f.map (Polynomial.C : K →+* K[X]) ∣ P := by
  have he : (algebraMap K[X] (RatFunc K)).comp Polynomial.C = RatFunc.C := by
    ext a
    exact RatFunc.algebraMap_C a
  simpa only [Polynomial.map_map, he] using
    ((isPrimitive_map_polynomial_C f hf).dvd_iff_fraction_map_dvd_fraction_map
      (RatFunc K) (q := P)).symm

theorem map_ratFunc_C_dvd_iff_swap (f : K[X]) (hf : f ≠ 0) (P : K[X][X]) :
    f.map (RatFunc.C : K →+* RatFunc K) ∣
        P.map (algebraMap K[X] (RatFunc K)) ↔
      Polynomial.C f ∣ Polynomial.Bivariate.swap P := by
  rw [map_ratFunc_C_dvd_iff f hf P]
  constructor
  · intro h
    have hh := map_dvd (Polynomial.Bivariate.swap (R := K)).toRingHom h
    change Polynomial.Bivariate.swap (f.map Polynomial.C) ∣
      Polynomial.Bivariate.swap P at hh
    simpa only [Polynomial.Bivariate.swap_map_C] using hh
  · intro h
    have hh := map_dvd (Polynomial.Bivariate.swap (R := K)).toRingHom h
    change Polynomial.Bivariate.swap (Polynomial.C f) ∣
      Polynomial.Bivariate.swap (Polynomial.Bivariate.swap P) at hh
    simpa only [Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_swap_apply] using hh

end Rhone.Algebra.SamplingUniform
