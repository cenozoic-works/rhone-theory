/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DiagonalObstruction.CollisionClosure
public import Rhone.Analysis.DiagonalObstruction.SpectralFactorTransport
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Irreducible factors of `E_{m,m}` of unbounded degree over rational functions -/

@[expose] public section

namespace Rhone.Analysis.DiagonalObstruction

open Polynomial

attribute [local instance] Polynomial.algebra

noncomputable def rationalFunctionFactor (F : Polynomial (Polynomial ℤ)) :
    Polynomial (RatFunc ℚ) :=
  (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))).map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ))

theorem rationalFunctionFactor_natDegree (F : Polynomial (Polynomial ℤ)) (hF : F.Monic) :
    (rationalFunctionFactor F).natDegree = F.natDegree := by
  rw [rationalFunctionFactor, (hF.map _).natDegree_map, hF.natDegree_map]

theorem rationalFunctionFactor_irreducible (F : Polynomial (Polynomial ℤ))
    (hF : F.Monic)
    (hi : Irreducible (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))) :
    Irreducible (rationalFunctionFactor F) := by
  exact ((hF.map _).isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp hi

theorem exists_irreducible_distinguished_factor_gt (D : ℕ) :
    ∃ m : ℕ, ∃ F : Polynomial (Polynomial ℤ),
      2 ≤ m ∧ F.Monic ∧ F ∣ Algebra.DiagonalObstruction.spectralPolynomial m ∧ 0 ∈
          Algebra.DiagonalObstruction.factorLabels m F ∧
      Irreducible (rationalFunctionFactor F) ∧
      rationalFunctionFactor F ∣ rationalFunctionFactor
          (Algebra.DiagonalObstruction.spectralPolynomial m) ∧
      D < (rationalFunctionFactor F).natDegree := by
  obtain ⟨m, hm, hdegree⟩ := unbounded_distinguished_factor_degree D
  obtain ⟨F, hF, hdiv, hirr, hzero⟩ := Algebra.DiagonalObstruction.exists_monic_integer_factor_zero
      m
  refine ⟨m, F, hm, hF, hdiv, hzero,
    rationalFunctionFactor_irreducible F hF hirr, ?_, ?_⟩
  · exact Polynomial.map_dvd _ (Polynomial.map_dvd _ hdiv)
  · rw [rationalFunctionFactor_natDegree F hF]
    exact hdegree F hF hdiv hzero

theorem rationalFunctionFactor_spectralPolynomial (m : ℕ) :
    rationalFunctionFactor (Algebra.DiagonalObstruction.spectralPolynomial m) =
      (Algebra.DiagonalObstruction.spectralMatrix (RatFunc ℚ) m RatFunc.X).charpoly := by
  rw [rationalFunctionFactor, map_map, spectralPolynomial_map]
  simp

theorem unbounded_irreducible_E_mm_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m X 0 (C RatFunc.X) ∧
      D < G.natDegree := by
  obtain ⟨m, F, hm, _, _, _, hirr, hdiv, hdegree⟩ :=
    exists_irreducible_distinguished_factor_gt D
  refine ⟨m, hm, ?_⟩
  rw [rationalFunctionFactor_spectralPolynomial] at hdiv
  exact irreducible_ratFunc_factor_transport (by omega) _ hirr hdiv hdegree

end Rhone.Analysis.DiagonalObstruction
