/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DiagonalObstruction.SpectralFactorTransport

/-! # Nonvanishing of the diagonal determinant `E_{m,m}` as a polynomial in the mutation rate -/

@[expose] public section

namespace Rhone.Analysis.DiagonalObstruction

open Polynomial

theorem E_mutationPolynomial_ne_zero {K : Type*} [Field K] [CharZero K]
    {m : ℕ} (hm : 1 ≤ m) (ρ : K) :
    Rhone.LinearAlgebra.Tridiag.E K[X] m m X 0 (C ρ) ≠ 0 := by
  intro hzero
  have h := spectralVariableEquiv_charpoly hm ρ
  rw [hzero, mul_zero] at h
  have hc : (Algebra.DiagonalObstruction.spectralMatrix K m ρ).charpoly = 0 :=
    (spectralVariableEquiv K m (by omega)).injective (by simpa using h)
  exact (Matrix.charpoly_monic _).ne_zero hc

end Rhone.Analysis.DiagonalObstruction
