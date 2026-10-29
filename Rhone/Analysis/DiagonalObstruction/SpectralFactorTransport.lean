/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DiagonalObstruction.SpectralTransport
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Transport of irreducible spectral factors to irreducible factors of `E_{m,m}` -/

@[expose] public section

namespace Rhone.Analysis.DiagonalObstruction
open Polynomial LinearAlgebra.Tridiag
variable {K : Type*} [Field K] [CharZero K]

noncomputable def spectralVariableEquiv (K : Type*) [Field K] [CharZero K]
    (m : ℕ) (hm : m ≠ 0) : K[X] ≃ₐ[K] K[X] := by
  letI : Invertible (-(m : K)) := invertibleOfNonzero
    (neg_ne_zero.mpr (by exact_mod_cast hm))
  exact Polynomial.algEquivCMulXAddC (-(m : K)) 0

theorem spectralVariableEquiv_apply (m : ℕ) (hm : m ≠ 0) (F : K[X]) :
    spectralVariableEquiv K m hm F = F.comp (C (-(m : K)) * X) := by
  simp [spectralVariableEquiv, Polynomial.algEquivCMulXAddC_apply, comp_eq_aeval]

theorem spectralVariableEquiv_irreducible_iff (m : ℕ) (hm : m ≠ 0) (F : K[X]) :
    Irreducible (spectralVariableEquiv K m hm F) ↔ Irreducible F :=
  MulEquiv.irreducible_iff (spectralVariableEquiv K m hm)

theorem spectralVariableEquiv_natDegree (m : ℕ) (hm : m ≠ 0) (F : K[X]) :
    (spectralVariableEquiv K m hm F).natDegree = F.natDegree := by
  rw [spectralVariableEquiv_apply, natDegree_comp, natDegree_C_mul_X]
  · simp
  · exact neg_ne_zero.mpr (by exact_mod_cast hm)

theorem spectralVariableEquiv_charpoly {m : ℕ} (hm : 1 ≤ m) (ρ : K) :
    spectralVariableEquiv K m
        (by omega) (Algebra.DiagonalObstruction.spectralMatrix K m ρ).charpoly =
      C ((-1 : K) ^ (m + 1)) * E K[X] m m X 0 (C ρ) := by
  have h := spectral_charpoly_eval_eq_E (R := K[X]) hm X (C ρ)
  have hc : (Algebra.DiagonalObstruction.spectralMatrix K[X] m (C ρ)).charpoly =
      ((Algebra.DiagonalObstruction.spectralMatrix K m ρ).charpoly).map C := by
    rw [← Matrix.charpoly_map, Algebra.DiagonalObstruction.spectralMatrix_map]
  rw [hc, eval_map] at h
  rw [spectralVariableEquiv_apply, comp]
  convert h using 1
  · congr 1
    simp only [map_neg, map_natCast]
    ring
  · simp only [map_pow, map_neg, map_one]

theorem irreducible_factor_transport {m : ℕ} (hm : 1 ≤ m) (ρ : K)
    (F : K[X]) (hF : Irreducible F)
        (hdiv : F ∣ (Algebra.DiagonalObstruction.spectralMatrix K m ρ).charpoly) :
    ∃ G : K[X], Irreducible G ∧ G ∣ E K[X] m m X 0 (C ρ) ∧ G.natDegree = F.natDegree := by
  refine ⟨spectralVariableEquiv K m (by omega) F,
    (spectralVariableEquiv_irreducible_iff m (by omega) F).mpr hF, ?_,
    spectralVariableEquiv_natDegree m (by omega) F⟩
  have hd := map_dvd (spectralVariableEquiv K m (by omega)).toRingHom hdiv
  change spectralVariableEquiv K m (by omega) F ∣
    spectralVariableEquiv K m
        (by omega) (Algebra.DiagonalObstruction.spectralMatrix K m ρ).charpoly at hd
  rw [spectralVariableEquiv_charpoly hm ρ] at hd
  exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (by simp))).mp hd

theorem irreducible_ratFunc_factor_transport {m D : ℕ} (hm : 1 ≤ m)
    (F : Polynomial (RatFunc ℚ)) (hF : Irreducible F)
    (hdiv : F ∣ (Algebra.DiagonalObstruction.spectralMatrix (RatFunc ℚ) m RatFunc.X).charpoly)
        (hdegree : D < F.natDegree) :
    ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ E (Polynomial (RatFunc ℚ)) m m X 0 (C RatFunc.X) ∧ D < G.natDegree := by
  obtain ⟨G, hi, hd, hn⟩ := irreducible_factor_transport hm RatFunc.X F hF hdiv
  exact ⟨G, hi, hd, hn ▸ hdegree⟩

end Rhone.Analysis.DiagonalObstruction
