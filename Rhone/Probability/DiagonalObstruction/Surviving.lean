/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DiagonalObstruction.Unbounded
public import Rhone.Probability.DiagonalObstruction.DistinguishedPole

/-! # Unbounded irreducible factors of `E_{m,m}` that survive in the cleared-chain numerator -/

@[expose] public section

namespace Rhone.Probability.DiagonalObstruction

open Polynomial

theorem spectralVariableEquiv_chainNumerator {m : ℕ} (hm : 2 ≤ m) :
    Analysis.DiagonalObstruction.spectralVariableEquiv (RatFunc ℚ) m (by omega)
      ((spectralChainNumerator m).map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) =
      DiagonalChain.W m X (C RatFunc.X) := by
  let f : Polynomial (Polynomial ℚ) →+* Polynomial (RatFunc ℚ) :=
    Polynomial.mapRingHom (algebraMap (Polynomial ℚ) (RatFunc ℚ))
  let e := Analysis.DiagonalObstruction.spectralVariableEquiv (RatFunc ℚ) m (by omega : m ≠ 0)
  change e (f (DiagonalChain.W m (C (C (-1 / (m : ℚ))) * X) (C X))) = _
  rw [DiagonalChain.W_map]
  change e.toRingHom (DiagonalChain.W m (f (C (C (-1 / (m : ℚ))) * X)) (f (C X))) = _
  rw [DiagonalChain.W_map]
  have hm0 : (m : RatFunc ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hθ : e (f (C (C (-1 / (m : ℚ))) * X)) = X := by
    dsimp only [e, f]
    rw [Analysis.DiagonalObstruction.spectralVariableEquiv_apply]
    simp only [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      mul_comp, C_comp, X_comp, RatFunc.algebraMap_C]
    have hc : RatFunc.C (-1 / (m : ℚ)) * (-(m : RatFunc ℚ)) = 1 := by
      simp [map_div₀, hm0]
    rw [← mul_assoc, ← C_mul, hc, C_1, one_mul]
  have hρ : e (f (C X)) = C RatFunc.X := by
    dsimp only [e, f]
    rw [Analysis.DiagonalObstruction.spectralVariableEquiv_apply]
    simp
  change DiagonalChain.W m (e (f (C (C (-1 / (m : ℚ))) * X))) (e (f (C X))) = _
  rw [hθ, hρ]

theorem unbounded_surviving_E_mm_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m X 0 (C RatFunc.X) ∧
      ¬ G ∣ DiagonalChain.W m X (C RatFunc.X) ∧ D < G.natDegree := by
  obtain ⟨m, F, hm, hF, _, hzero, hirr, hdiv, hdegree⟩ :=
    Analysis.DiagonalObstruction.exists_irreducible_distinguished_factor_gt D
  let e := Analysis.DiagonalObstruction.spectralVariableEquiv (RatFunc ℚ) m (by omega : m ≠ 0)
  refine ⟨m, hm, e (Analysis.DiagonalObstruction.rationalFunctionFactor F),
    (Analysis.DiagonalObstruction.spectralVariableEquiv_irreducible_iff m
        (by omega) _).mpr hirr, ?_, ?_, ?_⟩
  · rw [Analysis.DiagonalObstruction.rationalFunctionFactor_spectralPolynomial] at hdiv
    have hd := map_dvd e.toRingHom hdiv
    change e (Analysis.DiagonalObstruction.rationalFunctionFactor F) ∣ e
        (Algebra.DiagonalObstruction.spectralMatrix (RatFunc ℚ) m RatFunc.X).charpoly at hd
    rw [Analysis.DiagonalObstruction.spectralVariableEquiv_charpoly (by omega) RatFunc.X] at hd
    exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (by simp))).mp hd
  · intro hd
    rw [← spectralVariableEquiv_chainNumerator hm] at hd
    have hb := (map_dvd_iff e).mp hd
    exact distinguishedFactor_not_dvd_chain_fraction hm F hF hzero hb
  · rw [Analysis.DiagonalObstruction.spectralVariableEquiv_natDegree]
    exact hdegree

end Rhone.Probability.DiagonalObstruction
