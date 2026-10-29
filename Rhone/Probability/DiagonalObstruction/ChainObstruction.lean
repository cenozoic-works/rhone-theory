/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DiagonalObstruction.Surviving
public import Rhone.Analysis.DiagonalObstruction.DeterminantNonzero
public import Rhone.Algebra.BoundedDenominator

/-! # The all-degree obstruction for the diagonal chain -/

@[expose] public section

namespace Rhone.Probability.DiagonalObstruction

open Polynomial DiagonalChain Analysis.RareAlleleHierarchy RareAlleleHierarchy

abbrev ChainCoefficient := RatFunc ℚ
abbrev ChainPolynomial := Polynomial ChainCoefficient
abbrev ChainField := RatFunc ChainCoefficient

noncomputable def chainRhoPolynomial : ChainPolynomial := C RatFunc.X
noncomputable def chainTheta : ChainField := algebraMap ChainPolynomial ChainField X
noncomputable def chainRho : ChainField := algebraMap ChainPolynomial ChainField chainRhoPolynomial

noncomputable def chainValue (m : ℕ) : ChainField :=
  algebraMap ChainPolynomial ChainField (W m X chainRhoPolynomial) /
    algebraMap ChainPolynomial ChainField (frakE m X chainRhoPolynomial)

theorem chainClearing_ne_zero (m : ℕ) :
    frakE m (X : ChainPolynomial) chainRhoPolynomial ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact Analysis.DiagonalObstruction.E_mutationPolynomial_ne_zero
      (by have := (Finset.mem_Icc.mp hk).1; omega) RatFunc.X

theorem unbounded_chain_denominator_factor (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : ChainPolynomial, Irreducible G ∧
      G ∣ (chainValue m).denom ∧ D < G.natDegree := by
  obtain ⟨m, hm, G, hirr, hdiv, hn, hdegree⟩ := unbounded_surviving_E_mm_factor_degree D
  refine ⟨m, hm, G, hirr, ?_, hdegree⟩
  apply Rhone.Algebra.prime_dvd_denom (chainClearing_ne_zero m) rfl hirr.prime
  · apply dvd_trans hdiv
    exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩)
  · exact hn

theorem no_uniform_chain_expression (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr ChainCoefficient,
      Rhone.Algebra.DAdm chainTheta 0 chainRho D e ∧
      Rhone.Algebra.Expr.eval chainTheta 0 chainRho e = chainValue m := by
  obtain ⟨m, hm, G, hirr, hdiv, hdegree⟩ := unbounded_chain_denominator_factor D
  refine ⟨m, hm, ?_⟩
  rintro ⟨e, hadm, heval⟩
  have hzero : Rhone.Algebra.BoundedDen D (0 : ChainField) := by
    simpa using (Rhone.Algebra.boundedDen_of_poly D (0 : ChainPolynomial))
  have hbound := Rhone.Algebra.natDegree_le_of_dvd_denom_eval (Rhone.Algebra.boundedDen_of_poly D X)
      hzero
    (Rhone.Algebra.boundedDen_of_poly D chainRhoPolynomial) hadm hirr
    (by
      change G ∣ (Rhone.Algebra.Expr.eval chainTheta 0 chainRho e).denom
      rw [heval]
      exact hdiv)
  omega

theorem chainValue_eq_of_isDiagChain {v : ℕ → ℕ → ChainField}
    (hv : IsDiagChain chainTheta chainRho v) {m : ℕ} (hm : 2 ≤ m) :
    v m 0 = chainValue m := by
  have h := clearedChain_eq_frakE_mul chainTheta chainRho hv m (by omega) 0 (by omega)
  have hW := W_map (algebraMap ChainPolynomial ChainField) m
    (X : ChainPolynomial) chainRhoPolynomial
  have hD := frakE_map (algebraMap ChainPolynomial ChainField) m
    (X : ChainPolynomial) chainRhoPolynomial
  change W m chainTheta chainRho = frakE m chainTheta chainRho * v m 0 at h
  simp only [chainTheta, chainRho] at h
  rw [← hW, ← hD] at h
  have hd := Rhone.Algebra.algebraMap_ne_zero (chainClearing_ne_zero m)
  apply (eq_div_iff hd).2
  simpa only [mul_comm] using h.symm

theorem no_uniform_expression_of_isDiagChain (D : ℕ) {v : ℕ → ℕ → ChainField}
    (hv : IsDiagChain chainTheta chainRho v) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr ChainCoefficient,
      Rhone.Algebra.DAdm chainTheta 0 chainRho D e ∧
      Rhone.Algebra.Expr.eval chainTheta 0 chainRho e = v m 0 := by
  obtain ⟨m, hm, h⟩ := no_uniform_chain_expression D
  exact ⟨m, hm, (chainValue_eq_of_isDiagChain hv hm) ▸ h⟩

end Rhone.Probability.DiagonalObstruction
