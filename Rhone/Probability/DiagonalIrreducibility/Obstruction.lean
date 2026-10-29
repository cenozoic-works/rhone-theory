/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalIrreducibility.Generic
public import Rhone.Algebra.BoundedDenominator
public import Rhone.Probability.DiagonalChain.Small

/-! # A degree-four irreducible denominator factor of the diagonal chain at `m = 3` -/

@[expose] public section

namespace Rhone.Probability.DiagonalIrreducibility
open Polynomial DiagonalChain Analysis.RareAlleleHierarchy RareAlleleHierarchy

abbrev F := RatFunc ℚ
abbrev P := Polynomial F
abbrev L := RatFunc F

noncomputable def rhoP : P := C RatFunc.X
noncomputable def thetaL : L := algebraMap P L X
noncomputable def rhoL : L := algebraMap P L rhoP
noncomputable def E2 : P := ED 2 X rhoP
noncomputable def W3 : P := W 3 X rhoP
noncomputable def D3 : P := frakE 3 X rhoP
noncomputable def chainThree : L := algebraMap P L W3 / algebraMap P L D3

theorem E33U_eq_ED : Algebra.DiagonalIrreducibility.E33U = ED 3 (X : P) rhoP := by
  rw [Algebra.DiagonalIrreducibility.E33U, Algebra.DiagonalIrreducibility.E33Theta_eq_E]
  have h := Rhone.LinearAlgebra.Tridiag.E_map (Polynomial.mapRingHom (algebraMap (Polynomial ℚ) F))
    3 3 (X : Polynomial (Polynomial ℚ)) 0 (C X)
  simpa [ED, rhoP, RatFunc.algebraMap_X] using h

theorem E2_expansion : E2 =
    4 * ((X+2) * rhoP^2 + (X+2)*(3*X+13)*rhoP + 2*(X+1)*(X+3)*(X+6)) := by
  rw [E2, ED, Rhone.LinearAlgebra.Tridiag.E_eq_cont]
  norm_num [Rhone.LinearAlgebra.Tridiag.cont, Rhone.LinearAlgebra.Tridiag.dcoef,
    Rhone.LinearAlgebra.Tridiag.bcoef, Rhone.LinearAlgebra.Tridiag.ccoef]
  ring

theorem E2_degree : E2.natDegree = 3 := by
  rw [E2_expansion, rhoP]
  compute_degree!

theorem E2_ne_zero : E2 ≠ 0 := by
  intro h
  have hd := E2_degree
  simp [h] at hd

theorem W3_expansion : W3 = 6912 * (2*(X+4)*rhoP + (3*X+8)*(X+6)) := W_three X rhoP

theorem W3_degree : W3.natDegree = 2 := by
  rw [W3_expansion, rhoP]
  compute_degree!

theorem W3_ne_zero : W3 ≠ 0 := by
  intro h
  have hd := W3_degree
  simp [h] at hd

theorem E33U_not_dvd_W3 : ¬ Algebra.DiagonalIrreducibility.E33U ∣ W3 := by
  intro h
  have hd := natDegree_le_of_dvd h W3_ne_zero
  rw [Algebra.DiagonalIrreducibility.E33U_degree, W3_degree] at hd
  omega

theorem D3_factor : D3 = E2 * Algebra.DiagonalIrreducibility.E33U := by
  rw [D3, frakE_succ X rhoP 2 (by omega),
    frakE_succ X rhoP 1 (by omega), frakE_one, one_mul, E33U_eq_ED]
  rfl

theorem D3_ne_zero : D3 ≠ 0 := by
  rw [D3_factor]
  exact mul_ne_zero E2_ne_zero Algebra.DiagonalIrreducibility.E33U_irreducible.ne_zero

theorem E33U_dvd_chainThree_denom : Algebra.DiagonalIrreducibility.E33U ∣ chainThree.denom := by
  apply Rhone.Algebra.prime_dvd_denom D3_ne_zero rfl
      Algebra.DiagonalIrreducibility.E33U_irreducible.prime
  · rw [D3_factor]; exact dvd_mul_left Algebra.DiagonalIrreducibility.E33U E2
  · exact E33U_not_dvd_W3

theorem four_le_of_chainThree {D : ℕ} {e : Algebra.Expr F}
    (he : Algebra.DAdm thetaL 0 rhoL D e) (hv : Algebra.Expr.eval thetaL 0 rhoL e = chainThree) :
        4 ≤ D := by
  have hzero : Algebra.BoundedDen D (0 : L) := by simpa using (Algebra.boundedDen_of_poly D (0 : P))
  have h := Algebra.natDegree_le_of_dvd_denom_eval (Algebra.boundedDen_of_poly D X) hzero
    (Algebra.boundedDen_of_poly D rhoP) he Algebra.DiagonalIrreducibility.E33U_irreducible
      (by change Algebra.DiagonalIrreducibility.E33U ∣ (Algebra.Expr.eval thetaL 0 rhoL e).denom
          rw [hv]; exact E33U_dvd_chainThree_denom)
  rwa [Algebra.DiagonalIrreducibility.E33U_degree] at h

theorem no_degree_three_chainThree :
    ¬ ∃ e : Algebra.Expr F, Algebra.DAdm thetaL 0 rhoL 3 e ∧ Algebra.Expr.eval thetaL 0 rhoL e =
        chainThree := by
  rintro ⟨e, he, hv⟩
  have := four_le_of_chainThree he hv
  omega

theorem eq_chainThree_of_isDiagChain {v : ℕ → ℕ → L}
    (hv : IsDiagChain thetaL rhoL v) : v 3 0 = chainThree := by
  have h := clearedChain_eq_frakE_mul thetaL rhoL hv 3 (by omega) 0 (by omega)
  have hW := W_map (algebraMap P L) 3 (X : P) rhoP
  have hD := frakE_map (algebraMap P L) 3 (X : P) rhoP
  change W 3 thetaL rhoL = frakE 3 thetaL rhoL * v 3 0 at h
  simp only [thetaL, rhoL] at h
  rw [← hW, ← hD] at h
  have hd : algebraMap P L D3 ≠ 0 := Rhone.Algebra.algebraMap_ne_zero D3_ne_zero
  apply (eq_div_iff hd).2
  simpa [chainThree, W3, D3, mul_comm] using h.symm

theorem no_degree_three_of_isDiagChain {v : ℕ → ℕ → L}
    (hv : IsDiagChain thetaL rhoL v) :
    ¬ ∃ e : Algebra.Expr F, Algebra.DAdm thetaL 0 rhoL 3 e ∧ Algebra.Expr.eval thetaL 0 rhoL e = v 3
        0 := by
  rw [eq_chainThree_of_isDiagChain hv]
  exact no_degree_three_chainThree

end Rhone.Probability.DiagonalIrreducibility
