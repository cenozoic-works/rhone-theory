/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic
public import Rhone.Probability.SlotDeletion.Matrix

/-! # Block Cramer identity `E_{i,j} Φ^{i,j} = adj(T^{(i,j)}) R^{i,j}` with explicit entries -/

@[expose] public section

namespace Rhone.Probability.DenominatorEquation

open Matrix LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear
open SlotDeletion LinearAlgebra.Tridiag Analysis.RecombinationExpansion
  LinearAlgebra.RecombinationExpansion

section Adjugate

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

theorem U_eq_adjugate (i j : ℕ) (θA θB ρ : R) (hE : E R i j θA θB ρ ≠ 0) :
    Analysis.DenominatorEquation.U R i j θA θB ρ = adjugate (T R i j θA θB ρ) := by
  have hd : (T R i j θA θB ρ).det = E R i j θA θB ρ := rfl
  have h1 : (E R i j θA θB ρ) • Analysis.DenominatorEquation.U R i j θA θB ρ
      = (E R i j θA θB ρ) • adjugate (T R i j θA θB ρ) := by
    calc (E R i j θA θB ρ) • Analysis.DenominatorEquation.U R i j θA θB ρ
        = ((E R i j θA θB ρ) • (1 : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R))
            * Analysis.DenominatorEquation.U R i j θA θB ρ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (adjugate (T R i j θA θB ρ) * T R i j θA θB ρ) * Analysis.DenominatorEquation.U R i j θA
          θB ρ := by
          rw [Matrix.adjugate_mul, hd]
      _ = adjugate (T R i j θA θB ρ) *
          (T R i j θA θB ρ * Analysis.DenominatorEquation.U R i j θA θB ρ) := mul_assoc _ _ _
      _ = adjugate (T R i j θA θB ρ)
            * ((E R i j θA θB ρ) • (1 : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R)) := by
          rw [Analysis.DenominatorEquation.T_mul_U]
      _ = (E R i j θA θB ρ) • adjugate (T R i j θA θB ρ) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
  ext p q
  have h2 := congrFun (congrFun h1 p) q
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ hE h2

end Adjugate

section Cramer

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem E_smul_Phi (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i j : ℕ) :
    (E F i j θA θB ρ) • (fun t : Fin (min i j + 1) => Phi q πA πB i j (t : ℕ))
      = Analysis.DenominatorEquation.U F i j θA θB ρ *ᵥ
          (fun t : Fin (min i j + 1) => phiRecursionSource q πA πB i j (t : ℕ)) := by
  have h := congrArg (fun x => Analysis.DenominatorEquation.U F i j θA θB ρ *ᵥ x)
    (T_mulVec_Phi_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i j)
  simp only [Matrix.mulVec_mulVec, Analysis.DenominatorEquation.U_mul_T, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h
  exact h

theorem E_mul_Phi_apply (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i j : ℕ)
    (t : Fin (min i j + 1)) :
    (E F i j θA θB ρ) * Phi q πA πB i j (t : ℕ)
      = ∑ s : Fin (min i j + 1), Analysis.DenominatorEquation.U F i j θA θB ρ t s *
          phiRecursionSource q πA πB i j (s : ℕ) := by
  have h := congrFun (E_smul_Phi hθA hθB hρ hq hπA hπB i j) t
  simpa [Matrix.mulVec, dotProduct] using h

theorem E_mul_Phi_zero (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i j : ℕ) :
    (E F i j θA θB ρ) * Phi q πA πB i j 0
      = ∑ s : Fin (min i j + 1), Analysis.DenominatorEquation.ell F i j θA θB ρ (s : ℕ) *
          phiRecursionSource q πA πB i j (s : ℕ) := by
  have h := E_mul_Phi_apply hθA hθB hρ hq hπA hπB i j 0
  rw [show ((0 : Fin (min i j + 1)) : ℕ) = 0 from rfl] at h
  rw [h]
  exact Finset.sum_congr rfl fun s _ => by rw [Analysis.DenominatorEquation.U_zero_apply]

end Cramer

end Rhone.Probability.DenominatorEquation
