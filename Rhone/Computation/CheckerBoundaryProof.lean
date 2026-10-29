/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerEncodingProof
public import Rhone.LinearAlgebra.Recursion.Finite

/-! # Executable singleton boundaries -/

@[expose] public section

namespace Rhone.Computation.CheckerEncoding

open LinearAlgebra.Recursion

@[simp] theorem checkerLineages_encode (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    checkerLineages (encode ξ) = ξ.n := encode_lineages ξ

@[simp] theorem checkerDiagonal_encode (p : Params)
    (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) :
    checkerDiagonal p (encode ξ) = diag p.thetaA p.thetaB p.rho ξ :=
  encode_diagonal p ξ

theorem checkerBoundary_encode_of_isSolution (p : Params)
    (q : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rat)
    (h : IsSolution p.thetaA p.thetaB p.rho (fun i => p.piA.getD i.val 0)
      (fun j => p.piB.getD j.val 0) q)
    (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (hn : ξ.n = 1) :
    checkerBoundary p (encode ξ) = q ξ := by
  rcases ξ.exists_e_of_n_eq_one hn with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
  · rw [h.bdryA]
    fin_cases i <;> simp [checkerBoundary, encode, Config.eA, incf, Function.update]
  · rw [h.bdryB]
    fin_cases j <;> simp [checkerBoundary, encode, Config.eB, incf, Function.update]
  · rw [h.bdryC]
    fin_cases i <;> fin_cases j <;>
      simp [checkerBoundary, encode, Config.eC, Config.incC, incf, Function.update]

end Rhone.Computation.CheckerEncoding
