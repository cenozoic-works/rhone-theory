/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ExplicitFormula.Block
public import Rhone.Probability.SlotDeletion.Surj
public import Rhone.LinearAlgebra.Recursion.Exist
public import Rhone.LinearAlgebra.Recursion.Unique

/-! # The explicit formula for the biallelic two-locus sampling probability -/

@[expose] public section

namespace Rhone.Probability.ExplicitFormula

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion
open Closure

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}

theorem q_eq_qExplicit {q : Config 2 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config 2 2) :
    q ξ = qExplicit θA θB ρ πA πB ξ := by
  have h := q_xi_eq_sum_Gcfg_coeff_mul_Phi hθA hθB hρ hq hπA hπB (matchOf ξ) isMatching_matchOf
      (alphaOf ξ) (betaOf ξ)
  rw [xi_matchOf] at h
  rw [h, qExplicit]
  refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ =>
    Finset.sum_congr rfl fun d3 _ => ?_
  rw [PhiX, Phi_eq_PhiTab hθA hθB hρ hq hπA hπB (d1 + d2) d1 d2 d3 le_rfl]

theorem qExplicit_isSolution
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    IsSolution θA θB ρ πA πB (qExplicit θA θB ρ πA πB) := by
  obtain ⟨q, hq⟩ := exists_isSolution (KA := 2) (KB := 2) (πA := πA) (πB := πB) hθA hθB hρ
  have : qExplicit θA θB ρ πA πB = q :=
    funext fun ξ => (q_eq_qExplicit hθA hθB hρ hπA hπB hq ξ).symm
  rw [this]
  exact hq

end Rhone.Probability.ExplicitFormula
