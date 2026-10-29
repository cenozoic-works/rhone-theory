/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BooleanLatticeInverse.Table
public import Rhone.Probability.BooleanLatticeInverse.Assembly

/-! # The explicit sampling probability for a biallelic `B` locus -/

@[expose] public section

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear

variable {KA : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin 2 → F}

theorem q_eq_qExplicitKB2 {q : Config KA 2 → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : πB 0 + πB 1 = 1)
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA 2) :
    q ξ = LinearAlgebra.BooleanLatticeInverse.qExplicitKB2 θA θB ρ πA πB ξ := by
  refine q_eq_qExplicitKB2_of hθA hθB hρ hq hπA hπB (fun n m M lab hM => ?_) ξ
  have h := Q_centred_eq_PhiX hθA hθB hρ hq hπA hπB M hM lab
  rwa [Fintype.card_fin] at h

end Rhone.Probability.BooleanLatticeInverse
