/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.HierarchyValueProof
public import Rhone.Computation.PolynomialQExpansionProof

/-! # Exact correctness of finite biallelic computation -/

@[expose] public section

namespace Rhone.Computation

theorem q_eq_recursion (p : Params) (c : Config) (hp : p.valid = true)
    (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) :
    q p c = .ok (Rhone.LinearAlgebra.Recursion.q
      (πA := fun k : Fin 2 => p.piA.getD k.val 0)
      (πB := fun k : Fin 2 => p.piB.getD k.val 0)
      hθA hθB hρ (CheckerEncoding.decode c)) := by
  obtain ⟨_, _, _, _, _, _, _, hπA, hπB⟩ := (Params.valid_iff p).mp hp
  obtain ⟨tab, ht, hvalue⟩ := phiTable_eq_Phi p c.block.1 c.block.2
    hθA hθB hρ hπA hπB
  have hassemble := PolynomialEncoding.assemble_polynomial_eq_q p c tab
    ha hb hc hθA hθB hρ hπA hπB hvalue
  simp [q, hp, ha, hb, hc, ht, hassemble]

theorem q_correct (p : Params) (c : Config) (hp : p.valid = true)
    (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4) :
    ∃ (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho),
      q p c = .ok (Rhone.LinearAlgebra.Recursion.q
        (πA := fun k : Fin 2 => p.piA.getD k.val 0)
        (πB := fun k : Fin 2 => p.piB.getD k.val 0)
        hθA hθB hρ (CheckerEncoding.decode c)) := by
  obtain ⟨hθA, hθB, hρ, _⟩ := (Params.valid_iff p).mp hp
  exact ⟨hθA, hθB, hρ, q_eq_recursion p c hp ha hb hc hθA hθB hρ⟩

end Rhone.Computation
