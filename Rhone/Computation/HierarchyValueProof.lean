/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.HierarchyScanProof

/-! # Identifying the finite hierarchy with protected centred moments -/

@[expose] public section

namespace Rhone.Computation

theorem hierarchyDegrees_preserve_prefix (p : Params) (value : Nat → Nat → Nat → Rat)
    (laws : HierarchyValueLaws p value) (na nb : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) (n : Nat) :
    ∃ tab,
      (List.range n).foldlM (fun current degree =>
        (List.range (na + 1)).foldlM
          (fun current row => hierarchyStep p nb degree row current) current)
        ⟨nb, Array.replicate ((na + 1) * (nb + 1)) #[]⟩ = .ok tab ∧
      HierarchyPrefix value na nb n 0 tab := by
  induction n with
  | zero => exact ⟨_, rfl, hierarchyPrefix_initial value na nb⟩
  | succ n ih =>
    obtain ⟨middle, hm, hmiddle⟩ := ih
    obtain ⟨tab, ht, htab⟩ := hierarchyRows_preserve_prefix p value laws na nb n middle
      hθA hθB hρ hmiddle (na + 1) le_rfl
    refine ⟨tab, ?_, htab.next_degree⟩
    rw [List.range_succ (n := n), List.foldlM_append, hm]
    rw [show (Except.ok middle : Except String PhiTable) = pure middle from rfl]
    simp only [pure_bind, List.foldlM_cons, List.foldlM_nil, bind_pure]
    exact ht

theorem phiTable_eq_value (p : Params) (value : Nat → Nat → Nat → Rat)
    (laws : HierarchyValueLaws p value) (na nb : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) :
    ∃ tab, phiTable p na nb = .ok tab ∧
      ∀ i j t, i ≤ na → j ≤ nb → t ≤ min i j → tab.get i j t = value i j t := by
  obtain ⟨tab, ht, htab⟩ := hierarchyDegrees_preserve_prefix p value laws na nb
    hθA hθB hρ (na + nb + 1)
  refine ⟨tab, ?_, ?_⟩
  · rw [phiTable_eq_foldlM]
    exact ht
  · exact fun i j t hi hj hs => htab.complete i j t hi hj hs

theorem phiTable_eq_Phi (p : Params) (na nb : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hπA : (∑ i : Fin 2, p.piA.getD i.val 0) = 1)
    (hπB : (∑ j : Fin 2, p.piB.getD j.val 0) = 1) :
    ∃ tab, phiTable p na nb = .ok tab ∧
      ∀ i j t, i ≤ na → j ≤ nb → t ≤ min i j →
        tab.get i j t = Rhone.Probability.Multilinear.Phi
          (Rhone.LinearAlgebra.Recursion.q
            (πA := fun k : Fin 2 => p.piA.getD k.val 0)
            (πB := fun k : Fin 2 => p.piB.getD k.val 0) hθA hθB hρ)
          (fun k : Fin 2 => p.piA.getD k.val 0)
          (fun k : Fin 2 => p.piB.getD k.val 0) i j t := by
  apply phiTable_eq_value
  · exact hierarchyValueLaws_of_solution p _ hθA hθB hρ
      (Rhone.LinearAlgebra.Recursion.q_isSolution hθA hθB hρ) hπA hπB
  · exact hθA
  · exact hθB
  · exact hρ

end Rhone.Computation
