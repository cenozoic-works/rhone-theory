/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootNormalization
/-!
# Identify the unranked root decomposition target with the endpoint target

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def unrankedShapeRootTargetEndpointEquiv (n : ℕ) (hn : 2 ≤ n) :
    ((Σ k : {k : ℕ // k ∈ Finset.Ico 1 ((n - 1) / 2+1)},
      Combinatorics.UnrankedShape k.val × Combinatorics.UnrankedShape (n - k.val)) ⊕
      (if Even n then Sym2 (Combinatorics.UnrankedShape (n / 2)) else Empty)) ≃
    BinaryHierarchyRootTarget n := by
  classical
  refine Equiv.sumCongr (Equiv.sigmaCongrRight (fun k => ?_)) ?_
  · have hk := mem_Ico.mp k.property
    exact Equiv.prodCongr (Combinatorics.unrankedShapeEndpointEquiv k.val hk.1)
      (Combinatorics.unrankedShapeEndpointEquiv (n - k.val) (by omega))
  · by_cases he : Even n
    · rw [ite_eq_left he, ite_eq_left he]
      let e := Combinatorics.unrankedShapeEndpointEquiv (n / 2) (by omega : 1 ≤ n / 2)
      exact {
        toFun := Sym2.map e
        invFun := Sym2.map e.symm
        left_inv := by intro p; induction p using Sym2.ind; simp
        right_inv := by intro p; induction p using Sym2.ind; simp }
    · simpa only [ite_eq_right he] using (Equiv.refl Empty)

end Rhone.Coalescent
