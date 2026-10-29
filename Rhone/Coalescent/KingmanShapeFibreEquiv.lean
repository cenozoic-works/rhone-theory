/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFibreHistoryData
public import Rhone.Coalescent.KingmanShapeFibreRightInverse
/-!
# Exact root-fibre equivalence of the ranked shape quotients

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rankedShapeRootFibreMap_left_inverse (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) :
    Function.LeftInverse (rankedShapeRootFibreInverse n hn k)
      (rankedShapeRootFibreMap n hn k) := by
  intro s
  let h : Combinatorics.RankedLabelledHistory n := s.1.out
  have hsize : rankedShapeRootSize n hn (Quotient.mk (Combinatorics.rankedShapeSetoid n) h) = k :=
      by
    rw [show Quotient.mk (Combinatorics.rankedShapeSetoid n) h = s.1 from Quotient.out_eq s.1]
    exact s.2
  have hk : (firstMergerRoot n hn h).card = k.val := congrArg Subtype.val hsize
  apply Subtype.ext
  rw [rankedShapeRootFibreMap_representative n hn k s h hk (Quotient.out_eq s.1),
    rootHistoryFibreData_eq_historyData]
  let p := rootHistoryFibreHistoryData n hn k h hk
  change (rankedShapeRootFibreInverse n hn k
    ((Quotient.mk (Combinatorics.rankedShapeSetoid k.val) p.1.1,
      Quotient.mk (Combinatorics.rankedShapeSetoid (n - k.val)) p.1.2), p.2)).1 = s.1
  rw [rankedShapeRootFibreInverse_representative]
  have hrec : Quotient.mk (Combinatorics.rankedShapeSetoid n) h =
      Quotient.mk (Combinatorics.rankedShapeSetoid n)
          (firstRootHistoryAssemble n hn k p.1.1 p.1.2 p.2) :=
    Quotient.sound (rootHistoryFibreHistoryData_reconstruct n hn k h hk)
  exact hrec.symm.trans (Quotient.out_eq s.1)
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rankedShapeRootFibreEquiv (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) :
    {s : Combinatorics.RankedShape n // rankedShapeRootSize n hn s = k} ≃
      ((Combinatorics.RankedShape k.val × Combinatorics.RankedShape (n - k.val)) ×
        Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :=
  { toFun := rankedShapeRootFibreMap n hn k
    invFun := rankedShapeRootFibreInverse n hn k
    left_inv := rankedShapeRootFibreMap_left_inverse n hn k
    right_inv := rankedShapeRootFibreMap_right_inverse n hn k }
end Rhone.Coalescent
