/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootAssemblyRoot
public import Rhone.Coalescent.KingmanShapeRootFibreMap
public import Rhone.Coalescent.KingmanShapeAssemblyDescent
/-!
# Daughter ranked shapes assemble into the ranked root-size fibre

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rankedShapeRootFibreInverse (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (p : ((Combinatorics.RankedShape k.val × Combinatorics.RankedShape (n - k.val)) ×
      Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))) :
    {s : Combinatorics.RankedShape n // rankedShapeRootSize n hn s = k} := by
  let h := firstRootHistoryAssemble n hn k p.1.1.out p.1.2.out p.2
  refine ⟨Quotient.mk (Combinatorics.rankedShapeSetoid n) h, Subtype.ext ?_⟩
  exact firstMergerRoot_card_firstRootHistoryAssemble n hn k p.1.1.out p.1.2.out p.2
theorem rankedShapeRootFibreInverse_val (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (p : ((Combinatorics.RankedShape k.val × Combinatorics.RankedShape (n - k.val)) ×
      Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1))) :
    (rankedShapeRootFibreInverse n hn k p).1 =
      Quotient.mk (Combinatorics.rankedShapeSetoid n)
        (firstRootHistoryAssemble n hn k p.1.1.out p.1.2.out p.2) := rfl
theorem rankedShapeRootFibreInverse_representative (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (h : Combinatorics.RankedLabelledHistory k.val)
        (g : Combinatorics.RankedLabelledHistory (n - k.val))
    (s : Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) :
    (rankedShapeRootFibreInverse n hn k
      ((Quotient.mk (Combinatorics.rankedShapeSetoid k.val) h,
        Quotient.mk (Combinatorics.rankedShapeSetoid (n - k.val)) g),s)).1 =
      Quotient.mk (Combinatorics.rankedShapeSetoid n) (firstRootHistoryAssemble n hn k h g s) := by
  apply Quotient.sound
  apply firstRootHistoryAssemble_shape_rel
  · exact @Quotient.mk_out _ (Combinatorics.rankedShapeSetoid k.val) h
  · exact @Quotient.mk_out _ (Combinatorics.rankedShapeSetoid (n - k.val)) g
end Rhone.Coalescent
