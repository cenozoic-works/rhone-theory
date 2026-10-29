/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootFirstSlot
public import Rhone.Coalescent.KingmanShapeRootSize
/-!
# The map from ranked shapes of a given root size to daughter shapes and slots

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rankedShapeRootFibreMap (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (s : {s : Combinatorics.RankedShape n // rankedShapeRootSize n hn s = k}) :
    ((Combinatorics.RankedShape k.val × Combinatorics.RankedShape (n - k.val)) ×
      Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) := by
  let h : Combinatorics.RankedLabelledHistory n := s.1.out
  let A := firstMergerRoot n hn h
  let p := firstRootHistoryDecomposition n hn h
  have hsize : rankedShapeRootSize n hn (Quotient.mk (Combinatorics.rankedShapeSetoid n) h) = k :=
      by
    rw [show Quotient.mk (Combinatorics.rankedShapeSetoid n) h = s.1 from Quotient.out_eq s.1]
    exact s.2
  have hA : A.card = k.val := congrArg Subtype.val hsize
  have hB : (univ \ A).card = n - k.val := by
    have hc := rootPartition_card A
    omega
  exact ⟨⟨Equiv.cast (congrArg Combinatorics.RankedShape hA)
      (Quotient.mk (Combinatorics.rankedShapeSetoid A.card) p.1.1),
    Equiv.cast (congrArg Combinatorics.RankedShape hB)
      (Quotient.mk (Combinatorics.rankedShapeSetoid (univ \ A).card) p.1.2)⟩,
    Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving (congrArg (fun a => a - 1) hA)
      (congrArg (fun a => a - 1) hB)) p.2⟩
end Rhone.Coalescent
