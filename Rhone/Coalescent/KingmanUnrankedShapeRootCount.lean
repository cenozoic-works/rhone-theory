/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootEquiv
/-!
# Cardinality recurrence for unranked shapes from the root decomposition

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
theorem card_unranked_shape_recurrence (n : ℕ) (hn : 2 ≤ n) :
  Fintype.card (Combinatorics.UnrankedShape n) =
    (∑ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1),
      Fintype.card (Combinatorics.UnrankedShape k) * Fintype.card
          (Combinatorics.UnrankedShape (n - k))) +
    if Even n then
      Fintype.card (Combinatorics.UnrankedShape (n / 2)) *
        (Fintype.card (Combinatorics.UnrankedShape (n / 2)) + 1) / 2
    else 0 := by
  classical
  let : Fintype (if Even n then Sym2 (Combinatorics.UnrankedShape (n / 2)) else Empty) := by
    split_ifs <;> infer_instance
  have hc := Fintype.card_congr (unrankedShapeRootEquiv n hn)
  rw [Fintype.card_sum, Fintype.card_sigma] at hc
  simp only [Fintype.card_prod] at hc
  rw [← Finset.sum_subtype (Ico 1 ((n - 1) / 2+1)) (fun _ => Iff.rfl)
    (fun k => Fintype.card (Combinatorics.UnrankedShape k) * Fintype.card
        (Combinatorics.UnrankedShape (n - k)))] at hc
  by_cases he : Even n
  · simpa only [ite_eq_left he, Sym2.card, Nat.choose_two_right, Nat.add_sub_cancel,
      Nat.mul_comm] using hc
  · simpa only [ite_eq_right he, Fintype.card_empty] using hc
end Rhone.Coalescent
