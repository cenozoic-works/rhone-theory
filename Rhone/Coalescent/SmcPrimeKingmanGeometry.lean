/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanHistory
public import Rhone.Coalescent.SmcPrimeLengthGeometry

/-!
# Normalization of the SMC′ initial tree

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem metric_tree_from_history_normalized (N : ℕ) (h : KingmanHistory N) :
    TreeNormalized (metricTreeFromHistory N h) := by
  have hchild (k : Fin (N - 1)) (right : Bool) :
      (historyChildBranch N h k right).2.1 ≤ (historyChildBranch N h k right).2.2 ∧
      ((historyChildBranch N h k right).1 = ∅ ∨
        (historyChildBranch N h k right).1 = Finset.univ →
        (historyChildBranch N h k right).2.2 = (historyChildBranch N h k right).2.1) := by
    cases he : ((historyExtension N h) (k.val + 1)).2.2 with
    | inl terminal =>
      simpa only [historyChildBranch, he] using finite_branch_normalized (N := N) ∅ 0 0
    | inr event =>
      cases event with
      | inl ij =>
        by_cases hp : ij.1 < ij.2 ∧ ij.2 < ((historyExtension N h) k.val).1.2.2.1
        · simpa only [historyChildBranch, he, hp, and_self, ↓reduceIte] using
            finite_branch_normalized (historyClade N h k.val
              (IntervalProcess.liveLabelAt ((historyExtension N h) k.val).1
                (if right then ij.2 else ij.1)))
              (pairBirthTime (historyExtension N h) k.val
                (IntervalProcess.liveLabelAt ((historyExtension N h) k.val).1
                  (if right then ij.2 else ij.1)))
              ((historyExtension N h) (k.val + 1)).1.1
        · simpa only [historyChildBranch, he, hp, and_self, ↓reduceIte] using
            finite_branch_normalized (N := N) ∅ 0 0
      | inr splitEvent =>
        simpa only [historyChildBranch, he] using finite_branch_normalized (N := N) ∅ 0 0
  intro i
  apply (show ∀ b ∈ (List.finRange (N - 1)).flatMap
      (fun k => [historyChildBranch N h k false, historyChildBranch N h k true]),
      b.2.1 ≤ b.2.2 ∧ (b.1 = ∅ ∨ b.1 = Finset.univ → b.2.2 = b.2.1) from ?_)
      _ (List.get_mem _ i)
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨k, _, hb⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact hchild k false
  · exact hchild k true

end Rhone.Coalescent.SmcPrime
