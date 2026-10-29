/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanTreeLaw
public import Rhone.Coalescent.SmcPrimeProposalGeometry

/-!
# Branch births of the Kingman initial tree are nonnegative

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem pair_birth_time_nonnegative (ω : EventPath)
    (ht : ∀ j, 0 ≤ (ω j).1.1) (k a : ℕ) : 0 ≤ pairBirthTime ω k a := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    unfold pairBirthTime
    split
    · split
      · exact ht _
      · exact ih
    · exact ih

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem pair_birth_time_le_current_time (ω : EventPath)
    (ht0 : 0 ≤ (ω 0).1.1) (hmono : Monotone (fun j => (ω j).1.1)) (k a : ℕ) :
    pairBirthTime ω k a ≤ (ω k).1.1 := by
  induction k with
  | zero => exact ht0
  | succ k ih =>
    unfold pairBirthTime
    split
    · split
      · exact le_rfl
      · exact ih.trans (hmono (Nat.le_succ k))
    · exact ih.trans (hmono (Nat.le_succ k))

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem metric_tree_from_history_nonnegative (N : ℕ) (h : KingmanHistory N)
    (ht : ∀ k, 0 ≤ (h k).1.1) : TreeNonnegative (metricTreeFromHistory N h) := by
  have hext : ∀ j, 0 ≤ ((historyExtension N h) j).1.1 := by
    intro j
    by_cases hj : j < N
    · simpa only [historyExtension, hj, ↓reduceDIte] using ht ⟨j, hj⟩
    · simp [historyExtension, hj, initialState]
  have hchild (k : Fin (N - 1)) (right : Bool) :
      0 ≤ (historyChildBranch N h k right).2.1 := by
    cases he : ((historyExtension N h) (k.val + 1)).2.2 with
    | inl terminal => simp [historyChildBranch, he, finiteBranch]
    | inr event =>
      cases event with
      | inl ij =>
        by_cases hp : ij.1 < ij.2 ∧ ij.2 < ((historyExtension N h) k.val).1.2.2.1
        · simp only [historyChildBranch, he, hp, and_self, ↓reduceIte, finiteBranch]
          exact pair_birth_time_nonnegative _ hext _ _
        · simp [historyChildBranch, he, hp, finiteBranch]
      | inr splitEvent => simp [historyChildBranch, he, finiteBranch]
  intro i
  apply (show ∀ b ∈ (List.finRange (N - 1)).flatMap
      (fun k => [historyChildBranch N h k false, historyChildBranch N h k true]),
      0 ≤ b.2.1 from ?_) _ (List.get_mem _ i)
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨k, _, hb⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact hchild k false
  · exact hchild k true

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem TreeNonnegative_measurable (N : ℕ) :
    MeasurableSet {T : Tree N | TreeNonnegative T} := by
  apply Rhone.Coalescent.SmcSupport.measurableSet_sigma_of_fibers
  intro m
  change MeasurableSet {f : Fin m → Branch N | ∀ i, 0 ≤ (f i).2.1}
  apply Rhone.Coalescent.SmcSupport.measurableSet_forall
  intro i
  exact measurableSet_le measurable_const (measurable_pi_apply i).snd.fst

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem kingmanHistoryLaw_tree_nonnegative (N : ℕ) :
    ∀ᵐ h ∂kingmanHistoryLaw N, TreeNonnegative (metricTreeFromHistory N h) := by
  unfold kingmanHistoryLaw
  apply (ae_map_iff (kingmanHistoryMap_measurable N).aemeasurable
    ((TreeNonnegative_measurable N).preimage (metricTreeFromHistory_measurable N))).mpr
  filter_upwards [eventProcess_chronologicalAncestryPath N false 0] with ω hω
  apply metric_tree_from_history_nonnegative
  intro k
  exact (hω.valid k.val).1

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem kingmanTreeLaw_nonnegative (N : ℕ) :
    ∀ᵐ T ∂kingmanTreeLaw N, TreeNonnegative T := by
  unfold kingmanTreeLaw
  exact (ae_map_iff (metricTreeFromHistory_measurable N).aemeasurable
    (TreeNonnegative_measurable N)).mpr (kingmanHistoryLaw_tree_nonnegative N)

end Rhone.Coalescent.SmcPrime
