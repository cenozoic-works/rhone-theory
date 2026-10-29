/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanBranchGeometry
public import Rhone.Coalescent.SmcPrimeRootGeometry

/-! # Finite tree root height is the last Kingman merger clock -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem metric_tree_root_height (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (hN : 2 ≤ N) :
    rootHeight (metricTreeFromHistory N (fun j : Fin N => ω j.val)) = (ω (N - 1)).1.1 := by
  let T := metricTreeFromHistory N (fun j : Fin N => ω j.val)
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hup : rootHeight T ≤ (ω (N - 1)).1.1 := by
    apply root_height_le_of_branch_bounds T _ (hvalid (N - 1)).1
    intro i _
    obtain ⟨k, right, he⟩ := metric_tree_branch_from_child N (fun j : Fin N => ω j.val) i
    have hb := history_child_branch_positive N ω hinit hvalid hstep k right
    rw [he, hb.2.2]
    apply hmono
    have := k.isLt
    omega
  let k : Fin (N - 1) := ⟨N - 2, by omega⟩
  obtain ⟨i, he⟩ := historyChildBranch_mem_tree N (fun j : Fin N => ω j.val) k false
  have hb := history_child_branch_positive N ω hinit hvalid hstep k false
  have hlo := branch_hi_le_root T i (by rw [he]; exact hb.1)
  have hindex : k.val + 1 = N - 1 := by dsimp only [k]; omega
  rw [he, hb.2.2, hindex] at hlo
  exact le_antisymm hup hlo

end Rhone.Coalescent.SmcPrime
