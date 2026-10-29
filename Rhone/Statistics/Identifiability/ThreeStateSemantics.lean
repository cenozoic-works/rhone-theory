/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IslandThreeSpectrum
public import Rhone.Statistics.Identifiability.Admissibility

/-! # Block identities and unreachable dummy states for the three-sample model -/
set_option linter.style.longLine false

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

theorem islandThreeTree_first_block (k : ℕ) (c q : ℝ) (i j : Fin 3) :
    islandThreeTreeGenerator k c q (Fin.castLE (by decide) i) (Fin.castLE (by decide) j) =
      threeGenerator k c q i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator,threeGenerator,MarkovChain.Identifiability.totalMigration,Fin.castLE,Fin.natAdd] <;> ring

theorem islandThreeTree_pair_block (k : ℕ) (c q : ℝ) (i j : Fin 2) :
    islandThreeTreeGenerator k c q (Fin.natAdd 3 i) (Fin.natAdd 3 j) =
      MarkovChain.Identifiability.pairGenerator k c q i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator,MarkovChain.Identifiability.pairGenerator,MarkovChain.Identifiability.totalMigration,Fin.castLE,Fin.natAdd] <;> ring

theorem islandThreeTree_merger_flux (k : ℕ) (c q : ℝ) (i : Fin 3) :
    (∑ j : Fin 2, islandThreeTreeGenerator k c q (Fin.castLE (by decide) i) (Fin.natAdd 3 j)) =
      c * (MarkovChain.Identifiability.killedCount (threeShape i) : ℝ) := by
  rw [three_events_checked.2.2]
  fin_cases i <;> norm_num [islandThreeTreeGenerator,Fin.sum_univ_two,Fin.castLE,Fin.natAdd]
  ring

theorem three_two_islands_dummy_unreachable (c q t : ℝ) :
    NormedSpace.exp (t • threeGenerator 0 c q) 0 2 = 0 := by
  apply matrix_exp_no_escape _ (fun i => i ≠ 2) _ t 0 2 (by decide) (by simp)
  intro i j hi hj
  have hj' : j = 2 := by simpa using hj
  subst j
  fin_cases i
  · change (0 : ℝ) = 0
    rfl
  · change 2*((0 : ℕ) : ℝ)*q = 0
    norm_num
  · exact False.elim (hi rfl)

theorem islandThreeTree_two_islands_dummy_unreachable (c q t : ℝ) :
    NormedSpace.exp (t • islandThreeTreeGenerator 0 c q) 0 2 = 0 := by
  apply matrix_exp_no_escape _ (fun i => i ≠ 2) _ t 0 2 (by decide) (by simp)
  intro i j hi hj
  have hj' : j = 2 := by simpa using hj
  subst j
  fin_cases i
  · change (0 : ℝ) = 0
    rfl
  · change 2*((0 : ℕ) : ℝ)*q = 0
    norm_num
  · exact False.elim (hi rfl)
  · change (0 : ℝ) = 0
    rfl
  · change (0 : ℝ) = 0
    rfl

end Rhone.Statistics.Identifiability
