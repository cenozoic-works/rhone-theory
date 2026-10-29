/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.IslandPairLumping
public import Rhone.Statistics.Identifiability.FirstExit

/-! # The island pair generator as a projection of the symmetric-island design generator -/

@[expose] public section

namespace Rhone.Statistics.IslandPairSpatialDesign

open Coalescent.IslandPair MarkovChain.Identifiability Identifiability

def transientCategory : Fin 2 → Category := ![some true, some false]

theorem destinationRate_succ_mul (n : ℕ) (q : ℝ) :
    destinationRate (n + 2) ((n + 1) * q) = q := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold destinationRate
  rw [show n + 2 - 1 = n + 1 by omega]
  push_cast
  field_simp

theorem pairGenerator_eq_projectedGenerator (n : ℕ) (c q : ℝ) (i j : Fin 2) :
    pairGenerator n c q i j =
      projectedGenerator (n + 2) ((n + 1) * q) c (transientCategory i)
        (transientCategory j) := by
  fin_cases i <;> fin_cases j
  · simp [pairGenerator, projectedGenerator, transientCategory, totalMigration]
    ring
  all_goals simp [pairGenerator, projectedGenerator, transientCategory, totalMigration,
    destinationRate_succ_mul]

theorem exitRate_pairGenerator (n : ℕ) (c q : ℝ) (i : Fin 2) :
    exitRate (pairGenerator n c q) i =
      projectedGenerator (n + 2) ((n + 1) * q) c (transientCategory i) none := by
  fin_cases i <;>
    simp [exitRate, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pairGenerator,
      projectedGenerator, transientCategory]

end Rhone.Statistics.IslandPairSpatialDesign
