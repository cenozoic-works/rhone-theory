/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Admissibility

/-! # Event-level projection to the surviving B pair -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

noncomputable def bProjection : Matrix MarkovChain.Identifiability.State (Fin 2) ℝ :=
  fun i j => if MarkovChain.Identifiability.bTogether (MarkovChain.Identifiability.shape i) then
      (if j = 0 then 1 else 0)
    else (if j = 0 then 0 else 1)

theorem bProjection_survival : bProjection *ᵥ MarkovChain.Identifiability.pairSurvival = fun _ =>
    1 := by
  ext i
  simp [bProjection, MarkovChain.Identifiability.pairSurvival, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem bProjection_initial (j : Fin 2) : bProjection 0 j = if j = 0 then 1 else 0 := by
  simp [bProjection, MarkovChain.Identifiability.bTogether, MarkovChain.Identifiability.shape,
      MarkovChain.Identifiability.carriesB]

set_option maxHeartbeats 800000 in
theorem pair_projection_generator (k : Nat) (c q r : ℝ) (i : MarkovChain.Identifiability.State)
    (hi : Admissible k i) (j : Fin 2) :
    (MarkovChain.Identifiability.generator k c q r * bProjection + firstAKernel c) i j =
      (bProjection * MarkovChain.Identifiability.pairGenerator k c q) i j := by
  have hn : ((k + 2 - MarkovChain.Identifiability.occupiedDemes i : Nat) : ℝ) =
      (k : ℝ) + 2 - (MarkovChain.Identifiability.occupiedDemes i : ℝ) := by
    rw [Nat.cast_sub hi]
    push_cast
    ring
  simp only [Matrix.add_apply, Matrix.mul_apply, MarkovChain.Identifiability.generator, hn]
  fin_cases i <;> fin_cases j <;>
    norm_num [bProjection, MarkovChain.Identifiability.pairGenerator, firstAKernel,
        MarkovChain.Identifiability.totalMigration,
      MarkovChain.Identifiability.bTogether, MarkovChain.Identifiability.shape,
          MarkovChain.Identifiability.carriesB, MarkovChain.Identifiability.firstATable,
          MarkovChain.Identifiability.firstAThenBTable,
      MarkovChain.Identifiability.coalescenceTable, MarkovChain.Identifiability.recombinationTable,
          MarkovChain.Identifiability.occupiedTable, MarkovChain.Identifiability.emptyTable,
      MarkovChain.Identifiability.occupiedDemes, Fin.sum_univ_succ] <;> ring

end Rhone.Statistics.Identifiability
