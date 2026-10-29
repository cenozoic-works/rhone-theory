/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedOnsetPrefixes

/-! # Recombination alone has a globally nonnegative derivative of the product witness -/

@[expose] public section

noncomputable section
open Matrix
open scoped BigOperators Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
open SimultaneousOnset

set_option maxHeartbeats 800000 in
theorem recombinationMark_witness (k : ℕ) :
    recombinationMark k *ᵥ witnessVec = Pi.single (0, 1) (2 : ℝ) := by
  ext ⟨i,a⟩
  rw [recombinationMark, productGenerator_mulVec]
  fin_cases i <;> fin_cases a <;>
    norm_num [MarkovChain.Identifiability.generator, MarkovChain.Identifiability.pairGenerator,
        MarkovChain.Identifiability.totalMigration, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, MarkovChain.Identifiability.recombinationTable, witnessVec,
          MarkovChain.Identifiability.firstATable, MarkovChain.Identifiability.firstAThenBTable,
      Pi.single_apply]

end Rhone.Statistics.Identifiability.SilentWindow
