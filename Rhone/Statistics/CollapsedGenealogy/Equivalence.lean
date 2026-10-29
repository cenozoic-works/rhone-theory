/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Encoding

/-! # Exact all-block identification of the scaled collapsed joint law -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites ThreeSiteSeparator

theorem all_blocks_iff_collapsed_joint_eq {K : ℕ} (hK : 2 ≤ K)
    {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) (μ ν : Measure Joint)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν) :
    (∀ L : ℕ, jointSequenceLaw (uniformBlockRoots K L (by omega)) k μ =
      jointSequenceLaw (uniformBlockRoots K L (by omega)) l ν) ↔ object k μ = object l ν := by
  constructor
  · intro he
    have hc : Measure.map (encode k) μ = Measure.map (encode l) ν := by
      apply compact_word_moment_unique 3
      intro L w
      rw [encoded_word_moment hK hk μ hμ L w, encoded_word_moment hK hl ν hν L w]
      apply Finset.sum_congr rfl
      intro x _
      rw [equal_laws_equal_masses _ hk hl μ ν hμ hν (he L) x]
    rw [← decoded_encoding_map hk μ hμ, ← decoded_encoding_map hl ν hν, hc]
  · intro he L
    exact collapsed_joint_eq_all_blocks k l μ ν he K L (by omega)

end Rhone.Statistics.CollapsedGenealogy
