/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.Score
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-! # Score differences of the three-site separator -/

@[expose] public section

namespace Rhone.Statistics.ThreeSiteRobustness

noncomputable def scoreVector (v : Fin 5 → ℝ) : ℝ :=
  ThreeSiteSeparator.score (v 0) (v 1) (v 2) (v 3) (v 4)

noncomputable def coefficient (v w : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![-14220 - 52290*(v 0+w 0-2/3) - 48090*(v 2-1/7),
    41160 + 77175*(v 1+w 1-2/5), -32060 - 48090*(w 0-1/3), 99540, -102900]

theorem score_difference (v w : Fin 5 → ℝ) :
    scoreVector v - scoreVector w = ∑ i, (v i-w i)*coefficient v w i := by
  simp [scoreVector, ThreeSiteSeparator.score, ThreeSiteSeparator.linearScore,
    coefficient, Fin.sum_univ_succ]
  ring

end Rhone.Statistics.ThreeSiteRobustness
