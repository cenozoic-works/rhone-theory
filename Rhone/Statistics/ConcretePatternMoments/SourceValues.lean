/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePatternMoments.Data
public import Rhone.Statistics.ThreeSiteSeparator.SourceLaplace

/-! # Nineteen exact moments from the island CTMC law -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.ConcretePatternMoments
open ThreeSiteSeparator MarkovChain.Identifiability Identifiability

def sourceValues : Fin 19 → ℝ :=
  ![(1 : ℝ) / 1,
    (45603 : ℝ) / 230885,
    (50351 : ℝ) / 592283,
    (105501 : ℝ) / 2229215,
    (20251 : ℝ) / 122915,
    (9537 : ℝ) / 128143,
    (120551 : ℝ) / 2829307,
    (453 : ℝ) / 757,
    (25301 : ℝ) / 179035,
    (70451 : ℝ) / 1064495,
    (406803 : ℝ) / 10499497,
    (91053 : ℝ) / 735965,
    (80501 : ℝ) / 1351051,
    (16739 : ℝ) / 471199,
    (251 : ℝ) / 587,
    (35401 : ℝ) / 321775,
    (271653 : ℝ) / 5013721,
    (40451 : ℝ) / 408395,
    (351 : ℝ) / 1055]

theorem source_values_exact (j : Fin 19) :
    sourceMoment (exponents j).1 (exponents j).2 (1 / 100) = sourceValues j := by
  fin_cases j <;> norm_num [exponents, sourceMoment, sourceValues]

theorem integral_eq_sourceValues (j : Fin 19) :
    (∫ t : ℝ × ℝ, Real.exp (-(((exponents j).1 : ℝ) + (exponents j).2) * t.1 -
      ((exponents j).2 : ℝ) * t.2) ∂IslandThreeTimes.durationLaw 0 1 (1 / 100)) =
      sourceValues j := by
  rw [integral_eq_sourceMoment (by norm_num : (0 : ℝ) < 1 / 100), source_values_exact]

end Rhone.Statistics.ConcretePatternMoments
