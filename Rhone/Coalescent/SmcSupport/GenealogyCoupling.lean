/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.EventCoupling
public import Rhone.Coalescent.FiniteIntervalGenealogyMeas

/-! # The pairwise MRCA observation inherits the trajectory total-variation bound -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace Rhone.Coalescent.IntervalProcess

noncomputable def hullContactGenealogyLaw (N : ℕ) (R : ℝ) :
    Measure (Genealogy N) :=
  ((eventProcess true R).pathLaw (initialState N, (0, .inl ()))).map
    (genealogyObservation N)

instance hullContactGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (hullContactGenealogyLaw N R) := by
  unfold hullContactGenealogyLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (genealogyObservation_measurable N).aemeasurable).mpr inferInstance

end Rhone.Coalescent.IntervalProcess
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound

theorem hullContact_genealogy_tv_le (R : ℝ) (hR : 0 ≤ R) (N : ℕ) (hN : 0 < N) :
    Rhone.Probability.eventTV (fullARGGenealogyLaw N R)
      (hullContactGenealogyLaw N R) ≤ ENNReal.ofReal (doubleBound R (N - 1)) := by
  exact (Rhone.Probability.data_processing
    ((eventProcess false R).pathLaw (initialState N, (0, .inl ())))
    ((eventProcess true R).pathLaw (initialState N, (0, .inl ())))
    (genealogyObservation N) (genealogyObservation_measurable N)).trans
    (event_path_tv_le R hR N hN)

theorem hullContact_genealogy_tv_quadratic (R : ℝ) (hR : 0 ≤ R) (N : ℕ) (hN : 0 < N) :
    Rhone.Probability.eventTV (fullARGGenealogyLaw N R)
      (hullContactGenealogyLaw N R) ≤
      ENNReal.ofReal (min 1 (R ^ 2 * quadraticCoefficient (N - 1))) := by
  exact (hullContact_genealogy_tv_le R hR N hN).trans (ENNReal.ofReal_le_ofReal
    (doubleBound_le_min R hR (N - 1)))

end Rhone.Coalescent.SmcSupport
