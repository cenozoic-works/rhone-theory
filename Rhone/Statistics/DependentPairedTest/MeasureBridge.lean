/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProbability
public import Rhone.Statistics.Identifiability.FinitePanelConcentration

/-! # Bridge from explicit finite masses to iid measures -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget Identifiability.FinitePanelSampling
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

def lawMeasure (P : Law X) : Measure X := ∑ x, ENNReal.ofReal (P.mass x) • Measure.dirac x

theorem law_measure_singleton (P : Law X) (x : X) :
    lawMeasure P {x} = ENNReal.ofReal (P.mass x) := by
  classical
  simp [lawMeasure, Measure.finsetSum_apply, Measure.smul_apply, Pi.single_apply]

instance lawMeasure_probability (P : Law X) : IsProbabilityMeasure (lawMeasure P) where
  measure_univ := by
    simp only [lawMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => P.nonneg x), P.total]
    norm_num

theorem law_measure_real_singleton (P : Law X) (x : X) :
    (lawMeasure P).real {x} = P.mass x := by
  rw [Measure.real, law_measure_singleton, ENNReal.toReal_ofReal (P.nonneg x)]

theorem law_measure_integral (P : Law X) (f : X → ℝ) :
    (∫ x, f x ∂lawMeasure P) = rejection P f := by
  rw [integral_fintype (by fun_prop)]
  simp only [law_measure_real_singleton, smul_eq_mul, rejection]

theorem iid_measure_real_singleton (P : Law X) (N : ℕ) (x : Fin N → X) :
    (iidLaw (lawMeasure P) N).real {x} = (iid P N).mass x := by
  simp only [iidLaw, Measure.real, Measure.pi_singleton, law_measure_singleton,
    ENNReal.toReal_prod, ENNReal.toReal_ofReal (P.nonneg _), iid]

theorem iid_measure_probability (P : Law X) (N : ℕ) (A : (Fin N → X) → Prop) :
    (iidLaw (lawMeasure P) N).real {x | A x} = probability (iid P N) A := by
  classical
  have h := sum_measureReal_singleton (μ := iidLaw (lawMeasure P) N) (Finset.univ.filter A)
  simpa [probability, Finset.sum_filter, iid_measure_real_singleton] using h.symm

end Rhone.Statistics.DependentPairedTest
