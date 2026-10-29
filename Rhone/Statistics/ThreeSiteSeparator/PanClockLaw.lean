/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.PanScaledPolynomial
public import Rhone.Statistics.ThreeSiteSeparator.CDFContinuity

/-! # Unit-interval and atomlessness properties of a positively scaled pan pair clock -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open AtomicSmoothing Algebra.Identifiability MarkovChain.Identifiability Identifiability

def panClockLaw (a : ℝ) (r : ℝ → ℝ) : Measure ℝ :=
  (panPairLaw r).map (scaledClock a)

lemma panClockLaw_probability (a : ℝ) (r : ℝ → ℝ)
    (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) : IsProbabilityMeasure (panClockLaw a r) := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  unfold panClockLaw
  infer_instance

lemma panClockLaw_unit_support (a : ℝ) (r : ℝ → ℝ) :
    ∀ᵐ z ∂panClockLaw a r, z ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff (scaledClock_continuous a).measurable.aemeasurable (by measurability)).mpr
  exact Filter.Eventually.of_forall fun t =>
    ⟨(unitClock_positive (a*t)).le, unitClock_le_one (a*t)⟩

lemma panClockLaw_exp {a : ℝ} (ha : 0 ≤ a) (r : ℝ → ℝ) :
    panClockLaw a r = (panPairLaw r).map (fun t => Real.exp (-a*t)) := by
  apply Measure.map_congr
  filter_upwards [PanThreeSample.pairLaw_positive_support r] with t ht
  unfold scaledClock
  rw [unitClock_eq (mul_nonneg ha ht.le)]
  congr 1
  ring

lemma panClockLaw_atomless {a : ℝ} (ha : 0 < a) (r : ℝ → ℝ) :
    NullSingletonClass (panClockLaw a r) := by
  rw [panClockLaw_exp ha.le]
  constructor
  intro x
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro s hs t ht
  have he : Real.exp (-a*s) = Real.exp (-a*t) := hs.trans ht.symm
  have he' := Real.exp_injective he
  nlinarith

lemma panClockLaw_CDF_continuous {a : ℝ} (ha : 0 < a) (r : ℝ → ℝ)
    (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) :
    Continuous (fun x => (panClockLaw a r).real (Iic x)) := by
  let : IsProbabilityMeasure (panClockLaw a r) := panClockLaw_probability a r hr hn ht
  let : NullSingletonClass (panClockLaw a r) := panClockLaw_atomless ha r
  exact realCDF_continuous _

end Rhone.Statistics.ThreeSiteSeparator
