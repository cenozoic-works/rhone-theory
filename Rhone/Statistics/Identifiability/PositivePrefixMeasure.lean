/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-! # Positive finite measures are identified by their finite positive prefix CDF -/

@[expose] public section

open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

lemma real_Iic_eq_Ioc_of_positive (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 < x) (t : ℝ) :
    μ.real (Iic t) = μ.real (Ioc 0 t) := by
  apply measureReal_congr
  filter_upwards [hμ] with x hx
  apply propext
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

lemma positive_measure_eq_of_prefix (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 < x) (hν : ∀ᵐ x ∂ν, 0 < x)
    (he : ∀ t, 0 ≤ t → μ.real (Ioc 0 t) = ν.real (Ioc 0 t)) : μ = ν := by
  apply Measure.ext_of_Iic
  intro t
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change μ.real (Iic t) = ν.real (Iic t)
  rw [real_Iic_eq_Ioc_of_positive μ hμ t, real_Iic_eq_Ioc_of_positive ν hν t]
  by_cases ht : 0 ≤ t
  · exact he t ht
  · rw [Ioc_eq_empty_of_le (le_of_not_ge ht)]
    simp

end Rhone.Statistics.Identifiability
