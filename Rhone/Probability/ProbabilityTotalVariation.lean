/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Event-supremum total variation and coupling

Source: levin_peres2017, secs. 4.1–4.2, Prop. 4.7, pp. 47–51. -/

@[expose] public section

namespace Rhone.Probability
open MeasureTheory
open scoped ENNReal symmDiff
variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β]

/-- Source: levin_peres2017, sec. 4.1. -/
noncomputable def eventTV (ν κ : Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_ : MeasurableSet s), ENNReal.ofReal |ν.real s - κ.real s|

/-- Source: levin_peres2017, sec. 4.1, definition 4.1. -/
theorem eventTV_le_iff (ν κ : Measure α) (ε : ℝ≥0∞) :
    eventTV ν κ ≤ ε ↔
      ∀ s, MeasurableSet s → ENNReal.ofReal |ν.real s - κ.real s| ≤ ε := by
  simp only [eventTV, iSup_le_iff]

/-- Source: levin_peres2017, sec. 4.1. -/
theorem eventTV_le_one (ν κ : Measure α) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ] : eventTV ν κ ≤ 1 := by
  apply (eventTV_le_iff _ _ _).2
  intro s _
  apply ENNReal.ofReal_le_one.mpr
  apply abs_le.mpr
  constructor
  · have h : κ.real s - ν.real s ≤ 1 :=
      (sub_le_self _ ENNReal.toReal_nonneg).trans measureReal_le_one
    simpa only [neg_sub] using neg_le_neg h
  · exact (sub_le_self _ ENNReal.toReal_nonneg).trans measureReal_le_one

/-- Source: levin_peres2017, Prop. 4.7, inequality 4.11. -/
theorem event_difference_le_disagreement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → α) (hX : Measurable X) (hY : Measurable Y)
    (s : Set α) (hs : MeasurableSet s) :
    ENNReal.ofReal |(μ.map X).real s - (μ.map Y).real s| ≤
      μ {ω | X ω ≠ Y ω} := by
  have hsub : (X ⁻¹' s) ∆ (Y ⁻¹' s) ⊆ {ω | X ω ≠ Y ω} := by
    intro ω hω heq
    simp only [Set.mem_symmDiff, Set.mem_preimage] at hω
    rcases hω with hω | hω
    · exact hω.2 (heq ▸ hω.1)
    · exact hω.2 (heq.symm ▸ hω.1)
  have h := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := μ) (hX hs).nullMeasurableSet (hY hs).nullMeasurableSet
  have hreal := h.trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))
  simpa only [Measure.real, Measure.map_apply hX hs, Measure.map_apply hY hs,
    ENNReal.ofReal_toReal (measure_ne_top μ _)] using ENNReal.ofReal_le_ofReal hreal

/-- Source: levin_peres2017, Prop. 4.7, inequality 4.12. -/
theorem coupling_inequality (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → α) (hX : Measurable X) (hY : Measurable Y) :
    eventTV (μ.map X) (μ.map Y) ≤ μ {ω | X ω ≠ Y ω} := by
  exact (eventTV_le_iff _ _ _).2
    (fun s hs => event_difference_le_disagreement μ X Y hX hY s hs)

/-- Source: levin_peres2017, Prop. 4.7, inequality 4.12. -/
theorem coupling_inequality_of_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → α) (hX : Measurable X) (hY : Measurable Y)
    (ε : ℝ≥0∞) (hε : μ {ω | X ω ≠ Y ω} ≤ ε) :
    eventTV (μ.map X) (μ.map Y) ≤ ε :=
  (coupling_inequality μ X Y hX hY).trans hε

/-- Source: levin_peres2017, sec. 4.1, definition 4.1. -/
theorem data_processing (ν κ : Measure α) (f : α → β) (hf : Measurable f) :
    eventTV (ν.map f) (κ.map f) ≤ eventTV ν κ := by
  apply (eventTV_le_iff _ _ _).2
  intro s hs
  simp only [Measure.real, Measure.map_apply hf hs]
  exact le_iSup_of_le (f ⁻¹' s) (le_iSup_of_le (hf hs) le_rfl)

/-- Source: levin_peres2017, secs. 4.1–4.2. -/
theorem eventTV_le_sub_common_mass
    (ν κ ξ : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (hξν : ξ ≤ ν) (hξκ : ξ ≤ κ) :
    eventTV ν κ ≤ ENNReal.ofReal (1 - ξ.real Set.univ) := by
  let : IsFiniteMeasure ξ := isFiniteMeasure_of_le ν hξν
  apply (eventTV_le_iff _ _ _).2
  intro s hs
  have hνs : ξ.real s ≤ ν.real s :=
    ENNReal.toReal_mono (measure_ne_top ν s) (hξν s)
  have hκs : ξ.real s ≤ κ.real s :=
    ENNReal.toReal_mono (measure_ne_top κ s) (hξκ s)
  have hνc : ξ.real sᶜ ≤ ν.real sᶜ :=
    ENNReal.toReal_mono (measure_ne_top ν sᶜ) (hξν sᶜ)
  have hκc : ξ.real sᶜ ≤ κ.real sᶜ :=
    ENNReal.toReal_mono (measure_ne_top κ sᶜ) (hξκ sᶜ)
  have hν := measureReal_add_measureReal_compl (μ := ν) hs
  have hκ := measureReal_add_measureReal_compl (μ := κ) hs
  have hξ := measureReal_add_measureReal_compl (μ := ξ) hs
  have hνu : ν.real Set.univ = 1 := by simp
  have hκu : κ.real Set.univ = 1 := by simp
  apply ENNReal.ofReal_le_ofReal
  apply abs_le.mpr
  constructor <;> linarith

end Rhone.Probability
