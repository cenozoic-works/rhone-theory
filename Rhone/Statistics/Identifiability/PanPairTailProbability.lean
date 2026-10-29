/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingCountLaw

/-! # Pair-tail probabilities for proper locally integrable pan histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.PanThreeSample

lemma pairLaw_probability (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    IsProbabilityMeasure (panPairLaw rate) := by
  constructor
  rw [panPairLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  simpa [conditionalPairDensity, integratedClock] using
    conditional_lintegral_one rate hr hn htail (s := 0) le_rfl

lemma pairLaw_positive_support (rate : ℝ → ℝ) : ∀ᵐ t ∂panPairLaw rate, 0 < t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

lemma pairLaw_real_Ioi (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    (panPairLaw rate).real (Ioi t) = Real.exp (-integratedClock rate t) := by
  let : IsProbabilityMeasure (panPairLaw rate) := pairLaw_probability rate hr hn htail
  have hcover : Ioc (0 : ℝ) t ∪ Ioi t = Ioi 0 := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact ht.trans_lt hx
    · intro hx
      by_cases hxt : x ≤ t
      · exact Or.inl ⟨hx, hxt⟩
      · exact Or.inr (lt_of_not_ge hxt)
  have hdis : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  have hpos : (panPairLaw rate).real (Ioi 0) = 1 := by
    calc
      _ = (panPairLaw rate).real univ := measureReal_congr
        ((pairLaw_positive_support rate).mono fun x hx =>
          propext ⟨fun _ => mem_univ x, fun _ => hx⟩)
      _ = 1 := by simp
  have he := measureReal_union (μ := panPairLaw rate) hdis measurableSet_Ioi
  rw [hcover, hpos, panPairLaw_real_Ioc rate hr hn ht] at he
  linarith

end Rhone.Statistics.Identifiability.PanThreeSample
