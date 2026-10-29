/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Finite product-measure uniqueness from open tail rectangles -/

@[expose] public section

noncomputable section
open Set MeasureTheory MeasurableSpace
namespace Rhone.Statistics.Identifiability.FiniteUnequalSurvival

def realTailSpanning (μ : Measure ℝ) [IsFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn (range (Ioi : ℝ → Set ℝ)) where
  set n := Ioi (-(n : ℝ))
  set_mem n := ⟨-(n : ℝ), rfl⟩
  finite n := measure_lt_top μ _
  spanning := by
    ext x
    simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    exact ⟨n, by linarith⟩

theorem eq_prod_of_tail_rectangles (α β : Measure ℝ)
    [IsFiniteMeasure α] [IsFiniteMeasure β] (μ : Measure (ℝ × ℝ))
    (h : ∀ s t : ℝ, μ (Ioi s ×ˢ Ioi t) = α (Ioi s) * β (Ioi t)) :
    μ = α.prod β := by
  have hgen : generateFrom (range (Ioi : ℝ → Set ℝ)) =
      (inferInstance : MeasurableSpace ℝ) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)).symm
  symm
  apply Measure.prod_eq_generateFrom hgen hgen isPiSystem_Ioi isPiSystem_Ioi
    (realTailSpanning α) (realTailSpanning β)
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  exact h s t

end Rhone.Statistics.Identifiability.FiniteUnequalSurvival
