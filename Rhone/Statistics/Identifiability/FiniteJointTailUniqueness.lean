/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteUnequalProductTailUniqueness

/-! # Two finite real-pair measures are identified by all open tail rectangles -/

@[expose] public section

noncomputable section
open Set MeasureTheory MeasurableSpace
namespace Rhone.Statistics.Identifiability.ThreeSampleCDF

def jointTailSpanning (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn
      (Set.image2 Set.prod (range (Ioi : ℝ → Set ℝ)) (range (Ioi : ℝ → Set ℝ))) where
  set n := Ioi (-(n : ℝ)) ×ˢ Ioi (-(n : ℝ))
  set_mem n := ⟨_, ⟨-(n : ℝ), rfl⟩, _, ⟨-(n : ℝ), rfl⟩, rfl⟩
  finite n := measure_lt_top μ _
  spanning := by
    ext p
    simp only [mem_iUnion, mem_prod, mem_Ioi, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (max (-p.1) (-p.2))
    exact ⟨n, by linarith [le_max_left (-p.1) (-p.2)],
      by linarith [le_max_right (-p.1) (-p.2)]⟩

lemma eq_of_tail_rectangles (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (he : ∀ s t : ℝ, μ (Ioi s ×ˢ Ioi t) = ν (Ioi s ×ˢ Ioi t)) : μ = ν := by
  have hg : generateFrom (range (Ioi : ℝ → Set ℝ)) =
      (inferInstance : MeasurableSpace ℝ) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)).symm
  let spanning := FiniteUnequalSurvival.realTailSpanning (Measure.dirac (0 : ℝ))
  have hspan := spanning.isCountablySpanning
  apply (jointTailSpanning μ).ext
    (generateFrom_eq_prod hg hg hspan hspan).symm (isPiSystem_Ioi.prod isPiSystem_Ioi)
  rintro _ ⟨s, ⟨a, rfl⟩, t, ⟨b, rfl⟩, rfl⟩
  exact he a b

end Rhone.Statistics.Identifiability.ThreeSampleCDF
