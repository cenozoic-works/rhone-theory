/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Mathlib.Probability.UniformOn
/-! # Uniform finite-support transport under a bijection -/
@[expose] public section
namespace Rhone.Probability
open MeasureTheory ProbabilityTheory

theorem map_uniformOn_of_bijOn {A B : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (s : Set A) (t : Set B) (hs : s.Finite) (f : A → B) (hf : Measurable f)
    (hbij : Set.BijOn f s t) : (uniformOn s).map f = uniformOn t := by
  classical
  have ht : t.Finite := hbij.image_eq ▸ hs.image f
  have hsize : s.encard = t.encard := by
    rw [← hbij.image_eq, hbij.injOn.encard_image]
  apply Measure.ext
  intro U hU
  have hpre : MeasurableSet (f ⁻¹' U) := hf hU
  have himage : f '' (s ∩ f ⁻¹' U) = t ∩ U := by
    ext b
    constructor
    · rintro ⟨a, ⟨ha, hUa⟩, rfl⟩
      exact ⟨hbij.mapsTo ha, hUa⟩
    · rintro ⟨hb, hUb⟩
      obtain ⟨a, ha, rfl⟩ := hbij.surjOn hb
      exact ⟨a, ⟨ha, hUb⟩, rfl⟩
  have hcount : (s ∩ f ⁻¹' U).encard = (t ∩ U).encard := by
    rw [← himage]
    exact (hbij.injOn.mono Set.inter_subset_left).encard_image.symm
  rw [Measure.map_apply hf hU, uniformOn, uniformOn,
    cond_apply hs.measurableSet, cond_apply ht.measurableSet,
    Measure.count_apply hs.measurableSet, Measure.count_apply ht.measurableSet,
    Measure.count_apply (hs.measurableSet.inter hpre),
    Measure.count_apply (ht.measurableSet.inter hU), hsize, hcount]
end Rhone.Probability
