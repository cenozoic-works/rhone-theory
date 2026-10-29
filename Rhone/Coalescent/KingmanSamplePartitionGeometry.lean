/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartition
/-! # Live-lineage and sample-block correspondence -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset IntervalProcess

theorem image_live_sample_fibres_eq_parts (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    (univ.image (fun v : Fin (ω k).1.2.2.1 =>
      univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
        ((ω k).1.2.2.2 v).1))) = (samplePartition N ω k).parts := by
  classical
  rw [samplePartition_parts]
  ext C
  constructor
  · rintro h
    obtain ⟨v, -, rfl⟩ := mem_image.mp h
    obtain ⟨a, ha⟩ := kingman_path_sample_surjective N ω hinit hvalid hstep k v
    exact mem_image.mpr ⟨a, mem_univ a, by simp only [ha]⟩
  · rintro h
    obtain ⟨a, -, rfl⟩ := mem_image.mp h
    obtain ⟨v, hv⟩ := kingman_sample_present N ω hinit hvalid hstep a k
    exact mem_image.mpr ⟨v, mem_univ v, by simp only [hv]⟩

theorem live_sample_fibres_injective (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    Function.Injective (fun v : Fin (ω k).1.2.2.1 =>
      univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
        ((ω k).1.2.2.2 v).1)) := by
  classical
  intro i j he
  dsimp only at he
  obtain ⟨a, ha⟩ := kingman_path_sample_surjective N ω hinit hvalid hstep k i
  have hm : a ∈ univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
      ((ω k).1.2.2.2 i).1) := mem_filter.mpr ⟨mem_univ a, ha⟩
  rw [he] at hm
  have hj := (mem_filter.mp hm).2
  exact (hvalid k).2.2.2 (ha.symm.trans hj)

theorem samplePartition_card_eq_liveCount (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    (samplePartition N ω k).parts.card = (ω k).1.2.2.1 := by
  classical
  rw [← image_live_sample_fibres_eq_parts N ω hinit hvalid hstep k,
    card_image_of_injective _ (live_sample_fibres_injective N ω hinit hvalid hstep k)]
  simp
end Rhone.Coalescent.SmcPrime
