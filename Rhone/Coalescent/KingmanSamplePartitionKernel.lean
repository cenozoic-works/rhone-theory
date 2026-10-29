/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePairLaw
public import Rhone.Coalescent.KingmanSamplePairBijection
public import Rhone.Coalescent.KingmanPartitionJumpKernel
public import Rhone.Probability.UniformOnBijection
/-! # Conditional sample-partition law under the event kernel -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory ProbabilityTheory IntervalProcess

theorem samplePartition_eventKernel (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    (eventKernel false 0 (ω k)).map
      (fun y => samplePartition N (Function.update ω (k + 1) y) (k + 1)) =
        (partitionChain (Fin N)).jumpChain.kernel (samplePartition N ω k) := by
  classical
  have hcard := samplePartition_card_eq_liveCount N ω hinit hvalid hstep k
  by_cases hm : 2 ≤ (ω k).1.2.2.1
  · let φ : ℕ × ℕ → Finpartition (univ : Finset (Fin N)) := fun p =>
      mergeBlocks (samplePartition N ω k)
        {univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          liveLabelAt (ω k).1 p.1),
         univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
          liveLabelAt (ω k).1 p.2)}
    have hφ : Measurable φ := measurable_of_countable φ
    have hobs := samplePartition_update_next_merge_ae N ω k (hvalid k)
      (fun a => kingman_sample_present N ω hinit hvalid hstep a k)
      (kingman_path_sample_surjective N ω hinit hvalid hstep k) hm
    have hs : (kingmanPairSet (ω k).1.2.2.1).Finite :=
      (((Set.finite_Iio (ω k).1.2.2.1).prod (Set.finite_Iio (ω k).1.2.2.1)).subset
        fun _ hp => ⟨lt_trans hp.1 hp.2, hp.2⟩)
    calc
      _ = (eventKernel false 0 (ω k)).map (φ ∘ eventPair) := Measure.map_congr hobs
      _ = ((eventKernel false 0 (ω k)).map eventPair).map φ :=
        (Measure.map_map hφ eventPair_measurable).symm
      _ = (uniformOn (kingmanPairSet (ω k).1.2.2.1)).map φ := by
        rw [eventKernel_kingmanPair_law (ω k) hm]
      _ = uniformOn (Rhone.Coalescent.merges (samplePartition N ω k) : Set _) :=
        Rhone.Probability.map_uniformOn_of_bijOn _ _ hs φ hφ
          (bijOn_kingmanPairSet_sampleMerges N ω hinit hvalid hstep k)
      _ = (partitionChain (Fin N)).jumpChain.kernel (samplePartition N ω k) :=
        (partition_jump_kernel_uniform (by simpa only [hcard] using hm)).symm
  · have hk : (samplePartition N ω k).parts.card ≤ 1 := by rw [hcard]; omega
    rw [partition_jump_kernel_absorbing hk]
    have hobs : (fun y => samplePartition N (Function.update ω (k + 1) y) (k + 1)) =ᵐ[
        eventKernel false 0 (ω k)] (fun _ => samplePartition N ω k) := by
      filter_upwards [eventKernel_kingmanTransition_ae (ω k)] with y hy
      rw [KingmanTransition, ite_eq_right hm] at hy
      have hmark : (Function.update ω (k + 1) y (k + 1)).2.2 = .inl () := by
        simpa only [Function.update_self] using hy.2
      exact (samplePartition_succ_idle N (Function.update ω (k + 1) y) k hmark).trans
        (samplePartition_update_next N ω k y k le_rfl)
    rw [Measure.map_congr hobs, Measure.map_const, measure_univ, one_smul]
end Rhone.Coalescent.SmcPrime
