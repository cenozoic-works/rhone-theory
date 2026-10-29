/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartitionStep
public import Rhone.Coalescent.KingmanSamplePartitionPrefix
public import Rhone.Coalescent.SmcPrimeKingmanOneStepMarkLaw
/-! # The pair-event kernel and its sample-partition observation -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory ProbabilityTheory IntervalProcess SmcSupport

theorem eventKernel_kingmanTransition_ae (z : AugmentedState) :
    ∀ᵐ y ∂eventKernel false 0 z, KingmanTransition (z, y) := by
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable false 0).comp (measurable_const.prodMk measurable_id)).aemeasurable
    (KingmanTransition_measurable.preimage
      (measurable_const.prodMk measurable_id))).mpr
  exact noiseLaw_interior.mono (fun u hu => sampleStep_kingmanTransition z u hu)

theorem eventKernel_kingmanPair_law (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) :
    (eventKernel false 0 z).map eventPair = uniformOn (kingmanPairSet z.1.2.2.1) := by
  have hmk : Measurable (kingmanMark z) :=
    kingmanMark_measurable.comp (measurable_const.prodMk measurable_id)
  let : IsProbabilityMeasure (expMeasure (Rhone.Coalescent.coalRate z.1.2.2.1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by exact_mod_cast Rhone.Coalescent.coalRate_pos hm)
  change (eventKernel false 0 z).map (Prod.fst ∘ kingmanMark z) = _
  rw [← Measure.map_map measurable_fst hmk, eventKernel_kingmanMark_law z hm,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem samplePartition_update_next_merge_ae (N : ℕ) (ω : EventPath) (k : ℕ)
    (hvalid : Valid (ω k).1)
    (hcarried : ∀ a : Fin N, ∃ v,
      ((ω k).1.2.2.2 v).1 = ancestorLabel N ω leftBoundaryProbe a k)
    (hsurj : ∀ v, ∃ a : Fin N,
      ancestorLabel N ω leftBoundaryProbe a k = ((ω k).1.2.2.2 v).1)
    (hm : 2 ≤ (ω k).1.2.2.1) :
    ∀ᵐ y ∂eventKernel false 0 (ω k),
      samplePartition N (Function.update ω (k + 1) y) (k + 1) =
        mergeBlocks (samplePartition N ω k)
          {univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
            liveLabelAt (ω k).1 (eventPair y).1),
           univ.filter (fun a => ancestorLabel N ω leftBoundaryProbe a k =
            liveLabelAt (ω k).1 (eventPair y).2)} := by
  classical
  filter_upwards [eventKernel_kingmanTransition_ae (ω k)] with y hy
  rw [KingmanTransition, ite_eq_left hm] at hy
  obtain ⟨p, hp, hb, hmark, -, -⟩ := hy
  change y.2.2 = .inr (.inl p) at hmark
  let η := Function.update ω (k + 1) y
  have hηk : η k = ω k := Function.update_of_ne (show k ≠ k + 1 by omega) y ω
  have hηnext : η (k + 1) = y := Function.update_self _ _ _
  have hlabels (a : Fin N) : ancestorLabel N η leftBoundaryProbe a k =
      ancestorLabel N ω leftBoundaryProbe a k := by
    apply ancestorLabel_eq_of_prefix
    intro l hl
    exact Function.update_of_ne (show l ≠ k + 1 by omega) y ω
  have hcarriedη : ∀ a : Fin N, ∃ v,
      ((η k).1.2.2.2 v).1 = ancestorLabel N η leftBoundaryProbe a k := by
    intro a
    rw [hlabels a, hηk]
    exact hcarried a
  have hsurjη : ∀ v, ∃ a : Fin N,
      ancestorLabel N η leftBoundaryProbe a k = ((η k).1.2.2.2 v).1 := by
    rw [hηk]
    intro v
    obtain ⟨a, ha⟩ := hsurj v
    exact ⟨a, (hlabels a).trans ha⟩
  let i : Fin (η k).1.2.2.1 := ⟨p.1, by simpa only [hηk] using lt_trans hp hb⟩
  let j : Fin (η k).1.2.2.1 := ⟨p.2, by simpa only [hηk] using hb⟩
  have hmerge := samplePartition_succ_eq_mergeBlocks_of_fibres N η k
    (by simpa only [hηk] using hvalid)
    hcarriedη hsurjη i j hp
    (by simpa only [hηnext, i, j] using hmark)
  have hevent : eventPair y = p := by
    simp only [eventPair, hmark, Sum.elim_inr, Sum.elim_inl, id_eq]
  have hpartk : samplePartition N η k = samplePartition N ω k :=
    samplePartition_update_next N ω k y k le_rfl
  have hfirst : p.1 < (η k).1.2.2.1 := i.isLt
  have hsecond : p.2 < (η k).1.2.2.1 := j.isLt
  have hiuid : ((η k).1.2.2.2 i).1 = liveLabelAt (η k).1 p.1 := by
    rw [liveLabelAt, dite_eq_left hfirst]
  have hjuid : ((η k).1.2.2.2 j).1 = liveLabelAt (η k).1 p.2 := by
    rw [liveLabelAt, dite_eq_left hsecond]
  rw [hiuid, hjuid, hηk] at hmerge
  change samplePartition N η (k + 1) = _
  simpa only [hpartk, hlabels, hevent, liveLabelAt, dite_eq_left (lt_trans hp hb),
    dite_eq_left hb] using hmerge
end Rhone.Coalescent.SmcPrime
