/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeKingmanClades
public import Rhone.Coalescent.KingmanPartition
/-! # Sample partitions of the Kingman event process -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory IntervalProcess

noncomputable def samplePartition (N : ℕ) (ω : EventPath) (k : ℕ) :
    Finpartition (univ : Finset (Fin N)) where
  parts := kingmanSampleClades N ω k
  supIndep := by
    classical
    apply supIndep_iff_pairwiseDisjoint.mpr
    intro A hA B hB hne
    exact (kingmanSampleClades_partition N ω k).2.2 A hA B hB hne
  sup_parts := by
    classical
    apply eq_univ_of_forall
    intro i
    exact mem_sup.mpr ((kingmanSampleClades_partition N ω k).2.1 i)
  bot_notMem := by
    intro h
    exact (kingmanSampleClades_partition N ω k).1 ∅ h rfl

theorem samplePartition_parts (N : ℕ) (ω : EventPath) (k : ℕ) :
    (samplePartition N ω k).parts = kingmanSampleClades N ω k := rfl

private theorem kingmanSampleClades_measurable (N k : ℕ) :
    Measurable (fun ω : EventPath => kingmanSampleClades N ω k) := by
  classical
  let code : EventPath → (Fin N × Fin N → Bool) := fun ω p =>
    decide (ancestorLabel N ω leftBoundaryProbe p.1 k =
      ancestorLabel N ω leftBoundaryProbe p.2 k)
  let decode : (Fin N × Fin N → Bool) → Finset (Finset (Fin N)) := fun c =>
    univ.image (fun i => univ.filter (fun j => c (j, i) = true))
  have hc : Measurable code := by
    apply measurable_pi_iff.mpr
    intro p
    apply measurable_to_bool
    simpa only [code, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_eq_fun (ancestorLabel_measurable N leftBoundaryProbe p.1 k)
        (ancestorLabel_measurable N leftBoundaryProbe p.2 k)
  have hd : Measurable decode := measurable_of_countable decode
  simpa only [code, decode, Function.comp_def, decide_eq_true_eq, kingmanSampleClades] using
    hd.comp hc

theorem samplePartition_measurable (N k : ℕ) :
    Measurable (fun ω : EventPath => samplePartition N ω k) := by
  apply measurable_to_countable'
  intro π
  convert measurableSet_eq_fun (kingmanSampleClades_measurable N k)
    (measurable_const (a := π.parts)) using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact ⟨congrArg Finpartition.parts, fun h => Finpartition.ext h⟩
end Rhone.Coalescent.SmcPrime
