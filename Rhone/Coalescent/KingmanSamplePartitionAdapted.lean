/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartition
public import Rhone.MarkovChain.Process
/-! # Adaptation and initial state of the sample partition -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory IntervalProcess

theorem ancestorLabel_measurable_piLE (N : ℕ) (q : GenomicProbe) (i : Fin N)
    (k n : ℕ) (hkn : k ≤ n) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      (fun ω : EventPath => ancestorLabel N ω q i k) := by
  induction k generalizing n with
  | zero => exact measurable_const
  | succ k ih =>
    have heval (l : ℕ) (hl : l ≤ n) :
        Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
          (fun ω : EventPath => ω l) :=
      (Rhone.MarkovChain.DiscreteProcess.measurable_eval_piLE l).mono
        ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).mono hl) le_rfl
    exact (ancestorStep_measurable q).comp
      ((heval k (by omega)).fst.prodMk
        ((heval (k + 1) hkn).snd.snd.prodMk (ih n (by omega))))

theorem samplePartition_measurable_piLE (N k n : ℕ) (hkn : k ≤ n) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      (fun ω : EventPath => samplePartition N ω k) := by
  classical
  let : MeasurableSpace EventPath :=
    Filtration.piLE (X := fun _ : ℕ => AugmentedState) n
  let code : EventPath → (Fin N × Fin N → Bool) := fun ω p =>
    decide (ancestorLabel N ω leftBoundaryProbe p.1 k =
      ancestorLabel N ω leftBoundaryProbe p.2 k)
  let decode : (Fin N × Fin N → Bool) → Finset (Finset (Fin N)) := fun c =>
    univ.image (fun i => univ.filter (fun j => c (j, i) = true))
  have hc : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n] code := by
    apply measurable_pi_iff.mpr
    intro p
    apply measurable_to_bool
    simpa only [code, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_eq_fun (ancestorLabel_measurable_piLE N leftBoundaryProbe p.1 k n hkn)
        (ancestorLabel_measurable_piLE N leftBoundaryProbe p.2 k n hkn)
  have hd : Measurable decode := measurable_of_countable decode
  have hclades : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      (fun ω : EventPath => kingmanSampleClades N ω k) := by
    simpa only [code, decode, Function.comp_def, decide_eq_true_eq, kingmanSampleClades] using
      hd.comp hc
  apply measurable_to_countable'
  intro π
  convert measurableSet_eq_fun hclades (measurable_const (a := π.parts)) using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact ⟨congrArg Finpartition.parts, fun h => Finpartition.ext h⟩

theorem samplePartition_cylinder_adapted (N n : ℕ)
    (z : ℕ → Finpartition (univ : Finset (Fin N))) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      {ω : EventPath | ∀ i ≤ n, samplePartition N ω i = z i} := by
  have he : {ω : EventPath | ∀ i ≤ n, samplePartition N ω i = z i} =
      ⋂ i, ⋂ (hi : i ≤ n), {ω | samplePartition N ω i = z i} := by ext ω; simp
  rw [he]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
    measurableSet_eq_fun (samplePartition_measurable_piLE N i n hi) measurable_const

theorem samplePartition_zero (N : ℕ) (ω : EventPath) :
    samplePartition N ω 0 = (⊥ : Finpartition (univ : Finset (Fin N))) := by
  classical
  apply Finpartition.ext
  rw [samplePartition_parts, Finpartition.parts_bot, map_eq_image]
  have hf (i : Fin N) : univ.filter (fun j : Fin N => j.val = i.val) = {i} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
  change univ.image (fun i : Fin N => univ.filter (fun j : Fin N => j.val = i.val)) = _
  exact congrArg (fun f : Fin N → Finset (Fin N) => univ.image f) (funext hf)
end Rhone.Coalescent.SmcPrime
