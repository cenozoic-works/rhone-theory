/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcSupport.ARGFiniteHistory
public import Rhone.Coalescent.FiniteIntervalGenealogy
/-! # Adapted events and the next-event kernel -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory ProbabilityTheory Preorder IntervalProcess SmcSupport

theorem eventProcess_adapted_next (R : ℝ) (z : AugmentedState) (n : ℕ)
    {E : Set EventPath}
    (hE : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => AugmentedState) (n + 1)] E) :
    (eventProcess false R).pathLaw z E =
      ∫⁻ ω, eventKernel false R (ω n)
        {y | Function.update ω (n + 1) y ∈ E} ∂(eventProcess false R).pathLaw z := by
  classical
  rw [Filtration.piLE_eq_comap_frestrictLe,
    MeasurableSpace.measurableSet_comap] at hE
  obtain ⟨T, hT, hTE⟩ := hE
  let F : EventPath → ARGPrefix n × AugmentedState :=
    fun ω => ((fun i : Iic n => ω i.val), ω (n + 1))
  let join : ARGPrefix n × AugmentedState → ARGPrefix (n + 1) := fun p i =>
    if hi : i.val ≤ n then p.1 ⟨i.val, mem_Iic.mpr hi⟩ else p.2
  have hjoin : Measurable join := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i.val ≤ n
    · simpa only [join, dite_eq_left hi, Function.comp_def] using
        (measurable_pi_apply (⟨i.val, mem_Iic.mpr hi⟩ : Iic n)).comp measurable_fst
    · simpa only [join, dite_eq_right hi] using
        (measurable_snd : Measurable (Prod.snd : ARGPrefix n × AugmentedState → _))
  let B : Set (ARGPrefix n × AugmentedState) := join ⁻¹' T
  have hB : MeasurableSet B := hT.preimage hjoin
  have hF : Measurable F :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply _)
  have hjoinF (ω : EventPath) : join (F ω) = frestrictLe (n + 1) ω := by
    funext i
    by_cases hi : i.val ≤ n
    · simp only [join, F, dite_eq_left hi, frestrictLe, Finset.restrict]
    · have hin : i.val = n + 1 := by have := mem_Iic.mp i.property; omega
      simp only [join, F, dite_eq_right hi, frestrictLe, Finset.restrict, hin]
  have hset : F ⁻¹' B = E := by
    rw [← hTE]
    ext ω
    simp only [B, Set.mem_preimage, hjoinF]
  have hsec (ω : EventPath) : Prod.mk (F ω).1 ⁻¹' B =
      {y | Function.update ω (n + 1) y ∈ E} := by
    ext y
    rw [← hTE]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, B]
    have heq : join ((F ω).1, y) = frestrictLe (n + 1) (Function.update ω (n + 1) y) := by
      funext i
      by_cases hi : i.val ≤ n
      · simp only [join, F, dite_eq_left hi, frestrictLe, Finset.restrict,
          Function.update_of_ne (show i.val ≠ n + 1 by omega)]
      · have hin : i.val = n + 1 := by have := mem_Iic.mp i.property; omega
        simp only [join, dite_eq_right hi, frestrictLe, Finset.restrict, hin,
          Function.update_self]
    rw [heq]
  have hmeas : Measurable fun h : ARGPrefix n =>
      (eventProcess false R).stepSeq n h (Prod.mk h ⁻¹' B) :=
    Kernel.measurable_kernel_prodMk_left hB
  rw [← hset, ← Measure.map_apply hF hB, argPrefixLaw_next, Measure.compProd_apply hB,
    argPrefixLaw, lintegral_map hmeas (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)]
  apply lintegral_congr
  intro ω
  rw [Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply, hsec]
  simp only [eventProcess, hset]
end Rhone.Coalescent.SmcPrime
