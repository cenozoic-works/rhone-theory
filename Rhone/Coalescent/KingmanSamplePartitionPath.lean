/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanSamplePartitionKernel
public import Rhone.Coalescent.KingmanSamplePartitionAdapted
public import Rhone.Coalescent.KingmanSampleAdapted
public import Rhone.MarkovChain.LumpingTrajectory
/-! # The zero-recombination sample-partition path law -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

theorem samplePartition_cylinder_mass (N n : ℕ)
    (z : ℕ → Finpartition (univ : Finset (Fin N))) :
    ((eventProcess false 0).pathLaw (initialState N, (0, .inl ())))
      {ω | ∀ i ≤ n, samplePartition N ω i = z i} =
      (if (⊥ : Finpartition (univ : Finset (Fin N))) = z 0 then 1 else 0) *
        ∏ i ∈ range n,
          ENNReal.ofReal ((partitionChain (Fin N)).jumpChain.P (z i) (z (i + 1))) := by
  classical
  let μ := (eventProcess false 0).pathLaw (initialState N, (0, .inl ()))
  induction n with
  | zero =>
    by_cases hz : (⊥ : Finpartition (univ : Finset (Fin N))) = z 0
    · simp [samplePartition_zero, hz]
    · simp [samplePartition_zero, hz]
  | succ n ih =>
    let A : Set EventPath := {ω | ∀ i ≤ n, samplePartition N ω i = z i}
    let E : Set EventPath := {ω | ∀ i ≤ n + 1, samplePartition N ω i = z i}
    have hA : MeasurableSet A := (Filtration.piLE.le n) A
      (samplePartition_cylinder_adapted N n z)
    have hval : ∀ᵐ ω ∂μ, eventKernel false 0 (ω n)
        {y | Function.update ω (n + 1) y ∈ E} =
        A.indicator (fun _ => ENNReal.ofReal
          ((partitionChain (Fin N)).jumpChain.P (z n) (z (n + 1)))) ω := by
      filter_upwards [eventProcess_chronologicalAncestryPath N false 0,
        eventProcess_kingmanTransition (initialState N, (0, .inl ()))] with ω hc hs
      by_cases hω : ω ∈ A
      · have hsec : {y | Function.update ω (n + 1) y ∈ E} =
            (fun y => samplePartition N (Function.update ω (n + 1) y) (n + 1)) ⁻¹'
              {z (n + 1)} := by
          ext y
          simp only [Set.mem_ofPred_eq, E, Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · intro h
            exact h (n + 1) le_rfl
          · intro h i hi
            rcases Nat.le_or_eq_of_le_succ hi with hin | hin
            · rw [samplePartition_update_next N ω n y i hin]
              exact hω i hin
            · simpa only [hin] using h
        rw [hsec, Set.indicator_of_mem hω,
          ← Measure.map_apply (samplePartition_update_measurable N ω n)
            (measurableSet_singleton _),
          samplePartition_eventKernel N ω (congrArg Prod.fst hc.1) hc.valid hs n,
          Rhone.MarkovChain.FinChain.kernel_apply_singleton, hω n le_rfl]
      · have hsec : {y | Function.update ω (n + 1) y ∈ E} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          apply hω
          intro i hi
          have he := hy i (Nat.le_succ_of_le hi)
          rwa [samplePartition_update_next N ω n y i hi] at he
        rw [hsec, measure_empty, Set.indicator_of_notMem hω]
    change μ E = _
    rw [eventProcess_adapted_next 0 _ n (samplePartition_cylinder_adapted N (n + 1) z),
      lintegral_congr_ae hval, lintegral_indicator_const hA, prod_range_succ]
    rw [show μ A = _ from ih]
    ring

theorem map_samplePartition_eventProcess_pathLaw (N : ℕ) :
    ((eventProcess false 0).pathLaw (initialState N, (0, .inl ()))).map
      (fun ω => fun k => samplePartition N ω k) =
        (partitionChain (Fin N)).jumpChain.pathLaw
          (⊥ : Finpartition (univ : Finset (Fin N))) := by
  have hmap : Measurable (fun ω : EventPath => fun k => samplePartition N ω k) :=
    measurable_pi_iff.mpr fun k => samplePartition_measurable N k
  refine Rhone.MarkovChain.measure_ext_of_cylinder fun n z => ?_
  have hB : MeasurableSet {ω : ℕ → Finpartition (univ : Finset (Fin N)) |
      ∀ i ≤ n, ω i = z i} := by
    have he : {ω : ℕ → Finpartition (univ : Finset (Fin N)) | ∀ i ≤ n, ω i = z i} =
        ⋂ i, ⋂ (_ : i ≤ n), (fun ω => ω i) ⁻¹' {z i} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton _).preimage (measurable_pi_apply i)
  rw [Measure.map_apply hmap hB]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((eventProcess false 0).pathLaw (initialState N, (0, .inl ()))).real
    {ω | ∀ i ≤ n, samplePartition N ω i = z i} =
    ((partitionChain (Fin N)).jumpChain.pathLaw
      (⊥ : Finpartition (univ : Finset (Fin N)))).real {ω | ∀ i ≤ n, ω i = z i}
  rw [Rhone.MarkovChain.FinChain.pathLaw_real_cylinder]
  rw [measureReal_def, samplePartition_cylinder_mass, ENNReal.toReal_mul, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal ((partitionChain (Fin N)).jumpChain.nonneg _ _)]
  split_ifs <;> simp
end Rhone.Coalescent.SmcPrime
