/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialLengthMean

/-! # Stopping probability of the spatial update -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

private theorem inverse_uniform_tail (r d : ℝ) (hr : 0 < r) (hd : 0 ≤ d) :
    unitUniform {u | d ≤ -Real.log u / r} = ENNReal.ofReal (Real.exp (-(r*d))) := by
  have hm : MeasurableSet {u : ℝ | d ≤ -Real.log u / r} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [unitUniform, Measure.restrict_apply hm]
  have hequiv (u : ℝ) (hu : 0 < u) :
      d ≤ -Real.log u / r ↔ u ≤ Real.exp (-(r*d)) := by
    rw [le_div_iff₀ hr, ← Real.log_le_iff_le_exp hu]
    constructor <;> intro h <;> nlinarith
  by_cases hd0 : d = 0
  · have hset : {u : ℝ | d ≤ -Real.log u / r} ∩ Set.Ioo 0 1 = Set.Ioo 0 1 := by
      apply Set.inter_eq_right.mpr
      intro u hu
      apply (hequiv u hu.1).mpr
      simpa [hd0] using hu.2.le
    rw [hset]
    simp [hd0]
  · have he1 : Real.exp (-(r*d)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hr (lt_of_le_of_ne hd (Ne.symm hd0))])
    have hset : {u : ℝ | d ≤ -Real.log u / r} ∩ Set.Ioo 0 1 =
        Set.Ioc 0 (Real.exp (-(r*d))) := by
      ext u
      constructor
      · rintro ⟨hw, hu⟩
        exact ⟨hu.1, (hequiv u hu.1).mp hw⟩
      · rintro ⟨hu, he⟩
        exact ⟨(hequiv u hu).mpr he, hu, he.trans_lt he1⟩
    rw [hset, Real.volume_Ioc, sub_zero]

private theorem proposal_distance {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise) :
    (proposal R T u).1 = -Real.log (u 0) / (R / 2 * treeLength T) := by
  unfold proposal
  cases cutPoint T (u 1) (u 2) <;> rfl

theorem spatial_kernel_stop_mass {N : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (z : SpatialState N) (hz : z.1 ≤ 1) :
    spatialKernel N R z {y | y.1 = 1} =
      ENNReal.ofReal (Real.exp (-(R / 2 * treeLength z.2 * (1-z.1)))) := by
  have hstep : Measurable (fun u : ProposalNoise => spatialStep N R z u) :=
    (spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet {y : SpatialState N | y.1 = 1} :=
    measurableSet_eq_fun measurable_fst measurable_const
  rw [spatialKernel_apply, Measure.map_apply hstep hset]
  by_cases hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0
  · have hm : {u : ProposalNoise | (spatialStep N R z u).1 = 1} = Set.univ := by
      simp [spatialStep, hstop]
    change proposalNoiseLaw {u | (spatialStep N R z u).1 = 1} = _
    rw [hm, measure_univ]
    rcases hstop with hx | hr | hl
    · simp [le_antisymm hz hx]
    · simp [le_antisymm hr hR]
    · simp [le_antisymm hl (treeLength_nonneg z.2)]
  · have hr : 0 < R / 2 * treeLength z.2 := by
      push Not at hstop
      exact mul_pos (div_pos hstop.2.1 (by norm_num)) hstop.2.2
    have heq : (fun u : ProposalNoise => spatialStep N R z u) ⁻¹'
        {y : SpatialState N | y.1 = 1} =
        (fun u : ProposalNoise => u 0) ⁻¹'
          {v : ℝ | 1-z.1 ≤ -Real.log v / (R/2*treeLength z.2)} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, spatialStep, hstop, ↓reduceIte]
      rw [proposal_distance]
      by_cases hi : z.1 + -Real.log (u 0) / (R/2*treeLength z.2) < 1
      · simp only [hi, ↓reduceIte]
        constructor <;> intro h <;> linarith
      · simp only [hi, ↓reduceIte, true_iff]
        linarith
    rw [heq]
    have heval := (measurePreserving_eval (fun _ : Fin 5 => unitUniform) (0 : Fin 5)).map_eq
    have ht : MeasurableSet {v : ℝ | 1-z.1 ≤ -Real.log v / (R/2*treeLength z.2)} :=
      measurableSet_le measurable_const (by fun_prop)
    rw [← Measure.map_apply (measurable_pi_apply 0) ht]
    change (Measure.pi (fun _ : Fin 5 => unitUniform)).map (fun u => u 0) _ = _
    rw [heval]
    exact inverse_uniform_tail _ _ hr (sub_nonneg.mpr hz)

theorem spatial_step_stop_output {N : ℕ} (R : ℝ) (z : SpatialState N)
    (u : ProposalNoise) (h : (spatialStep N R z u).1 = 1) :
    spatialStep N R z u = (1, z.2) := by
  by_cases hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0
  · simp [spatialStep, hstop]
  · by_cases hin : z.1 + (proposal R z.2 u).1 < 1
    · have he : z.1 + (proposal R z.2 u).1 = 1 := by
        simpa [spatialStep, hstop, hin] using h
      exact False.elim ((ne_of_lt hin) he)
    · simp [spatialStep, hstop, hin]

theorem spatial_kernel_stop_atom {N : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (z : SpatialState N) (hz : z.1 ≤ 1) :
    (spatialKernel N R z).restrict {y | y.1 = 1} =
      ENNReal.ofReal (Real.exp (-(R/2*treeLength z.2*(1-z.1)))) •
        Measure.dirac (1, z.2) := by
  have hstep : Measurable (fun u : ProposalNoise => spatialStep N R z u) :=
    (spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet {y : SpatialState N | y.1 = 1} :=
    measurableSet_eq_fun measurable_fst measurable_const
  rw [spatialKernel_apply, Measure.restrict_map hstep hset]
  have heq : (fun u => spatialStep N R z u) =ᵐ[
      proposalNoiseLaw.restrict ((fun u => spatialStep N R z u) ⁻¹' {y | y.1 = 1})]
      (fun _ => (1, z.2)) := by
    filter_upwards [ae_restrict_mem (hset.preimage hstep)] with u hu
    exact spatial_step_stop_output R z u hu
  rw [Measure.map_congr heq, Measure.map_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, ← Measure.map_apply hstep hset, ← spatialKernel_apply,
    spatial_kernel_stop_mass R hR z hz]

end Rhone.Coalescent.SmcPrime
