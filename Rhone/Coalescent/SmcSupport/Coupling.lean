/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.JointSampler
public import Rhone.Coalescent.SmcSupport.ProcessProjection
public import Rhone.Probability.ProbabilityTotalVariation

/-! # Trajectory marginals and total variation for the common-noise coupling -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory ProbabilityTheory

theorem jointSamplerProcess_left (R : ℝ) (z : JointState) :
    ((jointSamplerProcess R).pathLaw z).map leftPath =
      (samplerProcess false R).pathLaw z.1 :=
  process_map_pathLaw (jointSamplerProcess R) (samplerProcess false R)
    Prod.fst measurable_fst (jointSamplerKernel_left R) z

theorem jointSamplerProcess_right (R : ℝ) (z : JointState) :
    ((jointSamplerProcess R).pathLaw z).map rightPath =
      (samplerProcess true R).pathLaw z.2 :=
  process_map_pathLaw (jointSamplerProcess R) (samplerProcess true R)
    Prod.snd measurable_snd (jointSamplerKernel_right R) z

theorem sampler_path_tv_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 0 < n) :
    Probability.eventTV
      ((samplerProcess false R).pathLaw (trackedInitial n))
      ((samplerProcess true R).pathLaw (trackedInitial n)) ≤
      ENNReal.ofReal (doubleBound R (n - 1)) := by
  let μ := (jointSamplerProcess R).pathLaw (jointInitial n)
  have hl : Measurable leftPath := measurable_pi_iff.mpr
    (fun k => (measurable_pi_apply k).fst)
  have hr : Measurable rightPath := measurable_pi_iff.mpr
    (fun k => (measurable_pi_apply k).snd)
  have hsub : {ω | leftPath ω ≠ rightPath ω} ≤ᵐ[μ]
      {ω | ∃ k, (ω k).1.2.1 = .two} := by
    filter_upwards [jointSamplerProcess_prefix_agreement R hR n hn] with ω hω
    intro hd
    by_contra hp
    apply hd
    funext k
    exact hω k (fun j _ hj => hp ⟨j, hj⟩)
  have hbad : μ {ω | ∃ k, (ω k).1.2.1 = .two} ≤
      ENNReal.ofReal (doubleBound R (n - 1)) := by
    have he : MeasurableSet {ω : ℕ → TrackedState | ∃ k, (ω k).2.1 = .two} :=
      measurableSet_exists _ (fun k => measurableSet_eq_fun
        (measurable_pi_apply k).snd.fst measurable_const)
    have hmap := Measure.map_apply hl he (μ := μ)
    rw [jointSamplerProcess_left] at hmap
    change μ (leftPath ⁻¹' {ω | ∃ k, (ω k).2.1 = .two}) ≤ _
    rw [← hmap]
    apply (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top _ _) (doubleBound_nonneg R hR (n - 1))).mpr
    exact ever_second_split_le false R hR n hn
  have hc := Rhone.Probability.coupling_inequality_of_bound μ leftPath rightPath hl hr
    (ENNReal.ofReal (doubleBound R (n - 1)))
    ((measure_mono_ae hsub).trans hbad)
  simpa only [μ, jointSamplerProcess_left, jointSamplerProcess_right, jointInitial] using hc

theorem sampler_path_tv_quadratic (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : 0 < n) :
    Probability.eventTV
      ((samplerProcess false R).pathLaw (trackedInitial n))
      ((samplerProcess true R).pathLaw (trackedInitial n)) ≤
      ENNReal.ofReal (min 1 (R ^ 2 * quadraticCoefficient (n - 1))) := by
  exact (sampler_path_tv_le R hR n hn).trans (ENNReal.ofReal_le_ofReal
    (doubleBound_le_min R hR (n - 1)))

end Rhone.Coalescent.SmcSupport
