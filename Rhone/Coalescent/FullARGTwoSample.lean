/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSamplePath
public import Rhone.MarkovChain.FullARGTwoSampleFirstExit
public import Rhone.Analysis.SmcPrimeTwoSampleFormulas

/-!
# Two-sample, two-position agreement probability of the unrestricted backward sampler

Source: wilton_carmi_hobolth2015, eq. (5). -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem twoSample_agreement_measurableSet (x y : GenomicProbe) :
    MeasurableSet {G : Genealogy 2 | G x 0 1 = G y 0 1} :=
  measurableSet_eq_fun
    ((measurable_pi_apply (1 : Fin 2)).comp
      ((measurable_pi_apply (0 : Fin 2)).comp (measurable_pi_apply x)))
    ((measurable_pi_apply (1 : Fin 2)).comp
      ((measurable_pi_apply (0 : Fin 2)).comp (measurable_pi_apply y)))

theorem eventProcess_twoLocusPre_tendsto_zero (R : ℝ) (hR : 0 ≤ R) (x y : ℝ) :
    Tendsto (fun n => ((eventProcess false R).pathLaw (initialState 2, (0, .inl ()))).real
      {ω | ω n ∈ twoLocusPre x y}) atTop (𝓝 0) := by
  have hsum := eventProcess_active_events_le 2 R hR
  have hne : ∑' k, (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
      {ω | 2 ≤ (ω k).1.2.2.1} ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
  have hle : ∀ n, (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
      {ω | ω n ∈ twoLocusPre x y} ≤
      (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
        {ω | 2 ≤ (ω n).1.2.2.1} := by
    intro n
    apply measure_mono
    intro ω hω
    have h1 : carrierCount x (ω n).1 = 2 := hω.1
    have h2 := materialCount_le (fun a => materialContains a x) (ω n).1
    change 2 ≤ (ω n).1.2.2.1
    unfold carrierCount at h1
    omega
  have h1 : Tendsto (fun n => (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
      {ω | ω n ∈ twoLocusPre x y}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) hle
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simpa [Measure.real, Function.comp_def] using h2

theorem fullARG_two_sample_agreement_prob_explicit (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1} =
      ENNReal.ofReal
        ((R * ((y.val : ℝ) - (x.val : ℝ)) + 18) /
          ((R * ((y.val : ℝ) - (x.val : ℝ))) ^ 2 + 13 * (R * ((y.val : ℝ) - (x.val : ℝ))) +
            18)) := by
  have hxy' : (x.val : ℝ) < (y.val : ℝ) := by exact_mod_cast hxy
  have hρ : 0 ≤ R * ((y.val : ℝ) - (x.val : ℝ)) := mul_nonneg hR (sub_nonneg.mpr hxy'.le)
  have hx0 : (0 : ℝ) ≤ (x.val : ℝ) := by exact_mod_cast x.property.1
  have hx1 : (x.val : ℝ) < 1 := by exact_mod_cast x.property.2
  have hy0 : (0 : ℝ) ≤ (y.val : ℝ) := by exact_mod_cast y.property.1
  have hy1 : (y.val : ℝ) < 1 := by exact_mod_cast y.property.2
  have hstart : ((initialState 2, ((0 : ℝ), Sum.inl ())) : AugmentedState) ∈
      twoLocusPre (x.val : ℝ) (y.val : ℝ) :=
    ⟨carrierCount_initialState 2 _ hx0 hx1, carrierCount_initialState 2 _ hy0 hy1⟩
  have hexit := MarkovChain.IntervalProcess.pathLaw_real_firstExit (eventProcess false R)
    (twoLocusPre_measurable (x.val : ℝ) (y.val : ℝ))
    (twoLocusDone_measurable (x.val : ℝ) (y.val : ℝ))
    (twoLocusPre_disjoint_done (x.val : ℝ) (y.val : ℝ))
    (twoLocusHarmonic_measurable (x.val : ℝ) (y.val : ℝ) (R * ((y.val : ℝ) - (x.val : ℝ))))
    (M := 1)
    (fun s => abs_le.mpr ⟨by
        have := twoLocusValue_nonneg (R * ((y.val : ℝ) - (x.val : ℝ))) hρ
          (jointCarrierCount (x.val : ℝ) (y.val : ℝ) s.1)
        unfold twoLocusHarmonic
        linarith,
      twoLocusValue_le_one _ hρ _⟩)
    (fun s hs => eventKernel_twoLocus_step R hR (x.val : ℝ) (y.val : ℝ) hxy' s hs)
    (initialState 2, (0, .inl ())) hstart
    (eventProcess_twoLocusPre_tendsto_zero R hR (x.val : ℝ) (y.val : ℝ))
  have hval : twoLocusHarmonic (x.val : ℝ) (y.val : ℝ) (R * ((y.val : ℝ) - (x.val : ℝ)))
      (initialState 2, (0, .inl ())) =
      (R * ((y.val : ℝ) - (x.val : ℝ)) + 18) /
        ((R * ((y.val : ℝ) - (x.val : ℝ))) ^ 2 + 13 * (R * ((y.val : ℝ) - (x.val : ℝ))) +
          18) := by
    unfold twoLocusHarmonic
    rw [jointCarrierCount_initialState 2 _ _ hx0 hx1 hy0 hy1]
    rfl
  unfold fullARGGenealogyLaw
  rw [Measure.map_apply (genealogyObservation_measurable 2)
    (twoSample_agreement_measurableSet x y)]
  have hae := eventProcess_agreement_ae_iff R hR x y
  have hcongr : (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
      (genealogyObservation 2 ⁻¹' {G | G x 0 1 = G y 0 1}) =
      (eventProcess false R).pathLaw (initialState 2, (0, .inl ()))
        {ω | ∃ n, (∀ k ≤ n, ω k ∈ twoLocusPre (x.val : ℝ) (y.val : ℝ)) ∧
          ω (n + 1) ∈ twoLocusDone (x.val : ℝ) (y.val : ℝ)} := by
    apply measure_congr
    filter_upwards [hae] with ω hω
    exact propext hω
  rw [hcongr, ← hval, ← hexit, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem fullARG_two_sample_agreement_prob (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    fullARGGenealogyLaw 2 R {G | G x 0 1 = G y 0 1} =
      ENNReal.ofReal
        (Analysis.SmcPrime.argAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ)))) :=
  fullARG_two_sample_agreement_prob_explicit R hR x y hxy

end Rhone.Coalescent.IntervalProcess
