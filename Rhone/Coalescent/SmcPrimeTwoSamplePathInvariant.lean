/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSampleStepLaw
public import Rhone.Coalescent.SmcPrimeSpatialLengthMean
public import Rhone.Coalescent.SmcPrimeKingmanActiveUnique
public import Rhone.Coalescent.SmcPrimeKingmanChronology
public import Rhone.Coalescent.SmcPrimeKingmanNonnegative
public import Rhone.Coalescent.SmcPrimeActiveUniqueMeas
public import Rhone.Coalescent.SmcPrimeTreeChronologyMeas

/-!
# Reachable two-sample arrays along the SMC′ chain

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

theorem measurableSet_twoSampleArray : MeasurableSet {T : Tree 2 | TwoSampleArray T} := by
  have h : {T : Tree 2 | TwoSampleArray T} = {T | TreeNormalized T} ∩
      ({T | TreeNonnegative T} ∩ ({T | TreeChronology T} ∩ {T | TreeActiveUnique T})) := by
    ext T
    constructor
    · intro hT
      exact ⟨hT.normalized, hT.nonnegative, hT.chronology, hT.activeUnique⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [h]
  exact (TreeNormalized_measurable 2).inter ((TreeNonnegative_measurable 2).inter
    ((TreeChronology_measurable 2).inter (TreeActiveUnique_measurable 2)))

theorem measurableSet_twoSampleState :
    MeasurableSet {z : SpatialState 2 | TwoSampleArray z.2 ∧ 0 < rootHeight z.2} :=
  (measurableSet_twoSampleArray.preimage measurable_snd).inter
    (measurableSet_lt measurable_const ((rootHeight_measurable 2).comp measurable_snd))

theorem kingmanTreeLaw_twoSampleArray : ∀ᵐ T ∂kingmanTreeLaw 2, TwoSampleArray T := by
  filter_upwards [kingmanTreeLaw_normalized 2, kingmanTreeLaw_nonnegative 2,
    kingmanTreeLaw_chronology 2 (by norm_num), kingmanTreeLaw_active_unique 2 (by norm_num)]
    with T h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem spatialStep_tree_cases {N : ℕ} (R : ℝ) (z : SpatialState N) (u : ProposalNoise) :
    (spatialStep N R z u).2 = z.2 ∨ (spatialStep N R z u).2 = (proposal R z.2 u).2.2 := by
  by_cases hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0
  · left
    simp only [spatialStep, hstop, ↓reduceIte]
  · by_cases hin : z.1 + (proposal R z.2 u).1 < 1
    · right
      simp only [spatialStep, hstop, ↓reduceIte, hin]
    · left
      simp only [spatialStep, hstop, ↓reduceIte, hin]

namespace TwoSampleArray

variable {T : Tree 2}

theorem proposal_rootHeight_pos_ae (hT : TwoSampleArray T) (R : ℝ) (hh : 0 < rootHeight T) :
    ∀ᵐ u ∂proposalNoiseLaw, 0 < rootHeight (SmcPrime.proposal R T u).2.2 := by
  have hg : Measurable ((Iic (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Iic
  have hm : Measurable (fun u : ProposalNoise =>
      rootHeight (SmcPrime.proposal R T u).2.2) :=
    (rootHeight_measurable 2).comp ((measurable_snd.comp measurable_snd).comp
      ((proposal_measurable 2 R).comp (measurable_const.prodMk measurable_id)))
  have hlaw := hT.proposal_rootHeight_lintegral R hh _ hg
  have hz : ∀ a ∈ Ioi (0 : ℝ), ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
      (Iic (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) a = (fun _ => 0) a := by
    intro a ha
    rw [indicator_of_notMem (fun hc : a ∈ Iic (0 : ℝ) => not_lt.mpr hc ha), mul_zero]
  rw [indicator_of_notMem (fun hc : rootHeight T ∈ Iic (0 : ℝ) => not_lt.mpr hc hh), mul_zero,
    setLIntegral_congr_fun measurableSet_Ioi hz, lintegral_zero, add_zero,
    lintegral_eq_zero_iff (show Measurable (fun u : ProposalNoise =>
      (Iic (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞)
        (rootHeight (SmcPrime.proposal R T u).2.2)) from hg.comp hm)] at hlaw
  filter_upwards [hlaw] with u hu
  by_contra hneg
  have hmem : rootHeight (SmcPrime.proposal R T u).2.2 ∈ Iic (0 : ℝ) :=
    not_lt.mp hneg
  rw [indicator_of_mem hmem] at hu
  exact one_ne_zero hu

theorem spatialStep_good_ae (hT : TwoSampleArray T) (R : ℝ) (hh : 0 < rootHeight T) (p : ℝ) :
    ∀ᵐ u ∂proposalNoiseLaw, TwoSampleArray (SmcPrime.spatialStep 2 R (p, T) u).2 ∧
      0 < rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2 := by
  filter_upwards [proposalNoiseLaw_ae_marks, hT.proposal_rootHeight_pos_ae R hh] with u hu hpos
  refine ⟨TwoSampleArray.spatialStep (z := (p, T)) hT R u hu, ?_⟩
  rcases spatialStep_tree_cases R (p, T) u with h | h
  · rw [h]
    exact hh
  · rw [h]
    exact hpos

end TwoSampleArray

theorem spatialProcess_pathLaw_twoSampleArray_ae (R : ℝ) (z : SpatialState 2)
    (hz : TwoSampleArray z.2) (hh : 0 < rootHeight z.2) :
    ∀ᵐ ω ∂(spatialProcess 2 R).pathLaw z,
      ∀ n, TwoSampleArray (ω n).2 ∧ 0 < rootHeight (ω n).2 := by
  have hGood := measurableSet_twoSampleState
  rw [ae_all_iff]
  intro n
  have hn : (((spatialProcess 2 R).pathLaw z).map (fun ω => ω n))
      {z : SpatialState 2 | TwoSampleArray z.2 ∧ 0 < rootHeight z.2}ᶜ = 0 := by
    induction n with
    | zero =>
      rw [Rhone.MarkovChain.DiscreteProcess.map_eval_zero, Measure.dirac_apply' _ hGood.compl]
      exact indicator_of_notMem
        (s := {z : SpatialState 2 | TwoSampleArray z.2 ∧ 0 < rootHeight z.2}ᶜ)
        (fun hc => hc ⟨hz, hh⟩) _
    | succ n ih =>
      rw [Rhone.MarkovChain.DiscreteProcess.map_eval_succ,
        Measure.bind_apply hGood.compl (Kernel.measurable _).aemeasurable]
      change ∫⁻ z', spatialKernel 2 R z' _ ∂_ = 0
      rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hGood.compl)]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp ih] with z' hz'
      have hz'' : TwoSampleArray z'.2 ∧ 0 < rootHeight z'.2 := not_not.mp hz'
      rw [spatialKernel_apply, Measure.map_apply
        (show Measurable (fun u => spatialStep 2 R z' u) from
          (spatialStep_measurable 2 R).comp measurable_prodMk_left) hGood.compl]
      refine measure_eq_zero_iff_ae_notMem.mpr ?_
      filter_upwards [hz''.1.spatialStep_good_ae R hz''.2 z'.1] with u hu
      exact fun hc => hc hu
  rw [Measure.map_apply (measurable_pi_apply n) hGood.compl] at hn
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with ω hω
  exact not_not.mp hω

theorem spatialProcess_law_twoSampleArray_ae (R : ℝ) (μ₀ : Measure (SpatialState 2))
    (hμ : ∀ᵐ z ∂μ₀, TwoSampleArray z.2 ∧ 0 < rootHeight z.2) :
    ∀ᵐ ω ∂(spatialProcess 2 R).law μ₀,
      ∀ n, TwoSampleArray (ω n).2 ∧ 0 < rootHeight (ω n).2 := by
  have hGood := measurableSet_twoSampleState
  have hM : MeasurableSet (⋂ n : ℕ, (fun ω : ℕ → SpatialState 2 => ω n) ⁻¹'
      {z : SpatialState 2 | TwoSampleArray z.2 ∧ 0 < rootHeight z.2}) :=
    MeasurableSet.iInter fun n => hGood.preimage (measurable_pi_apply n)
  have h0 : ((spatialProcess 2 R).law μ₀) (⋂ n : ℕ, (fun ω : ℕ → SpatialState 2 => ω n) ⁻¹'
      {z : SpatialState 2 | TwoSampleArray z.2 ∧ 0 < rootHeight z.2})ᶜ = 0 := by
    rw [Rhone.MarkovChain.DiscreteProcess.law,
      Measure.bind_apply hM.compl (Kernel.measurable _).aemeasurable,
      lintegral_eq_zero_iff (Kernel.measurable_coe _ hM.compl)]
    filter_upwards [hμ] with z hz
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [spatialProcess_pathLaw_twoSampleArray_ae R z hz.1 hz.2] with ω hω
    exact fun hc => hc (mem_iInter.mpr hω)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with ω hω
  exact mem_iInter.mp (not_not.mp hω)

end Rhone.Coalescent.SmcPrime
