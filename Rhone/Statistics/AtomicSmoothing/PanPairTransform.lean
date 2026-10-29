/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.PanSurvival
public import Rhone.Statistics.AtomicSmoothing.CDFEndpoints
public import Rhone.Statistics.Identifiability.PanPairTailProbability

/-! # Exponential transform of the pan pair time and laws realizing it -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Rhone.Statistics.AtomicSmoothing
open Algebra.Identifiability MarkovChain.Identifiability Identifiability

instance panPairLaw_nullSingleton (r : ℝ → ℝ) : NullSingletonClass (panPairLaw r) := by
  unfold panPairLaw
  infer_instance

lemma exp_neg_preimage_Iic {x : ℝ} (hx : 0 < x) :
    (fun t : ℝ => Real.exp (-t)) ⁻¹' Iic x = Ici (-Real.log x) := by
  ext t
  simp only [mem_preimage, mem_Iic, mem_Ici, ← Real.le_log_iff_exp_le hx]
  constructor <;> intro ht <;> linarith

lemma pan_pair_transform_inner (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))).real (Iic x) =
      Real.exp (-integratedClock r (-Real.log x)) := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic, exp_neg_preimage_Iic hx]
  rw [← measureReal_congr (Ioi_ae_eq_Ici (μ := panPairLaw r) (a := -Real.log x))]
  exact PanThreeSample.pairLaw_real_Ioi r hr hn ht
    (neg_nonneg.mpr (Real.log_nonpos hx.le hx1))

lemma pan_pair_transform_below (r : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))).real (Iic x) = 0 := by
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have he : (fun t : ℝ => Real.exp (-t)) ⁻¹' Iic x = ∅ := by
    ext t
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
    exact not_le_of_gt (hx.trans_lt (Real.exp_pos _))
  rw [he]
  simp

lemma pan_pair_transform_above (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {x : ℝ} (hx : 1 ≤ x) :
    ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))).real (Iic x) = 1 := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have he : (fun t : ℝ => Real.exp (-t)) ⁻¹' Iic x =ᵐ[panPairLaw r] univ := by
    filter_upwards [PanThreeSample.pairLaw_positive_support r] with t ht0
    apply propext
    constructor
    · intro _
      exact mem_univ t
    · intro _
      exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le)).trans hx
  rw [measureReal_congr he, probReal_univ]

theorem exists_pan_pair_transform_law {α : Type*} [Fintype α] (loc w : α → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hl : ∀ a, 0 ≤ loc a - τ) (hu : ∀ a, loc a + τ ≤ 1) :
    ∃ r : ℝ → ℝ, LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧
      Tendsto (integratedClock r) atTop atTop ∧
      (panPairLaw r).map (fun t : ℝ => Real.exp (-t)) = mixtureLaw loc w τ := by
  obtain ⟨r, hr, hn, ht, he⟩ := exists_regular_pan_rate loc w hτ h1 hw hs hl hu
  refine ⟨r, hr, hn, ht, ?_⟩
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  let : IsProbabilityMeasure ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))) :=
    inferInstance
  let : IsProbabilityMeasure (mixtureLaw loc w τ) := mixtureLaw_probability loc w hτ.le h1 hw hs
  apply Measure.ext_of_Iic
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))).real (Iic x) =
    (mixtureLaw loc w τ).real (Iic x)
  rw [mixtureLaw_real_Iic loc w hτ h1 hw]
  by_cases hx : x ≤ 0
  · rw [pan_pair_transform_below r hx, mixtureCDF_below loc w hτ hl hx]
  · have hx0 : 0 < x := lt_of_not_ge hx
    by_cases hx1 : x ≤ 1
    · rw [pan_pair_transform_inner r hr hn ht hx0 hx1,
        he _ (neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)), neg_neg, Real.exp_log hx0]
    · have hx1' : 1 ≤ x := le_of_not_ge hx1
      rw [pan_pair_transform_above r hr hn ht hx1', mixtureCDF_above loc w hτ hu hs hx1']

end Rhone.Statistics.AtomicSmoothing
