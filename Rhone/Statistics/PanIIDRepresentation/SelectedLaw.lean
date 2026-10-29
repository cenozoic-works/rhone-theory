/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PanIIDRepresentation.CyclicIntegral

/-! # The selected pair pushforward and the pan three-time integral -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.PanIIDRepresentation
open Algebra.Identifiability MarkovChain.Identifiability Identifiability

def selectPair (p : LeftCube) : ℝ × ℝ := (min p.1.1 p.1.2, p.2)

lemma selectPair_map (μ : Measure ℝ) [SFinite μ] :
    ((μ.prod μ).prod μ).map selectPair = (pairMinimum μ).prod μ := by
  have h := Measure.map_prod_map (μ.prod μ) μ
    (show Measurable (fun p : ℝ × ℝ => min p.1 p.2) by fun_prop) measurable_id
  rw [Measure.map_id] at h
  convert! h.symm using 1

lemma integral_selected (μ : Measure ℝ) [SFinite μ]
    (hp : ∀ᵐ x ∂μ, 0 < x) (φ : ℝ × ℝ → ℝ) (hφ : StronglyMeasurable φ) :
    (∫ p : LeftCube, selectedKernel (fun x y => φ (x, y)) p.1.1 p.1.2 p.2
      ∂(μ.prod μ).prod μ) =
      ∫ p in upperWedge, φ p ∂(pairMinimum μ).prod μ := by
  rw [← integral_indicator upperWedge_open.measurableSet, ← selectPair_map,
    integral_map_of_stronglyMeasurable (show Measurable selectPair by unfold selectPair; fun_prop)
      (hφ.indicator upperWedge_open.measurableSet)]
  have hp2 : ∀ᵐ p ∂μ.prod μ, 0 < min p.1 p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp,
      Measure.quasiMeasurePreserving_snd.ae hp] with p ha hb
    exact lt_min ha hb
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp2] with p hpmin
  simp only [selectedKernel, selectPair, indicator_apply, upperWedge, mem_ofPred_eq]
  simp only [hpmin, true_and]

theorem pan_integral_eq_selected (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    (φ : ℝ × ℝ → ℝ) (hφ : StronglyMeasurable φ) :
    (∫ p, φ p ∂PanThreeSample.law r) =
      (3 / 2 : ℝ) * ∫ p : LeftCube,
        selectedKernel (fun x y => φ (x, y)) p.1.1 p.1.2 p.2
        ∂((panPairLaw r).prod (panPairLaw r)).prod (panPairLaw r) := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  rw [integral_selected _ (PanThreeSample.pairLaw_positive_support r) φ hφ,
    pairMinimum_pan r hr hn ht, PanThreeSample.law_product_representation r hr hn,
    Measure.restrict_smul, integral_smul_measure]
  norm_num

end Rhone.Statistics.PanIIDRepresentation
