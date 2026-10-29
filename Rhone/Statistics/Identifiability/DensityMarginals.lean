/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TriangularMass

/-! # Coordinate marginals of product and triangular density measures -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem product_density_map_fst {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ((volume.prod volume).withDensity f).map Prod.fst =
      volume.withDensity (fun s => ∫⁻ t, f (s,t)) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA, ← prod_univ]
  simpa only [setLIntegral_univ] using
    setLIntegral_prod (μ := volume) (ν := volume) (s := A) (t := univ) f hf.aemeasurable.restrict

theorem product_density_map_snd {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ((volume.prod volume).withDensity f).map Prod.snd =
      volume.withDensity (fun t => ∫⁻ s, f (s,t)) := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, withDensity_apply _ (measurable_snd hA),
    withDensity_apply _ hA, ← univ_prod]
  simpa only [setLIntegral_univ] using
    setLIntegral_prod_symm (μ := volume) (ν := volume) (s := univ) (t := A)
      f hf.aemeasurable.restrict

theorem triangular_map_fst (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map Prod.fst =
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun s => ∫⁻ t in Ioi s, ENNReal.ofReal (j (s,t))) := by
  rw [triangularDensityLaw, ← withDensity_indicator upperWedge_open.measurableSet]
  change ((volume.prod volume).withDensity _).map Prod.fst = _
  rw [product_density_map_fst (hj.ennreal_ofReal.indicator upperWedge_open.measurableSet),
    ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext s
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : s < t <;> simp [upperWedge, hs, ht]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
    have hz : (fun t => upperWedge.indicator (fun p => ENNReal.ofReal (j p)) (s,t)) =
        fun _ => 0 := by
      funext t
      simp [upperWedge, hs]
    rw [hz, lintegral_zero]

theorem triangular_map_snd (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map Prod.snd =
    volume.withDensity (fun t => ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s,t))) := by
  rw [triangularDensityLaw, ← withDensity_indicator upperWedge_open.measurableSet]
  change ((volume.prod volume).withDensity _).map Prod.snd = _
  rw [product_density_map_snd (hj.ennreal_ofReal.indicator upperWedge_open.measurableSet)]
  congr 1
  funext t
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s ∧ s < t <;> simp [upperWedge, hs]

theorem triangular_map_snd_positive (j : ℝ × ℝ → ℝ) (hj : Measurable j) :
    (triangularDensityLaw j).map Prod.snd =
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s,t))) := by
  rw [triangular_map_snd j hj, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), Ioo_eq_empty ht]
    simp

end Rhone.Statistics.Identifiability
