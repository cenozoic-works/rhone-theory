/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableClockCalculus

/-! # Coordinate marginals of product and triangular density measures -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem product_density_map_fst_ae {f : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.prod volume)) :
    ((volume.prod volume).withDensity f).map Prod.fst =
      volume.withDensity (fun s => ∫⁻ t, f (s,t)) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA, ← prod_univ]
  simpa only [setLIntegral_univ] using
    setLIntegral_prod (μ := volume) (ν := volume) (s := A) (t := univ) f hf.restrict

theorem product_density_map_snd_ae {f : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.prod volume)) :
    ((volume.prod volume).withDensity f).map Prod.snd =
      volume.withDensity (fun t => ∫⁻ s, f (s,t)) := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, withDensity_apply _ (measurable_snd hA),
    withDensity_apply _ hA, ← univ_prod]
  simpa only [setLIntegral_univ] using
    setLIntegral_prod_symm (μ := volume) (ν := volume) (s := univ) (t := A)
      f hf.restrict

theorem triangular_map_fst_ae (j : ℝ × ℝ → ℝ) (hj : AEMeasurable j (planeVolume.restrict
  upperWedge)) :
    (triangularDensityLaw j).map Prod.fst =
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun s => ∫⁻ t in Ioi s, ENNReal.ofReal (j (s,t))) := by
  rw [triangularDensityLaw, ← withDensity_indicator upperWedge_open.measurableSet]
  change ((volume.prod volume).withDensity _).map Prod.fst = _
  rw [product_density_map_fst_ae ((aemeasurable_indicator_iff upperWedge_open.measurableSet).mpr
    hj.ennreal_ofReal),
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

theorem triangular_map_snd_ae (j : ℝ × ℝ → ℝ) (hj : AEMeasurable j (planeVolume.restrict
  upperWedge)) :
    (triangularDensityLaw j).map Prod.snd =
    volume.withDensity (fun t => ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s,t))) := by
  rw [triangularDensityLaw, ← withDensity_indicator upperWedge_open.measurableSet]
  change ((volume.prod volume).withDensity _).map Prod.snd = _
  rw [product_density_map_snd_ae ((aemeasurable_indicator_iff upperWedge_open.measurableSet).mpr
    hj.ennreal_ofReal)]
  congr 1
  funext t
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s ∧ s < t <;> simp [upperWedge, hs]

theorem triangular_map_snd_positive_ae (j : ℝ × ℝ → ℝ) (hj : AEMeasurable j (planeVolume.restrict
  upperWedge)) :
    (triangularDensityLaw j).map Prod.snd =
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s,t))) := by
  rw [triangular_map_snd_ae j hj, ← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), Ioo_eq_empty ht]
    simp

theorem withDensity_add_left_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    μ.withDensity (f + g) = μ.withDensity f + μ.withDensity g := by
  ext A hA
  rw [Measure.add_apply, withDensity_apply _ hA, withDensity_apply _ hA,
    withDensity_apply _ hA]
  exact lintegral_add_left' hf.restrict _

theorem regularJointLaw_map_swap (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ) :
    (regularJointLaw δ j).map Prod.swap = regularJointLaw δ j := by
  have hm : Measurable (Prod.swap : ℝ × ℝ → ℝ × ℝ) := measurable_snd.prodMk measurable_fst
  have hd : (diagonalDensityLaw δ).map Prod.swap = diagonalDensityLaw δ := by
    rw [diagonalDensityLaw, Measure.map_map (f := fun t : ℝ => (t,t)) hm (measurable_id.prodMk
      measurable_id)]
    rfl
  rw [regularJointLaw, Measure.map_add _ _ hm, Measure.map_add _ _ hm, hd,
    Measure.map_map hm hm]
  have he : (Prod.swap : ℝ × ℝ → ℝ × ℝ) ∘ Prod.swap = id := by
    funext p
    rfl
  rw [he, Measure.map_id]
  ac_rfl

theorem triangularDensityLaw_mass_of_tail_ae (j : ℝ × ℝ → ℝ) (a : ℝ → ℝ)
    (hj : AEMeasurable j (planeVolume.restrict upperWedge))
    (htail : ∀ᵐ s ∂volume.restrict (Ioi 0),
      (∫⁻ t in Ioi s, ENNReal.ofReal (j (s, t))) = ENNReal.ofReal (a s)) :
    triangularDensityLaw j univ = ∫⁻ s in Ioi 0, ENNReal.ofReal (a s) := by
  have he : (triangularDensityLaw j).map Prod.fst =
      (volume.restrict (Ioi 0)).withDensity (fun s => ENNReal.ofReal (a s)) := by
    rw [triangular_map_fst_ae _ hj]
    exact withDensity_congr_ae htail
  have hh := congrArg (fun μ : Measure ℝ => μ univ) he
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hh

theorem regularJointLaw_probability_of_tail_ae (δ a : ℝ → ℝ) (j : ℝ × ℝ → ℝ)
    (hδ : AEMeasurable δ (volume.restrict (Ioi 0)))
    (ha : AEMeasurable a (volume.restrict (Ioi 0)))
    (hj : AEMeasurable j (planeVolume.restrict upperWedge))
    (hδn : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ δ s)
    (han : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ a s)
    (htail : ∀ᵐ s ∂volume.restrict (Ioi 0),
      (∫⁻ t in Ioi s, ENNReal.ofReal (j (s, t))) = ENNReal.ofReal (a s))
    (hmass : (∫⁻ s in Ioi 0, ENNReal.ofReal (δ s + 2 * a s)) = 1) :
    IsProbabilityMeasure (regularJointLaw δ j) := by
  constructor
  rw [regularJointLaw, asymmetricDensityLaw_total,
    triangularDensityLaw_mass_of_tail_ae j a hj htail]
  have hs : (∫⁻ s in Ioi 0, ENNReal.ofReal (δ s + 2 * a s)) =
      (∫⁻ s in Ioi 0, ENNReal.ofReal (δ s)) +
      (∫⁻ s in Ioi 0, ENNReal.ofReal (a s)) +
      (∫⁻ s in Ioi 0, ENNReal.ofReal (a s)) := by
    calc
      _ = ∫⁻ s in Ioi 0,
          ENNReal.ofReal (δ s) + ENNReal.ofReal (a s) + ENNReal.ofReal (a s) := by
        apply lintegral_congr_ae
        filter_upwards [hδn, han] with s hsδ hsa
        rw [show δ s + 2 * a s = δ s + a s + a s by ring,
          ENNReal.ofReal_add (add_nonneg hsδ hsa) hsa, ENNReal.ofReal_add hsδ hsa]
      _ = _ := by
        rw [lintegral_add_left' (f := fun s => ENNReal.ofReal (δ s) + ENNReal.ofReal (a s))
          (hδ.ennreal_ofReal.add ha.ennreal_ofReal),
          lintegral_add_left' (f := fun s => ENNReal.ofReal (δ s)) hδ.ennreal_ofReal]
  exact hs.symm.trans hmass

end Rhone.Statistics.Identifiability
