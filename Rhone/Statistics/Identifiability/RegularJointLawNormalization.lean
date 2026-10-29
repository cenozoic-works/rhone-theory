/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularJointLaw

/-! # Generic Tonelli normalization for diagonal and two triangular densities -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem density_lintegral_upperWedge (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in upperWedge, f p ∂planeVolume) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi s, f (s, t) := by
  rw [← lintegral_indicator upperWedge_open.measurableSet]
  change (∫⁻ p, upperWedge.indicator f p ∂(volume : Measure ℝ).prod volume) = _
  rw [lintegral_prod _ (hf.indicator upperWedge_open.measurableSet).aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),
      ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : s < t <;> simp [upperWedge, hs, ht]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
    have hz : (fun t => upperWedge.indicator f (s, t)) = fun _ => 0 := by
      funext t
      simp [upperWedge, hs]
    rw [hz, lintegral_zero]

theorem triangularDensityLaw_mass_of_tail (j : ℝ × ℝ → ℝ) (a : ℝ → ℝ)
    (hj : Measurable j)
    (htail : ∀ s, 0 < s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (j (s, t))) = ENNReal.ofReal (a s)) :
    triangularDensityLaw j univ =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (a s) := by
  rw [triangularDensityLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    density_lintegral_upperWedge _ hj.ennreal_ofReal]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact htail s hs

theorem asymmetricDensityLaw_total (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) :
    (diagonalDensityLaw δ + triangularDensityLaw jA +
      (triangularDensityLaw jB).map Prod.swap) univ =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s)) +
      triangularDensityLaw jA univ + triangularDensityLaw jB univ := by
  rw [Measure.add_apply, Measure.add_apply,
    Measure.map_apply (f := Prod.swap) (measurable_snd.prodMk measurable_fst)
      MeasurableSet.univ,
    preimage_univ, diagonalDensityLaw,
    Measure.map_apply (f := fun t : ℝ => (t, t)) (measurable_id.prodMk measurable_id)
      MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]

theorem asymmetricDensityLaw_probability (δ a b : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hδ : Measurable δ) (ha : Measurable a) (_hb : Measurable b)
    (hjA : Measurable jA) (hjB : Measurable jB)
    (hδn : ∀ s, 0 < s → 0 ≤ δ s)
    (han : ∀ s, 0 < s → 0 ≤ a s)
    (hbn : ∀ s, 0 < s → 0 ≤ b s)
    (htailA : ∀ s, 0 < s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (jA (s, t))) = ENNReal.ofReal (a s))
    (htailB : ∀ s, 0 < s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (jB (s, t))) = ENNReal.ofReal (b s))
    (hmass : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s + a s + b s)) = 1) :
    IsProbabilityMeasure (diagonalDensityLaw δ + triangularDensityLaw jA +
      (triangularDensityLaw jB).map Prod.swap) := by
  constructor
  rw [asymmetricDensityLaw_total,
    triangularDensityLaw_mass_of_tail jA a hjA htailA,
    triangularDensityLaw_mass_of_tail jB b hjB htailB]
  have hsplit : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s + a s + b s)) =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s)) +
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (a s)) +
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (b s)) := by
    calc
      _ = ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (δ s) + ENNReal.ofReal (a s) + ENNReal.ofReal (b s) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs
        dsimp only
        rw [ENNReal.ofReal_add (add_nonneg (hδn s hs) (han s hs)) (hbn s hs),
          ENNReal.ofReal_add (hδn s hs) (han s hs)]
      _ = _ := by
        rw [lintegral_add_left (f := fun s => ENNReal.ofReal (δ s) + ENNReal.ofReal (a s))
          (hδ.ennreal_ofReal.add ha.ennreal_ofReal),
          lintegral_add_left (f := fun s => ENNReal.ofReal (δ s)) hδ.ennreal_ofReal]
  rw [← hsplit]
  exact hmass

theorem regularJointLaw_probability_of_tail (δ a : ℝ → ℝ) (j : ℝ × ℝ → ℝ)
    (hδ : Measurable δ) (ha : Measurable a) (hj : Measurable j)
    (hδn : ∀ s, 0 < s → 0 ≤ δ s) (han : ∀ s, 0 < s → 0 ≤ a s)
    (htail : ∀ s, 0 < s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (j (s, t))) = ENNReal.ofReal (a s))
    (hmass : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s + 2 * a s)) = 1) :
    IsProbabilityMeasure (regularJointLaw δ j) := by
  apply asymmetricDensityLaw_probability δ a a j j hδ ha ha hj hj hδn han han htail htail
  convert hmass using 1
  congr 1
  funext s
  congr 1
  ring

end Rhone.Statistics.Identifiability
