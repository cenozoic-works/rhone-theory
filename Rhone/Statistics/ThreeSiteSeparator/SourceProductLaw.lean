/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IslandThreeFirstMarginal
public import Rhone.Statistics.Identifiability.ShearDensity

/-! # The literal island duration law as two products, one per post-merger state -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace Rhone.Statistics.ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability

def entryMeasure (m : ℝ) (j : Fin 2) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun s => ENNReal.ofReal (IslandThreeTimes.entryFlux 0 1 m j s))

def postMeasure (m : ℝ) (j : Fin 2) : Measure ℝ := firstExitLaw (pairGenerator 0 1 m) j

lemma ordered_source_product (m : ℝ) (hm : 0 ≤ m) :
    IslandThreeTimes.law 0 1 m =
      ((entryMeasure m 0).prod (postMeasure m 0)).map upperShear +
        ((entryMeasure m 1).prod (postMeasure m 1)).map upperShear := by
  unfold entryMeasure postMeasure firstExitLaw
  rw [shear_product_density _ _
      (IslandThreeTimes.entryFlux_continuous 0 1 m 0).measurable.ennreal_ofReal
      (flowOutput_continuous _ _ _ _).measurable.ennreal_ofReal,
    shear_product_density _ _
      (IslandThreeTimes.entryFlux_continuous 0 1 m 1).measurable.ennreal_ofReal
      (flowOutput_continuous _ _ _ _).measurable.ennreal_ofReal]
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (IslandThreeTimes.entryFlux 0 1 m 0 p.1)*
        ENNReal.ofReal (flowOutput (pairGenerator 0 1 m) 0
          (exitRate (pairGenerator 0 1 m)) 0 (p.2-p.1))) :=
    ((IslandThreeTimes.entryFlux_continuous 0 1 m 0).measurable.comp
      measurable_fst).ennreal_ofReal.mul
      (((flowOutput_continuous _ _ _ _).measurable.comp
        (measurable_snd.sub measurable_fst)).ennreal_ofReal)
  rw [← withDensity_add_left hmeas]
  unfold IslandThreeTimes.law triangularDensityLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  have he (j : Fin 2) : 0 ≤ IslandThreeTimes.entryFlux 0 1 m j p.1 :=
    IslandThreeTimes.entryFlux_nonneg 0 (by norm_num) hm hp.1.le j
  have hd (j : Fin 2) : 0 ≤ IslandThreeTimes.postDensity 0 1 m j (p.2-p.1) :=
    IslandThreeTimes.postDensity_nonneg 0 (by norm_num) hm (sub_nonneg.mpr hp.2.le) j
  change ENNReal.ofReal (IslandThreeTimes.density 0 1 m p) = _
  simp only [IslandThreeTimes.density, Fin.sum_univ_two]
  rw [ENNReal.ofReal_add (mul_nonneg (he 0) (hd 0)) (mul_nonneg (he 1) (hd 1)),
    ENNReal.ofReal_mul (he 0), ENNReal.ofReal_mul (he 1)]
  rfl

theorem source_duration_products (m : ℝ) (hm : 0 ≤ m) :
    IslandThreeTimes.durationLaw 0 1 m =
      (entryMeasure m 0).prod (postMeasure m 0) +
        (entryMeasure m 1).prod (postMeasure m 1) := by
  rw [IslandThreeTimes.durationLaw, ordered_source_product m hm,
    Measure.map_add _ _ IslandThreeTimes.measurable_toDurations,
    Measure.map_map IslandThreeTimes.measurable_toDurations upperShear.measurable,
    Measure.map_map IslandThreeTimes.measurable_toDurations upperShear.measurable]
  have he : IslandThreeTimes.toDurations ∘ upperShear = id := by
    funext p
    simp [IslandThreeTimes.toDurations, upperShear_apply]
  rw [he, Measure.map_id, Measure.map_id]

lemma postMeasure_probability {m : ℝ} (hm : 0 < m) (j : Fin 2) :
    IsProbabilityMeasure (postMeasure m j) :=
  firstExitLaw_probability _ (pairGenerator_metzler 0 hm.le)
    (pairGenerator_rows_nonpos 0 (by norm_num)) j
    (pair_survival_tendsto_zero 0 (by norm_num) hm j)

end Rhone.Statistics.ThreeSiteSeparator
