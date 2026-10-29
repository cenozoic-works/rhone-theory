/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.TwoIslandSpatial.Flow
public import Rhone.Statistics.ThreeSiteSeparator.MigrationIntervalSeparation
public import Rhone.Statistics.Identifiability.TwoEventFluxLaw

/-! # Direct full-spatial-chain sequence observer and the three-site exclusion -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace Rhone.Statistics.TwoIslandSpatial
open Algebra.Identifiability MarkovChain.Identifiability Identifiability ThreeSiteSeparator

def spatialSequenceMass {K L : ℕ} (π : ThreeTipSites.Roots K L)
    (clock c m : ℝ) (x : ThreeTipSites.Panel K L) : ℝ :=
  ∫ p in upperWedge, ∑ i : Fin 3, spatialDensity c m i p *
    ThreeTipSites.fixedTopology π clock (p.1,p.2-p.1) i x ∂planeVolume

def spatialSequenceLaw {K L : ℕ} (π : ThreeTipSites.Roots K L)
    (clock c m : ℝ) : Measure (ThreeTipSites.Panel K L) :=
  Measure.sum fun x => ENNReal.ofReal (spatialSequenceMass π clock c m x) • Measure.dirac x

lemma spatialSequenceMass_eq {K L : ℕ} (π : ThreeTipSites.Roots K L)
    (clock : ℝ) {c m : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m) (x : ThreeTipSites.Panel K L) :
    spatialSequenceMass π clock c m x =
      ThreeTipSites.mass π clock (IslandThreeTimes.durationLaw 0 c m) x := by
  unfold spatialSequenceMass
  simp_rw [spatial_density_lumped, IslandLabelledCherry.sequence_density_factor]
  rw [ThreeTipSites.mass, IslandThreeTimes.durationLaw,
    integral_map IslandThreeTimes.measurable_toDurations.aemeasurable
      (ThreeTipSites.conditional_measurable π clock x).aestronglyMeasurable]
  symm
  apply TwoEventFluxLaw.integral_ofReal_density
  · exact (IslandThreeTimes.density_continuous 0 c m).measurable.aemeasurable
  · filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
    exact IslandThreeTimes.density_nonneg 0 hc hm hp

lemma spatialSequenceLaw_eq {K L : ℕ} (π : ThreeTipSites.Roots K L)
    (clock : ℝ) {c m : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m) :
    spatialSequenceLaw π clock c m =
      ThreeTipSites.law π clock (IslandThreeTimes.durationLaw 0 c m) := by
  unfold spatialSequenceLaw ThreeTipSites.law
  congr 1
  funext x
  rw [spatialSequenceMass_eq π clock hc hm x]

theorem full_spatial_three_site_separation {K : ℕ} (hK : 3 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    spatialSequenceLaw (uniformBlockRoots K 3 (by omega)) 2 1 (1/100) ≠
      ThreeTipSites.law (uniformBlockRoots K 3 (by omega)) k
        (PanThreeSample.durationLaw r) := by
  rw [spatialSequenceLaw_eq _ _ (by norm_num) (by norm_num)]
  exact three_site_separation hK r hr hn ht hk

theorem full_spatial_weak_migration_separation {K : ℕ} (hK : 3 ≤ K)
    {m : ℝ} (hm : 0 < m) (hsmall : m ≤ 1 / 1000)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    spatialSequenceLaw (uniformBlockRoots K 3 (by omega)) 2 1 m ≠
      ThreeTipSites.law (uniformBlockRoots K 3 (by omega)) k
        (PanThreeSample.durationLaw r) := by
  rw [spatialSequenceLaw_eq _ _ (by norm_num) hm.le]
  exact weak_migration_three_site_separation hK hm hsmall r hr hn ht hk

end Rhone.Statistics.TwoIslandSpatial
