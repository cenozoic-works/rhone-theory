/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ObservationMoments
public import Rhone.Statistics.SingleSiteChannel.Formula

/-! # Labelled joint observer and its zero-clock/star boundaries -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites SingleSiteChannel ThreeSiteSeparator
open Identifiability.EqualRatesMutation

abbrev Joint := (ℝ × ℝ) × Fin 3

def jointMass {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure Joint)
    (x : Panel K L) : ℝ := ∫ g, fixedTopology π k g.1 g.2 x ∂μ

def jointSequenceLaw {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure Joint) :
    Measure (Panel K L) :=
  Measure.sum fun x => ENNReal.ofReal (jointMass π k μ x) • Measure.dirac x

theorem transition_zero_clock (K : ℕ) (t : ℝ) : transition K 0 t = 1 := by
  simp [transition]

theorem star_site_orientation {K : ℕ} (hK : 0 < K) (k u : ℝ)
    (q : Fin 3) (x : Triple K) :
    site K (fun _ => 1 / (K : ℝ)) k (u, 0) (orientation K q x) =
      site K (fun _ => 1 / (K : ℝ)) k (u, 0) x := by
  rw [site_eq_star hK, site_eq_star hK]
  simp only [mul_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  fin_cases q <;> simp [orientation, cycle] <;> ring

theorem star_fixed_topology {K L : ℕ} (hK : 0 < K) (k u : ℝ)
    (q p : Fin 3) (x : Panel K L) :
    fixedTopology (uniformBlockRoots K L hK) k (u, 0) q x =
      fixedTopology (uniformBlockRoots K L hK) k (u, 0) p x := by
  unfold fixedTopology uniformBlockRoots
  apply Finset.prod_congr rfl
  intro s _
  rw [star_site_orientation hK, star_site_orientation hK]

theorem star_labels_same_sequence_law {K L : ℕ} (hK : 0 < K) (k u : ℝ)
    (q p : Fin 3) :
    jointSequenceLaw (uniformBlockRoots K L hK) k (Measure.dirac ((u, 0), q)) =
      jointSequenceLaw (uniformBlockRoots K L hK) k (Measure.dirac ((u, 0), p)) := by
  unfold jointSequenceLaw
  congr 1
  funext x
  simp only [jointMass, integral_dirac]
  rw [star_fixed_topology hK k u q p x]

theorem site_zero_clock {K : ℕ} (π : Fin K → ℝ) (t : ℝ × ℝ) (x : Triple K) :
    site K π 0 t x = site K π 0 (0, 0) x := by
  unfold site
  simp_rw [transition_zero_clock]

theorem fixed_zero_clock {K L : ℕ} (hK : 0 < K) (g : Joint) (x : Panel K L) :
    fixedTopology (uniformBlockRoots K L hK) 0 g.1 g.2 x =
      fixedTopology (uniformBlockRoots K L hK) 0 (0, 0) 0 x := by
  calc
    _ = fixedTopology (uniformBlockRoots K L hK) 0 (0, 0) g.2 x := by
      unfold fixedTopology
      apply Finset.prod_congr rfl
      intro s _
      exact site_zero_clock _ _ _
    _ = _ := star_fixed_topology hK 0 0 g.2 0 x

theorem zero_clock_all_probability_sources {K L : ℕ} (hK : 0 < K)
    (μ ν : Measure Joint) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    jointSequenceLaw (uniformBlockRoots K L hK) 0 μ =
      jointSequenceLaw (uniformBlockRoots K L hK) 0 ν := by
  unfold jointSequenceLaw
  congr 1
  funext x
  unfold jointMass
  simp_rw [fixed_zero_clock hK]
  simp

end Rhone.Statistics.CollapsedGenealogy
