/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockSumLaw
public import Rhone.Statistics.Identifiability.CommonClockIslandMarkSymmetry
public import Rhone.Statistics.Identifiability.NoRecombinationOverlap

/-! # Exact diagonal-and-triangles decomposition of the marked island law -/

@[expose] public section

open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem commonClock_lower_component (μ ν : Measure ℝ) :
    (μ.prod ν).map (fun p : ℝ × ℝ => (p.1+p.2,p.1)) =
      ((μ.prod ν).map upperShear).map Prod.swap := by
  rw [Measure.map_map measurable_swap upperShear.measurable]
  rfl

theorem commonClockIslandJointLaw_eq_regular_of_symmetry (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h13 : markFlux k c q r 1 = markFlux k c q r 3)
    (h24 : markFlux k c q r 2 = markFlux k c q r 4) :
    jointLaw k c q r = regularJointLaw (markFlux k c q r 0)
      (fun p => upperDensity k c q r p.1 p.2) := by
  have hm3 : markLaw k c q r 3 = markLaw k c q r 1 := by
    simp only [markLaw, ← h13]
  have hm4 : markLaw k c q r 4 = markLaw k c q r 2 := by
    simp only [markLaw, ← h24]
  have hu : upperEventLaw k c q r = triangularDensityLaw
      (fun p => upperDensity k c q r p.1 p.2) :=
    upperEventLaw_density k hc hq hr
  have hzero : ((markLaw k c q r 0).prod (lagLaw k c q 0)).map (recoverTimes 0) =
      diagonalDensityLaw (markFlux k c q r 0) :=
    zero_mark_component_eq_diagonal k c q r
  rw [jointLaw, Measure.sum_fintype]
  simp only [Fin.sum_univ_succ]
  rw [hzero]
  norm_num [lagLaw, postPairState]
  change diagonalDensityLaw (markFlux k c q r 0) +
    ((((markLaw k c q r 1).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)).map upperShear) +
    ((((markLaw k c q r 2).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 1)).map upperShear) +
    ((((markLaw k c q r 3).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)).map
      (fun p : ℝ × ℝ => (p.1+p.2,p.1))) +
    (((markLaw k c q r 4).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 1)).map
      (fun p : ℝ × ℝ => (p.1+p.2,p.1)))))) = _
  rw [hm3, hm4, commonClock_lower_component, commonClock_lower_component,
    ← Measure.map_add _ _ measurable_swap]
  change diagonalDensityLaw (markFlux k c q r 0) +
    ((((markLaw k c q r 1).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)).map upperShear) +
    ((((markLaw k c q r 2).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 1)).map upperShear) +
      (upperEventLaw k c q r).map Prod.swap)) = _
  calc
    _ = diagonalDensityLaw (markFlux k c q r 0) + upperEventLaw k c q r +
        (upperEventLaw k c q r).map Prod.swap := by
          unfold upperEventLaw
          ac_rfl
    _ = _ := by rw [hu]; rfl

noncomputable def commonClockIslandSumDensity (k : ℕ) (c q r z : ℝ) : ℝ :=
  markFlux k c q r 0 (z/2) / 2 +
    2 * ∫ s in 0..z/2, upperDensity k c q r s (z-s)

theorem commonClockIslandSumDensity_continuous (k : ℕ) (c q r : ℝ) :
    Continuous (commonClockIslandSumDensity k c q r) := by
  have hj : Continuous (fun p : ℝ × ℝ => upperDensity k c q r p.2 (p.1-p.2)) :=
    (upperDensity_continuous k c q r).comp
      (f := fun p : ℝ × ℝ => (p.2, p.1-p.2))
      (continuous_snd.prodMk (continuous_fst.sub continuous_snd))
  have hi : Continuous (fun z : ℝ =>
      ∫ s in 0..z/2, upperDensity k c q r s (z-s)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun z s => upperDensity k c q r s (z-s)) hj
      (continuous_id.div_const 2)
  exact (((markFlux_continuous k c q r 0).comp
    (continuous_id.div_const 2)).div_const 2).add (continuous_const.mul hi)

theorem commonClockIslandSumDensity_nonneg (k : ℕ) {c q r z : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (hz : 0 ≤ z) :
    0 ≤ commonClockIslandSumDensity k c q r z := by
  unfold commonClockIslandSumDensity
  apply add_nonneg
    (div_nonneg (markFlux_nonneg k hc hq hr (by positivity) 0) (by norm_num))
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by positivity)
  intro s hs
  exact upperDensity_nonneg k hc hq hr hs.1 (by linarith [hs.2])

theorem commonClockIslandJointLaw_map_sum_of_symmetry (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h13 : markFlux k c q r 1 = markFlux k c q r 3)
    (h24 : markFlux k c q r 2 = markFlux k c q r 4) :
    (jointLaw k c q r).map (fun p => p.1+p.2) =
      (volume.restrict (Ioi (0:ℝ))).withDensity (fun z =>
        ENNReal.ofReal (commonClockIslandSumDensity k c q r z)) := by
  rw [commonClockIslandJointLaw_eq_regular_of_symmetry k hc hq hr h13 h24]
  apply regularJointLaw_map_sum_real _ _
    (markFlux_continuous k c q r 0).measurable
    (upperDensity_continuous k c q r).measurable
  · intro t ht
    exact markFlux_nonneg k hc hq hr ht.le 0
  · intro p hp
    exact upperDensity_nonneg k hc hq hr hp.1.le hp.2.le
  · intro z _
    exact ((upperDensity_continuous k c q r).comp
      (continuous_id.prodMk (continuous_const.sub continuous_id))).intervalIntegrable _ _

theorem commonClockIslandJointLaw_eq_regular (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    jointLaw k c q r = regularJointLaw (markFlux k c q r 0)
      (fun p => upperDensity k c q r p.1 p.2) :=
  commonClockIslandJointLaw_eq_regular_of_symmetry k hc hq hr
    (funext (markFlux1_eq3 k c q r)) (funext (markFlux2_eq4 k c q r))

theorem commonClockIslandJointLaw_map_sum (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    (jointLaw k c q r).map (fun p => p.1+p.2) =
      (volume.restrict (Ioi (0:ℝ))).withDensity (fun z =>
        ENNReal.ofReal (commonClockIslandSumDensity k c q r z)) :=
  commonClockIslandJointLaw_map_sum_of_symmetry k hc hq hr
    (funext (markFlux1_eq3 k c q r)) (funext (markFlux2_eq4 k c q r))

end Rhone.Statistics.Identifiability
