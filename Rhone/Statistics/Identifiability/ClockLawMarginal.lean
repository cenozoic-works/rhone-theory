/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DensityMarginals
public import Rhone.Statistics.Identifiability.ClockColumnIntegral

/-! # The coordinate marginal of the constructed joint law is its pair-clock law -/

@[expose] public section

open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem clock_triangular_measurable (rate H N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N) :
    Measurable (fun p : ℝ × ℝ => rate p.1*N p.1*rate p.2*Real.exp (H p.1-H p.2)) :=
  ((((hr.comp continuous_fst).mul (hN.comp continuous_fst)).mul (hr.comp continuous_snd)).mul
    (Real.continuous_exp.comp ((hH.comp continuous_fst).sub (hH.comp continuous_snd)))).measurable

theorem clock_triangular_map_fst (rate H N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t) (hNn : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t) (htail : Tendsto H atTop atTop) :
    (triangularDensityLaw (fun p => rate p.1*N p.1*rate p.2*Real.exp (H p.1-H p.2))).map
      Prod.fst = (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal (rate t*N t)) := by
  rw [triangular_map_fst _ (clock_triangular_measurable rate H N hr hH hN)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have he : ∀ t, rate s*N s*rate t*Real.exp (H s-H t) =
      (rate s*N s)*conditionalPairDensity rate H s t := by
    intro t
    unfold conditionalPairDensity
    ring
  simp_rw [he,ENNReal.ofReal_mul (mul_nonneg (hrn s hs.le) (hNn s hs.le))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    conditionalPair_lintegral_one rate H hs.le hrn hclock htail,mul_one]

theorem clock_triangular_map_snd (rate H N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t) (hNn : ∀ t, 0 ≤ t → 0 ≤ N t) :
    (triangularDensityLaw (fun p => rate p.1*N p.1*rate p.2*Real.exp (H p.1-H p.2))).map
      Prod.snd = (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal (rate t*pendingPairMass rate H N t)) := by
  rw [triangular_map_snd_positive _ (clock_triangular_measurable rate H N hr hH hN)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact clock_column_lintegral rate H N hr hH hN hrn hNn ht

noncomputable def conditionalPairLaw (rate H : ℝ → ℝ) (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi s)).withDensity 
    (fun t => ENNReal.ofReal (conditionalPairDensity rate H s t))

theorem clockJointLaw_map_fst (rate H D N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hD : Continuous D) (hN : Continuous N)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hDn : ∀ t, 0 ≤ t → 0 ≤ D t) (hNn : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hzero : D 0 + N 0 = 1)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop)
    (hbalance : ∀ t, 0 ≤ t →
      HasDerivAt (fun x => D x + N x) (-rate t * (D t + 2 * N t)) t) :
    (clockJointLaw rate H D N).map Prod.fst = conditionalPairLaw rate H 0 := by
  unfold clockJointLaw regularJointLaw
  rw [Measure.map_add _ _ measurable_fst,Measure.map_add _ _ measurable_fst,
    diagonalDensityLaw_map_fst,
    Measure.map_map (f := Prod.swap) measurable_fst (measurable_snd.prodMk measurable_fst)]
  change _ + _ + (triangularDensityLaw _).map Prod.snd = _
  rw [clock_triangular_map_fst rate H N hr hH hN hrn hNn hclock htail,
    clock_triangular_map_snd rate H N hr hH hN hrn hNn]
  rw [← withDensity_add_left (f := fun t => ENNReal.ofReal (rate t*D t))
    (hr.mul hD).measurable.ennreal_ofReal]
  rw [← withDensity_add_left
    (f := (fun t => ENNReal.ofReal (rate t*D t)) +
      (fun t => ENNReal.ofReal (rate t*N t)))
    ((hr.mul hD).measurable.ennreal_ofReal.add (hr.mul hN).measurable.ennreal_ofReal)]
  unfold conditionalPairLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hd := mul_nonneg (hrn t ht.le) (hDn t ht.le)
  have hn := mul_nonneg (hrn t ht.le) (hNn t ht.le)
  have hp := mul_nonneg (hrn t ht.le) (pendingPairMass_nonneg rate H N hrn hNn ht.le)
  simp only [Pi.add_apply]
  rw [← ENNReal.ofReal_add hd hn,← ENNReal.ofReal_add (add_nonneg hd hn) hp]
  congr 1
  unfold conditionalPairDensity
  calc
    rate t*D t+rate t*N t+rate t*pendingPairMass rate H N t =
        rate t*(D t+N t+pendingPairMass rate H N t) := by ring
    _ = _ := by rw [marginal_mass_clock_identity rate H D N hr hH hN hzero hclock hbalance ht.le]

end Rhone.Statistics.Identifiability
