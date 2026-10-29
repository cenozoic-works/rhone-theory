/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TriangularMass
public import Rhone.Statistics.Identifiability.ClockLawIdentification

/-! # Normalization of the nonautonomous joint clock law from its first-event flux -/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem regularJointLaw_total (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ) :
    regularJointLaw δ j univ =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s)) +
      triangularDensityLaw j univ + triangularDensityLaw j univ := by
  rw [regularJointLaw,Measure.add_apply,Measure.add_apply,
    Measure.map_apply (f := Prod.swap) (measurable_snd.prodMk measurable_fst) MeasurableSet.univ,
    preimage_univ,diagonalDensityLaw,
    Measure.map_apply (f := fun t : ℝ => (t,t)) (measurable_id.prodMk measurable_id)
      MeasurableSet.univ,preimage_univ,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]

theorem clockEventLaw_probability (δ b rate H : ℝ → ℝ)
    (hδ : Measurable δ) (hb : Measurable b) (hr : Measurable rate) (hH : Measurable H)
    (hδn : ∀ t, 0 ≤ t → 0 ≤ δ t) (hbn : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hkernel : ∀ s, 0 ≤ s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (conditionalPairDensity rate H s t)) = 1)
    (hmass : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s + b s + b s)) = 1) :
    IsProbabilityMeasure (regularJointLaw δ
      (fun p => b p.1*conditionalPairDensity rate H p.1 p.2)) := by
  constructor
  rw [regularJointLaw_total,triangular_clock_mass b rate H hb hr hH hbn hkernel]
  have hsplit : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s + b s + b s)) =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s))+
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (b s))+
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (b s)) := by
    calc
      _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (δ s)+ENNReal.ofReal (b s)+
          ENNReal.ofReal (b s) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs
        dsimp only
        rw [ENNReal.ofReal_add (add_nonneg (hδn s hs.le) (hbn s hs.le)) (hbn s hs.le),
          ENNReal.ofReal_add (hδn s hs.le) (hbn s hs.le)]
      _ = _ := by
        rw [lintegral_add_left (f := fun s => ENNReal.ofReal (δ s)+ENNReal.ofReal (b s))
          (hδ.ennreal_ofReal.add hb.ennreal_ofReal),
          lintegral_add_left (f := fun s => ENNReal.ofReal (δ s)) hδ.ennreal_ofReal]
  rw [← hsplit]
  exact hmass

theorem firstFlux_lintegral_one (G δ b : ℝ → ℝ)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (-(δ t + b t + b t)) t)
    (hzero : G 0 = 1) (htail : Tendsto G atTop (𝓝 0))
    (hδn : ∀ t, 0 ≤ t → 0 ≤ δ t) (hbn : ∀ t, 0 ≤ t → 0 ≤ b t) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (δ t + b t + b t)) = 1 := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (fun x => 1-G x) (δ t + b t + b t) t := by
    intro t ht
    convert! (hG t ht).const_sub 1 using 1
    ring
  have hn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ δ t + b t + b t := fun t ht =>
    add_nonneg (add_nonneg (hδn t ht.le) (hbn t ht.le)) (hbn t ht.le)
  have hi := integrableOn_Ioi_deriv_of_nonneg' (fun t ht => hd t ht) hn (htail.const_sub 1)
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t ht => hd t ht) hn (htail.const_sub 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [he]
    simp [hzero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hn t ht

end Rhone.Statistics.Identifiability
