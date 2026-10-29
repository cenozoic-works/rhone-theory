/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AbsolutelyContinuousClock

/-! # Separation from panmictic forward systems with measurable time variation -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

structure PanForwardSystem where
  rate : ℝ → ℝ
  recombination : ℝ → ℝ
  clock : ℝ → ℝ
  firstFlux : ℝ → ℝ
  postMass : ℝ → ℝ → Fin 2 → ℝ
  rate_measurable : Measurable rate
  recombination_measurable : Measurable recombination
  clock_measurable : Measurable clock
  firstFlux_measurable : Measurable firstFlux
  rate_nonneg : ∀ t, 0 ≤ rate t
  recombination_nonneg : ∀ t, 0 ≤ recombination t
  firstFlux_nonneg : ∀ t, 0 ≤ firstFlux t
  initial_mass : ∀ s, 0 < s → (∑ i, postMass s s i) = 1
  post_nonneg : ∀ s t, 0 < s → s ≤ t → ∀ i, 0 ≤ postMass s t i
  post_ac : ∀ s t, 0 < s → s < t → ∀ i,
    AbsolutelyContinuousOnInterval (fun x => postMass s x i) s t
  clock_ac : ∀ s t, 0 < s → s < t → AbsolutelyContinuousOnInterval clock s t
  post_equation : ∀ s t, 0 < s → s < t → ∀ᵐ x, x ∈ uIcc s t → ∀ i,
    HasDerivAt (fun y => postMass s y i)
      (∑ j, postMass s x j * panPostGenerator (rate x) (recombination x) j i) x
  clock_equation : ∀ s t, 0 < s → s < t → ∀ᵐ x, x ∈ uIcc s t →
    HasDerivAt clock (rate x) x

noncomputable def PanForwardSystem.upperDensity (P : PanForwardSystem) (s t : ℝ) : ℝ :=
  P.firstFlux s * P.rate t * (∑ i, P.postMass s t i)

theorem PanForwardSystem.survival_clock (P : PanForwardSystem) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) :
    (∑ i, P.postMass s t i) = Real.exp (P.clock s - P.clock t) := by
  have h := panPost_survival_clock_ae P.rate P.recombination P.clock (P.postMass s) s t
    (P.post_ac s t hs hst) (P.clock_ac s t hs hst)
    (P.post_equation s t hs hst) (P.clock_equation s t hs hst)
  simpa only [P.initial_mass s hs, one_mul] using h

theorem PanForwardSystem.upperDensity_clock (P : PanForwardSystem) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) :
    P.upperDensity s t = panClockDensity P.firstFlux P.rate P.clock s t := by
  rw [PanForwardSystem.upperDensity, P.survival_clock hs hst]
  rfl

theorem island_jointLaw_ne_pan_forward (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) (P : PanForwardSystem)
    (μ : Measure (ℝ × ℝ))
    (hμ : μ.restrict timeBox = timeBoxMeasure.withDensity
      (fun p => ENNReal.ofReal (P.upperDensity p.1 p.2))) :
    jointLaw k c q r ≠ μ := by
  apply island_jointLaw_ne_pan_clock k hc hq hr μ P.firstFlux P.rate P.clock
    P.firstFlux_measurable P.rate_measurable P.clock_measurable
    P.firstFlux_nonneg P.rate_nonneg
  rw [hμ]
  apply withDensity_congr_ae
  have hm : ∀ᵐ p ∂timeBoxMeasure, p ∈ timeBox := by
    unfold timeBoxMeasure
    rw [Measure.prod_restrict]
    exact ae_restrict_mem timeBox_measurable
  filter_upwards [hm] with p hp
  rw [P.upperDensity_clock hp.1.1 (lt_trans hp.1.2 hp.2)]

end Rhone.Statistics.Identifiability
