/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanObservableNecessity
public import Rhone.Statistics.Identifiability.PanGaugeUniqueness

/-! # Recombination gauges for locally integrable panmictic models -/

@[expose] public section

open Set Filter MeasureTheory

namespace Rhone.Statistics.Identifiability

theorem integrablePanPreModel_gauge_states_ae {rate rate' : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hrate : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hx : ∀ᵐ t, 0 ≤ t → 0 < rate t → P.exposure t = Q.exposure t) :
    EqOn Q.D (fun t => panGaugeD (Real.exp (-(Q.exposure t - P.exposure t)))
      (P.D t)) (Ici 0) ∧
    EqOn Q.R (fun t => panGaugeR (Real.exp (-(Q.exposure t - P.exposure t)))
      (P.D t) (P.R t)) (Ici 0) ∧
    EqOn Q.U (fun t => panGaugeU (Real.exp (-(Q.exposure t - P.exposure t)))
      (P.D t) (P.R t) (P.U t)) (Ici 0) := by
  let z : ℝ → ℝ := fun t => Real.exp (-(Q.exposure t - P.exposure t))
  have hzac (T : ℝ) : AbsolutelyContinuousOnInterval z 0 T :=
    ac_exp ((Q.exposure_ac 0 T).fun_sub (P.exposure_ac 0 T)).fun_neg
  have honeac (T : ℝ) : AbsolutelyContinuousOnInterval (fun t => 1 - z t) 0 T :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.fun_sub
      (hzac T)
  have hdac (T : ℝ) (hT : 0 ≤ T) :
      AbsolutelyContinuousOnInterval (fun t => panGaugeD (z t) (P.D t)) 0 T := by
    simpa only [panGaugeD, pow_two] using ((hzac T).fun_mul (hzac T)).fun_mul (P.D_ac T hT)
  have hrac (T : ℝ) (hT : 0 ≤ T) :
      AbsolutelyContinuousOnInterval (fun t => panGaugeR (z t) (P.D t) (P.R t)) 0 T := by
    exact ((hzac T).fun_mul (P.R_ac T hT)).fun_add
      ((((hzac T).const_mul 2).fun_mul (honeac T)).fun_mul (P.D_ac T hT))
  have huac (T : ℝ) (hT : 0 ≤ T) :
      AbsolutelyContinuousOnInterval (fun t => panGaugeU (z t) (P.D t) (P.R t) (P.U t))
        0 T := by
    simpa only [panGaugeU, pow_two] using
      ((P.U_ac T hT).fun_add ((honeac T).fun_mul (P.R_ac T hT))).fun_add
        (((honeac T).fun_mul (honeac T)).fun_mul (P.D_ac T hT))
  have he : IntegrablePanPreEquations rate' Q.recomb
      (fun t => panGaugeD (z t) (P.D t))
      (fun t => panGaugeR (z t) (P.D t) (P.R t))
      (fun t => panGaugeU (z t) (P.D t) (P.R t) (P.U t)) := by
    filter_upwards [P.equations.congr_rates hrate (ae_of_all _ (fun _ _ => rfl)),
      P.rate_nonneg, hx, hrate,
      integrablePanClock_ae_hasDerivAt P.recomb_integrable,
      integrablePanClock_ae_hasDerivAt Q.recomb_integrable] with t ht hrt hxt hratet hp hq ht0
    have hz : HasDerivAt z (-(Q.recomb t - P.recomb t) * z t) t := by
      exact exponential_clock_derivative (fun t => Q.exposure t - P.exposure t) _ t
        ((hq ht0).sub (hp ht0))
    have hd : HasDerivAt P.D (-(rate' t + 2 * P.recomb t) * P.D t + rate' t * P.R t) t := by
      convert (ht ht0).1 using 1
      ring
    have hc : rate' t = 0 ∨ z t = 1 := by
      rw [← hratet ht0]
      by_cases hzero : rate t = 0
      · exact Or.inl hzero
      · right
        have hpos : 0 < rate t := lt_of_le_of_ne (hrt ht0) (Ne.symm hzero)
        simp only [z, hxt ht0 hpos, sub_self, neg_zero, Real.exp_zero]
    have hg := panGauge_derivatives rate' P.recomb Q.recomb z P.D P.R P.U t hz hd
      (ht ht0).2.1 (ht ht0).2.2 hc
    refine ⟨?_, hg.2⟩
    convert hg.1 using 1
    ring
  apply integrablePanPreEquations_unique rate' Q.recomb Q.D Q.R Q.U _ _ _
    Q.rate_integrable Q.recomb_integrable Q.rate_nonneg Q.recomb_nonneg
    Q.D_ac Q.R_ac Q.U_ac hdac hrac huac Q.equations he
  simp [z, panGaugeD, panGaugeR, panGaugeU, P.initial, Q.initial]

theorem integrablePanPreModel_gauge_states (rate : ℝ → ℝ)
    (P Q : IntegrablePanPreModel rate)
    (hx : ∀ᵐ t, 0 ≤ t → 0 < rate t → P.exposure t = Q.exposure t) :
    EqOn Q.D (fun t => panGaugeD (Real.exp (-(Q.exposure t - P.exposure t)))
      (P.D t)) (Ici 0) ∧
    EqOn Q.R (fun t => panGaugeR (Real.exp (-(Q.exposure t - P.exposure t)))
      (P.D t) (P.R t)) (Ici 0) ∧
    EqOn Q.U (fun t => panGaugeU (Real.exp (-(Q.exposure t - P.exposure t)))
      (P.D t) (P.R t) (P.U t)) (Ici 0) :=
  integrablePanPreModel_gauge_states_ae P Q (ae_of_all _ (fun _ _ => rfl)) hx

theorem integrablePanPreModel_gauge_fluxes_ae {rate rate' : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hrate : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hx : ∀ᵐ t, 0 ≤ t → 0 < rate t → P.exposure t = Q.exposure t) :
    (∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t) ∧
    (∀ᵐ t, 0 ≤ t → rate t * P.nonDiagonal t = rate' t * Q.nonDiagonal t) := by
  obtain ⟨hd, hr, hu⟩ := integrablePanPreModel_gauge_states_ae P Q hrate hx
  have hflux : ∀ᵐ t, 0 ≤ t →
      P.diagonalDensity t = Q.diagonalDensity t ∧
      rate t * P.nonDiagonal t = rate' t * Q.nonDiagonal t := by
    filter_upwards [hx, P.rate_nonneg, hrate] with t hxt hrt hratet ht
    by_cases hzero : rate t = 0
    · simp [IntegrablePanPreModel.diagonalDensity, ← hratet ht, hzero]
    · have hpos : 0 < rate t := lt_of_le_of_ne (hrt ht) (Ne.symm hzero)
      constructor
      · change rate t * P.D t = rate' t * Q.D t
        rw [hd ht, ← hratet ht]
        simp [hxt ht hpos, panGaugeD]
      · change rate t * (P.R t + P.U t) = rate' t * (Q.R t + Q.U t)
        rw [hr ht, hu ht, ← hratet ht]
        simp [hxt ht hpos, panGaugeR, panGaugeU]
  exact ⟨hflux.mono (fun _ h ht => (h ht).1), hflux.mono (fun _ h ht => (h ht).2)⟩

end Rhone.Statistics.Identifiability
