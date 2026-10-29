/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanMassPositivity
public import Rhone.Statistics.Identifiability.UnknownClockMembership

/-! # Positivity of the pan ODE pre-equations -/

@[expose] public section

open Set Filter
namespace Rhone.Statistics.Identifiability

theorem panAllNegativeMassEnergy_bound (rate recomb d r u : ℝ)
    (hr : 0 ≤ rate) (hρ : 0 ≤ recomb) :
    2 * min d 0 * (-(rate + 2 * recomb) * d + rate * r) +
    2 * min r 0 * (2 * recomb * d - (3 * rate + recomb) * r + 4 * rate * u) +
    2 * min u 0 * (recomb * r - 6 * rate * u) ≤
      (5 * rate + 3 * recomb) * ((min d 0)^2 + (min r 0)^2 + (min u 0)^2) := by
  have hd := pan_min_zero_mul_self d
  have hr' := pan_min_zero_mul_self r
  have hu := pan_min_zero_mul_self u
  have hcross₁ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonpos_left (min_le_left r 0) (min_le_right d 0))
    (show 0 ≤ 2 * rate by positivity)
  have hcross₂ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonpos_left (min_le_left d 0) (min_le_right r 0))
    (show 0 ≤ 4 * recomb by positivity)
  have hcross₃ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonpos_left (min_le_left u 0) (min_le_right r 0))
    (show 0 ≤ 8 * rate by positivity)
  have hcross₄ := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonpos_left (min_le_left r 0) (min_le_right u 0))
    (show 0 ≤ 2 * recomb by positivity)
  have hdg := congrArg (fun z => 2 * (rate + 2 * recomb) * z) hd
  have hrg := congrArg (fun z => 2 * (3 * rate + recomb) * z) hr'
  have hug := congrArg (fun z => 12 * rate * z) hu
  have hc₁ := mul_nonneg (show 0 ≤ rate + 2 * recomb by positivity)
    (sq_nonneg (min d 0 - min r 0))
  have hc₂ := mul_nonneg (show 0 ≤ 4 * rate + recomb by positivity)
    (sq_nonneg (min r 0 - min u 0))
  have hD := mul_nonneg (show 0 ≤ 6 * rate + 5 * recomb by positivity) (sq_nonneg (min d 0))
  have hR := mul_nonneg (show 0 ≤ 6 * rate + 2 * recomb by positivity) (sq_nonneg (min r 0))
  have hU := mul_nonneg (show 0 ≤ 13 * rate + 2 * recomb by positivity) (sq_nonneg (min u 0))
  nlinarith only [hcross₁, hcross₂, hcross₃, hcross₄, hdg, hrg, hug, hc₁, hc₂, hD, hR, hU]

theorem panPreEquations_all_nonneg (rate recomb D R U : ℝ → ℝ)
    (hrc : Continuous rate) (hρc : Continuous recomb)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (he : PanPreEquations rate recomb D R U)
    (hD₀ : 0 ≤ D 0) (hR₀ : 0 ≤ R 0) (hU₀ : 0 ≤ U 0) :
    ∀ t, 0 ≤ t → 0 ≤ D t ∧ 0 ≤ R t ∧ 0 ≤ U t := by
  let E : ℝ → ℝ := fun t => (min (D t) 0)^2 + (min (R t) 0)^2 + (min (U t) 0)^2
  let Edot : ℝ → ℝ := fun t =>
    2 * min (D t) 0 * (-(rate t + 2 * recomb t) * D t + rate t * R t) +
    2 * min (R t) 0 * (2 * recomb t * D t - (3 * rate t + recomb t) * R t + 4 * rate t * U t) +
    2 * min (U t) 0 * (recomb t * R t - 6 * rate t * U t)
  let C : ℝ → ℝ := fun t => 5 * rate t + 3 * recomb t
  let H : ℝ → ℝ := fun t => -(∫ s in (0 : ℝ)..t, C s)
  have hCc : Continuous C := by dsimp [C]; fun_prop
  have hE : ∀ t, 0 ≤ t → HasDerivAt E (Edot t) t := by
    intro t ht
    exact (((hasDerivAt_sq_min_zero (D t)).comp t (he t ht).1).add
      ((hasDerivAt_sq_min_zero (R t)).comp t (he t ht).2.1)).add
      ((hasDerivAt_sq_min_zero (U t)).comp t (he t ht).2.2)
  have hH : ∀ t, 0 ≤ t → HasDerivAt H (-C t) t := by
    intro t _
    exact (intervalIntegral.integral_hasDerivAt_right (hCc.intervalIntegrable 0 t)
      hCc.aestronglyMeasurable.stronglyMeasurableAtFilter hCc.continuousAt).neg
  have hbound : ∀ t, 0 ≤ t → Edot t ≤ -(-C t) * E t := by
    intro t ht
    simpa only [C, neg_neg] using panAllNegativeMassEnergy_bound
      (rate t) (recomb t) (D t) (R t) (U t) (hr t ht) (hρ t ht)
  have hzero : E 0 = 0 := by simp [E, min_eq_right hD₀, min_eq_right hR₀, min_eq_right hU₀]
  intro t ht
  have hle := clock_decay_bound E Edot H (fun t => -C t) hE hH hbound ht
  rw [hzero, zero_mul] at hle
  change (min (D t) 0)^2 + (min (R t) 0)^2 + (min (U t) 0)^2 ≤ 0 at hle
  have hd : min (D t) 0 = 0 := by nlinarith [sq_nonneg (min (R t) 0), sq_nonneg (min (U t) 0)]
  have hr : min (R t) 0 = 0 := by nlinarith [sq_nonneg (min (D t) 0), sq_nonneg (min (U t) 0)]
  have hu : min (U t) 0 = 0 := by nlinarith [sq_nonneg (min (D t) 0), sq_nonneg (min (R t) 0)]
  exact ⟨by simpa only [hd] using min_le_left (D t) 0,
    by simpa only [hr] using min_le_left (R t) 0,
    by simpa only [hu] using min_le_left (U t) 0⟩

theorem panPreEquations_D_positive (rate recomb D R U : ℝ → ℝ)
    (hrc : Continuous rate) (hρc : Continuous recomb)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (he : PanPreEquations rate recomb D R U)
    (hD₀ : 0 < D 0) (hR₀ : 0 ≤ R 0) (hU₀ : 0 ≤ U 0) :
    ∀ t, 0 ≤ t → 0 < D t := by
  have hn := panPreEquations_all_nonneg rate recomb D R U hrc hρc hr hρ he hD₀.le hR₀ hU₀
  let C : ℝ → ℝ := fun t => rate t + 2 * recomb t
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, C s
  have hCc : Continuous C := by dsimp [C]; fun_prop
  have hH : ∀ t, 0 ≤ t → HasDerivAt H (C t) t := by
    intro t _
    exact intervalIntegral.integral_hasDerivAt_right (hCc.intervalIntegrable 0 t)
      hCc.aestronglyMeasurable.stronglyMeasurableAtFilter hCc.continuousAt
  have hb : ∀ t, 0 ≤ t →
      -(-(rate t + 2 * recomb t) * D t + rate t * R t) ≤ -C t * (-D t) := by
    intro t ht
    dsimp [C]
    nlinarith [mul_nonneg (hr t ht) (hn t ht).2.1]
  intro t ht
  have h := clock_decay_bound (fun t => -D t)
    (fun t => -(-(rate t + 2 * recomb t) * D t + rate t * R t)) H C
    (fun t ht => (he t ht).1.neg) hH hb ht
  have hp := mul_pos hD₀ (Real.exp_pos (H 0 - H t))
  nlinarith

noncomputable def panPreModelOfSolution (rate recomb D R U : ℝ → ℝ)
    (hrc : Continuous rate) (hρc : Continuous recomb)
    (hDc : Continuous D) (hRc : Continuous R) (hUc : Continuous U)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (he : PanPreEquations rate recomb D R U)
    (hi : D 0 = 1 ∧ R 0 = 0 ∧ U 0 = 0) : PanPreModel rate where
  recomb := recomb
  D := D
  R := R
  U := U
  recomb_continuous := hρc
  D_continuous := hDc
  R_continuous := hRc
  U_continuous := hUc
  recomb_nonneg := hρ
  D_positive := panPreEquations_D_positive rate recomb D R U hrc hρc hr hρ he
    (by simp [hi.1]) (by simp [hi.2.1]) (by simp [hi.2.2])
  R_nonneg := fun t ht => (panPreEquations_all_nonneg rate recomb D R U hrc hρc hr hρ he
    (by simp [hi.1]) (by simp [hi.2.1]) (by simp [hi.2.2]) t ht).2.1
  U_nonneg := fun t ht => (panPreEquations_all_nonneg rate recomb D R U hrc hρc hr hρ he
    (by simp [hi.1]) (by simp [hi.2.1]) (by simp [hi.2.2]) t ht).2.2
  initial := hi
  equations := he

end Rhone.Statistics.Identifiability
