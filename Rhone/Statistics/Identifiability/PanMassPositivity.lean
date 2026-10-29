/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.JoinDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Positivity of pre-merger masses follows from the forward equations -/

@[expose] public section

open Set
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_sq_min_zero (x : ℝ) :
    HasDerivAt (fun y : ℝ => (min y 0) ^ 2) (2 * min x 0) x := by
  have h := joinAt_derivative 0 (fun y : ℝ => y ^ 2) (fun _ => 0)
    (fun y => 2 * y) (fun _ => 0)
    (fun y => by convert! (hasDerivAt_id y).pow 2 using 1; simp)
    (fun y => hasDerivAt_const y 0) (by norm_num) (by norm_num) x
  have hf : joinAt 0 (fun y : ℝ => y ^ 2) (fun _ => 0) =
      fun y => (min y 0) ^ 2 := by
    funext y
    by_cases hy : y ≤ 0
    · simp [joinAt, hy]
    · simp [joinAt, hy, min_eq_right (le_of_not_ge hy)]
  rw [hf] at h
  by_cases hx : x ≤ 0
  · simpa [joinAt, hx, min_eq_left hx] using h
  · simpa [joinAt, hx, min_eq_right (le_of_not_ge hx)] using h

theorem pan_min_zero_mul_self (x : ℝ) : min x 0 * x = (min x 0) ^ 2 := by
  by_cases hx : x ≤ 0
  · simp [min_eq_left hx, pow_two]
  · simp [min_eq_right (le_of_not_ge hx)]

theorem panNegativeMassEnergy_bound (rate recomb d r u : ℝ)
    (hr : 0 ≤ rate) (hρ : 0 ≤ recomb) (hd : 0 ≤ d) :
    2 * min r 0 * (2 * recomb * d - (3 * rate + recomb) * r + 4 * rate * u) +
        2 * min u 0 * (recomb * r - 6 * rate * u) ≤
      (4 * rate + recomb) * ((min r 0) ^ 2 + (min u 0) ^ 2) := by
  have har := pan_min_zero_mul_self r
  have hbu := pan_min_zero_mul_self u
  have hcross₁ : min r 0 * u ≤ min r 0 * min u 0 :=
    mul_le_mul_of_nonpos_left (min_le_left u 0) (min_le_right r 0)
  have hcross₂ : min u 0 * r ≤ min u 0 * min r 0 :=
    mul_le_mul_of_nonpos_left (min_le_left r 0) (min_le_right u 0)
  have hc₁ := mul_le_mul_of_nonneg_left hcross₁ (show 0 ≤ 8 * rate by positivity)
  have hc₂ := mul_le_mul_of_nonneg_left hcross₂ (show 0 ≤ 2 * recomb by positivity)
  have hf : 4 * recomb * d * min r 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (min_le_right r 0)
  have hrdiag : 0 ≤ 2 * (3 * rate + recomb) * (min r 0) ^ 2 := by positivity
  have hudiag : 0 ≤ 12 * rate * (min u 0) ^ 2 := by positivity
  have hcross := mul_nonneg (show 0 ≤ 4 * rate + recomb by positivity)
    (sq_nonneg (min r 0 - min u 0))
  have hdiag₁ := congrArg (fun z => 2 * (3 * rate + recomb) * z) har
  have hdiag₂ := congrArg (fun z => 12 * rate * z) hbu
  nlinarith only [hdiag₁, hdiag₂, hc₁, hc₂, hf, hrdiag, hudiag, hcross]

theorem panPreEquations_R_U_nonneg_of_continuousOn (rate recomb D R U : ℝ → ℝ)
    (hrc : ContinuousOn rate (Ici 0)) (hρc : ContinuousOn recomb (Ici 0))
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (hD : ∀ t, 0 ≤ t → 0 ≤ D t)
    (he : PanPreEquations rate recomb D R U)
    (hR₀ : 0 ≤ R 0) (hU₀ : 0 ≤ U 0) :
    ∀ t, 0 ≤ t → 0 ≤ R t ∧ 0 ≤ U t := by
  let E : ℝ → ℝ := fun t => (min (R t) 0) ^ 2 + (min (U t) 0) ^ 2
  let Edot : ℝ → ℝ := fun t =>
    2 * min (R t) 0 * (2 * recomb t * D t - (3 * rate t + recomb t) * R t +
      4 * rate t * U t) + 2 * min (U t) 0 * (recomb t * R t - 6 * rate t * U t)
  let C : ℝ → ℝ := fun t => 4 * rate (max t 0) + recomb (max t 0)
  let H : ℝ → ℝ := fun t => -(∫ s in (0 : ℝ)..t, C s)
  have hCc : Continuous C := by
    have hm : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
    exact (continuous_const.mul (hrc.comp_continuous hm (fun t => le_max_right t 0))).add
      (hρc.comp_continuous hm (fun t => le_max_right t 0))
  have hE : ∀ t, 0 ≤ t → HasDerivAt E (Edot t) t := by
    intro t ht
    exact ((hasDerivAt_sq_min_zero (R t)).comp t (he t ht).2.1).add
      ((hasDerivAt_sq_min_zero (U t)).comp t (he t ht).2.2)
  have hH : ∀ t, 0 ≤ t → HasDerivAt H (-C t) t := by
    intro t _
    exact (intervalIntegral.integral_hasDerivAt_right (hCc.intervalIntegrable 0 t)
      hCc.aestronglyMeasurable.stronglyMeasurableAtFilter hCc.continuousAt).neg
  have hbound : ∀ t, 0 ≤ t → Edot t ≤ -(-C t) * E t := by
    intro t ht
    simpa only [C, max_eq_left ht, neg_neg] using panNegativeMassEnergy_bound
      (rate t) (recomb t) (D t) (R t) (U t) (hr t ht) (hρ t ht) (hD t ht)
  have hzero : E 0 = 0 := by simp [E, min_eq_right hR₀, min_eq_right hU₀]
  intro t ht
  have hle := clock_decay_bound E Edot H (fun t => -C t) hE hH hbound ht
  rw [hzero, zero_mul] at hle
  change (min (R t) 0) ^ 2 + (min (U t) 0) ^ 2 ≤ 0 at hle
  have hR : min (R t) 0 = 0 := by nlinarith [sq_nonneg (min (U t) 0)]
  have hU : min (U t) 0 = 0 := by nlinarith [sq_nonneg (min (R t) 0)]
  exact ⟨by simpa only [hR] using min_le_left (R t) 0,
    by simpa only [hU] using min_le_left (U t) 0⟩

theorem panPreEquations_R_U_nonneg (rate recomb D R U : ℝ → ℝ)
    (hrc : Continuous rate) (hρc : Continuous recomb)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (hD : ∀ t, 0 ≤ t → 0 ≤ D t)
    (he : PanPreEquations rate recomb D R U)
    (hR₀ : 0 ≤ R 0) (hU₀ : 0 ≤ U 0) :
    ∀ t, 0 ≤ t → 0 ≤ R t ∧ 0 ≤ U t :=
  panPreEquations_R_U_nonneg_of_continuousOn rate recomb D R U
    hrc.continuousOn hρc.continuousOn hr hρ hD he hR₀ hU₀

theorem panPreEquations_initial_nonneg (rate recomb D R U : ℝ → ℝ)
    (hrc : Continuous rate) (hρc : Continuous recomb)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hρ : ∀ t, 0 ≤ t → 0 ≤ recomb t)
    (hD : ∀ t, 0 ≤ t → 0 < D t)
    (he : PanPreEquations rate recomb D R U)
    (hzero : D 0 = 1 ∧ R 0 = 0 ∧ U 0 = 0) :
    ∀ t, 0 ≤ t → 0 ≤ D t ∧ 0 ≤ R t ∧ 0 ≤ U t := by
  have hRU := panPreEquations_R_U_nonneg rate recomb D R U hrc hρc hr hρ
    (fun t ht => (hD t ht).le) he (by simp [hzero.2.1]) (by simp [hzero.2.2])
  exact fun t ht => ⟨(hD t ht).le, hRU t ht⟩

end Rhone.Statistics.Identifiability
