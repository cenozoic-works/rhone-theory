/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingDrift
public import Rhone.Statistics.Identifiability.ThreeSamplingLyapunov
public import Rhone.Statistics.Identifiability.AEPositivePartDerivative

/-! # Rigidity of normalized three-occupancy ODE paths with a proper first-merger clock -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

theorem normalized_trace_rigidity (n : ℝ) (hn : 1 < n) (c q x y H : ℝ → ℝ)
    (hc : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hq : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hx : ∀ t, 0 ≤ t → 0 ≤ x t ∧ x t ≤ 1)
    (hy : ∀ t, 0 ≤ t → y t ≤ 1 ∧ 3 * x t ≤ 1 + 2 * y t)
    (hxac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval x a b)
    (hHac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval H a b)
    (hxd : ∀ᵐ t, 0 ≤ t → HasDerivAt x (xDrift (c t) (q t) n (x t) (y t)) t)
    (hyd : ∀ᵐ t, 0 ≤ t → HasDerivAt y (yDrift (c t) (q t) n (x t) (y t)) t)
    (hHd : ∀ᵐ t, 0 ≤ t → HasDerivAt H (3 * c t * x t) t)
    (htrace : ∀ᵐ t, 0 ≤ t → 0 < c t → y t = (x t) ^ 2)
    (hproper : Tendsto H atTop atTop) :
    (∀ t, 0 ≤ t → x t = 1 ∧ y t = 1) ∧ (∀ᵐ t, 0 ≤ t → q t = 0) := by
  let w := fun t => max (x t - 1 / n) 0
  let wDot := fun t => if 1 / n < x t then xDrift (c t) (q t) n (x t) (y t) else 0
  have hwd := ae_positivePart_derivative x
    (fun t => xDrift (c t) (q t) n (x t) (y t)) (1 / n)
    (fun b hb => hxac 0 b le_rfl hb) hxd
  have hdiss : ∀ᵐ t, 0 ≤ t → wDot t ≤ -(3 * c t * x t) * (1 - x t) := by
    filter_upwards [hc, hq, hxd, hyd, htrace,
      ae_derivative_zero_on_level (fun t => y t - (x t) ^ 2) 0] with
      t hct hqt hxdt hydt htr htzero ht0
    have hlocal : 0 < c t → y t = (x t) ^ 2 ∧
        yDrift (c t) (q t) n (x t) (y t) -
          2 * x t * xDrift (c t) (q t) n (x t) (y t) = 0 := by
      intro hcp
      refine ⟨htr ht0 hcp, ?_⟩
      apply htzero (sub_eq_zero.mpr (htr ht0 hcp))
      exact ((hydt ht0).sub ((hxdt ht0).pow 2)).congr_deriv (by ring)
    have he := positivePart_drift_bound (c t) (q t) n (x t) (y t)
      (hct ht0) (hqt ht0) hn (hx t ht0).1 (hx t ht0).2 hlocal
    dsimp [wDot]
    nlinarith only [he]
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  have hrate : ∀ᵐ t, 0 ≤ t → 0 ≤ 3 * c t * x t := by
    filter_upwards [hc] with t ht ht0
    exact mul_nonneg (mul_nonneg (by norm_num) (ht ht0)) (hx t ht0).1
  have hxone : ∀ t, 0 ≤ t → x t = 1 :=
    proper_clock_forces_one x w wDot H (fun t => 3 * c t * x t) (1 / n)
      ((div_lt_one hn0).mpr hn) (fun t ht => (hx t ht).2) (fun _ _ => rfl)
      (fun a b ha hab => ac_positivePart (hxac a b ha hab) (1 / n))
      hHac hwd hHd hrate hdiss hproper
  have hyone (t : ℝ) (ht : 0 ≤ t) : y t = 1 := by
    have he := hy t ht
    rw [hxone t ht] at he
    linarith
  refine ⟨fun t ht => ⟨hxone t ht, hyone t ht⟩, ?_⟩
  filter_upwards [hxd, ae_derivative_zero_on_level x 1] with t hdt hz ht0
  have he := hz (hxone t ht0) _ (hdt ht0)
  rw [hxone t ht0, hyone t ht0] at he
  have hid : xDrift (c t) (q t) n 1 1 = (-2 * (n - 1)) * q t := by
    unfold xDrift
    ring
  rw [hid] at he
  exact (mul_eq_zero.mp he).resolve_left
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_gt hn)))

end Rhone.Statistics.Identifiability.ThreeSampling
