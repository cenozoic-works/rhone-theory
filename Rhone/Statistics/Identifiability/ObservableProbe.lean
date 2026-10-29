/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ClockReparameterization

/-! # The diagonal and one off-diagonal probe identify observable pre-merger masses -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem clockJointLaw_congr_masses (rate H D₁ D₂ N₁ N₂ : ℝ → ℝ)
    (hd : EqOn D₁ D₂ (Ioi 0)) (hn : EqOn N₁ N₂ (Ioi 0)) :
    clockJointLaw rate H D₁ N₁ = clockJointLaw rate H D₂ N₂ := by
  apply regularJointLaw_congr_on_support
  · intro t ht
    change rate t*D₁ t = rate t * D₂ t
    rw [hd ht]
  · intro p hp
    change rate p.1*N₁ p.1*rate p.2*Real.exp (H p.1-H p.2) = _
    rw [hn hp.1]

theorem clockJointLaw_probe_identifies_masses
    (rate H D₁ D₂ N₁ N₂ δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H)
    (hD₁ : Continuous D₁) (hN₁ : Continuous N₁) (hδ : Continuous δ) (hj : Continuous j)
    (hp : ∀ t ∈ Ioi (0 : ℝ), 0 < rate t)
    (hd₁ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ D₁ t) (hn₁ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ N₁ t)
    (hδn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ δ t) (hjn : ∀ p ∈ upperWedge, 0 ≤ j p)
    (hdiag : ∀ t ∈ Ioi (0 : ℝ), δ t = rate t * D₂ t)
    (hprobe : ∀ t ∈ Ioi (0 : ℝ),
      j (t, t + 1) = rate t * N₂ t * rate (t + 1) * Real.exp (H t - H (t + 1)))
    (he : clockJointLaw rate H D₁ N₁ = regularJointLaw δ j) :
    EqOn D₁ D₂ (Ioi 0) ∧ EqOn N₁ N₂ (Ioi 0) := by
  have hd := regularJointLaw_identifies_diagonal (hr.mul hD₁) hδ
    (fun t ht => mul_nonneg (hp t ht).le (hd₁ t ht)) hδn he
  have hjc : Continuous (fun p : ℝ × ℝ =>
      rate p.1*N₁ p.1*rate p.2*Real.exp (H p.1-H p.2)) :=
    (((hr.comp continuous_fst).mul (hN₁.comp continuous_fst)).mul (hr.comp continuous_snd)).mul
      (Real.continuous_exp.comp ((hH.comp continuous_fst).sub (hH.comp continuous_snd)))
  have hh := regularJointLaw_identifies_upper hjc hj
    (fun p h => mul_nonneg
      (mul_nonneg (mul_nonneg (hp p.1 h.1).le (hn₁ p.1 h.1))
        (hp p.2 (lt_trans h.1 h.2)).le) (Real.exp_pos _).le) hjn he
  constructor
  · intro t ht
    apply mul_left_cancel₀ (hp t ht).ne'
    exact (hd ht).trans (hdiag t ht)
  · intro t ht
    have htp : t+1 ∈ Ioi (0 : ℝ) := by
      change 0 < t+1
      have ht0 : 0 < t := ht
      linarith
    have heq := (hh (show (t,t+1) ∈ upperWedge from ⟨ht,by linarith⟩)).trans (hprobe t ht)
    apply mul_left_cancel₀ (hp t ht).ne'
    apply mul_right_cancel₀ (hp (t+1) htp).ne'
    apply mul_right_cancel₀ (Real.exp_pos (H t-H (t+1))).ne'
    exact heq

end Rhone.Statistics.Identifiability
