/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularDensityIdentification

/-! # At a fixed positive pair clock, the joint law identifies pre-merger observables -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def clockJointLaw (rate H D N : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  regularJointLaw (fun t => rate t*D t)
    (fun p => rate p.1*N p.1*rate p.2*Real.exp (H p.1-H p.2))

theorem clockJointLaw_identifies_masses (rate H D₁ D₂ N₁ N₂ : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H)
    (hD₁ : Continuous D₁) (hD₂ : Continuous D₂)
    (hN₁ : Continuous N₁) (hN₂ : Continuous N₂)
    (hp : ∀ t ∈ Ioi (0 : ℝ), 0 < rate t)
    (hd₁ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ D₁ t) (hd₂ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ D₂ t)
    (hn₁ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ N₁ t) (hn₂ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ N₂ t)
    (he : clockJointLaw rate H D₁ N₁ = clockJointLaw rate H D₂ N₂) :
    EqOn D₁ D₂ (Ioi 0) ∧ EqOn N₁ N₂ (Ioi 0) := by
  have hd := regularJointLaw_identifies_diagonal (hr.mul hD₁) (hr.mul hD₂)
    (fun t ht => mul_nonneg (hp t ht).le (hd₁ t ht))
    (fun t ht => mul_nonneg (hp t ht).le (hd₂ t ht)) he
  have hj := regularJointLaw_identifies_upper
    (((hr.comp continuous_fst).mul (hN₁.comp continuous_fst)).mul (hr.comp continuous_snd) |>.mul
      (Real.continuous_exp.comp ((hH.comp continuous_fst).sub (hH.comp continuous_snd))))
    (((hr.comp continuous_fst).mul (hN₂.comp continuous_fst)).mul (hr.comp continuous_snd) |>.mul
      (Real.continuous_exp.comp ((hH.comp continuous_fst).sub (hH.comp continuous_snd))))
    (fun p h => mul_nonneg
      (mul_nonneg (mul_nonneg (hp p.1 h.1).le (hn₁ p.1 h.1))
        (hp p.2 (lt_trans h.1 h.2)).le) (Real.exp_pos _).le)
    (fun p h => mul_nonneg
      (mul_nonneg (mul_nonneg (hp p.1 h.1).le (hn₂ p.1 h.1))
        (hp p.2 (lt_trans h.1 h.2)).le) (Real.exp_pos _).le) he
  constructor
  · intro t ht
    exact mul_left_cancel₀ (hp t ht).ne' (hd ht)
  · intro t ht
    have hh := hj (show (t,t+1) ∈ upperWedge from ⟨ht,by linarith⟩)
    have htp : t+1 ∈ Ioi (0 : ℝ) := by
      change 0 < t+1
      have ht0 : 0 < t := ht
      linarith
    apply mul_left_cancel₀ (hp t ht).ne'
    apply mul_right_cancel₀ (hp (t+1) htp).ne'
    apply mul_right_cancel₀ (Real.exp_pos (H t-H (t+1))).ne'
    exact hh

end Rhone.Statistics.Identifiability
