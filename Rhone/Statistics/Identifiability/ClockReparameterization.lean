/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairClockIdentification

/-! # Changing only irrelevant negative-time extensions or clock offsets preserves the law -/

@[expose] public section

open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem regularJointLaw_congr_on_support {δ₁ δ₂ : ℝ → ℝ} {j₁ j₂ : ℝ × ℝ → ℝ}
    (hd : EqOn δ₁ δ₂ (Ioi 0)) (hj : EqOn j₁ j₂ upperWedge) :
    regularJointLaw δ₁ j₁ = regularJointLaw δ₂ j₂ := by
  have hd' : diagonalDensityLaw δ₁ = diagonalDensityLaw δ₂ := by
    unfold diagonalDensityLaw
    congr 1
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hd ht]
  have hj' : triangularDensityLaw j₁ = triangularDensityLaw j₂ := by
    unfold triangularDensityLaw
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
    rw [hj hp]
  rw [regularJointLaw,regularJointLaw,hd',hj']

theorem clockJointLaw_congr_clocks (rate₁ rate₂ H₁ H₂ D N : ℝ → ℝ)
    (hr : EqOn rate₁ rate₂ (Ici 0))
    (hH : EqOn (fun t => H₁ 0 - H₁ t) (fun t => H₂ 0 - H₂ t) (Ici 0)) :
    clockJointLaw rate₁ H₁ D N = clockJointLaw rate₂ H₂ D N := by
  apply regularJointLaw_congr_on_support
  · intro t ht
    change rate₁ t*D t = rate₂ t*D t
    have ht0 : t ∈ Ici (0 : ℝ) := by
      change 0 ≤ t
      change 0 < t at ht
      exact ht.le
    rw [hr ht0]
  · intro p hp
    have hs : H₁ 0-H₁ p.1 = H₂ 0-H₂ p.1 := hH hp.1.le
    have ht : H₁ 0-H₁ p.2 = H₂ 0-H₂ p.2 := hH (le_of_lt (lt_trans hp.1 hp.2))
    have he : H₁ p.1-H₁ p.2 = H₂ p.1-H₂ p.2 := by linarith
    change rate₁ p.1*N p.1*rate₁ p.2*Real.exp (H₁ p.1-H₁ p.2) = _
    rw [hr hp.1.le,hr (le_of_lt (lt_trans hp.1 hp.2)),he]

def PanPreModel.changeRate {rate₁ : ℝ → ℝ} (P : PanPreModel rate₁) (rate₂ : ℝ → ℝ)
    (hr : EqOn rate₁ rate₂ (Ici 0)) : PanPreModel rate₂ where
  recomb := P.recomb
  D := P.D
  R := P.R
  U := P.U
  recomb_continuous := P.recomb_continuous
  D_continuous := P.D_continuous
  R_continuous := P.R_continuous
  U_continuous := P.U_continuous
  recomb_nonneg := P.recomb_nonneg
  D_positive := P.D_positive
  R_nonneg := P.R_nonneg
  U_nonneg := P.U_nonneg
  initial := P.initial
  equations := by
    intro t ht
    rw [← hr ht]
    exact P.equations t ht

theorem PanPreModel.changeRate_law {rate₁ : ℝ → ℝ} (P : PanPreModel rate₁)
    (rate₂ H₁ H₂ : ℝ → ℝ) (hr : EqOn rate₁ rate₂ (Ici 0))
    (hH : EqOn (fun t => H₁ 0 - H₁ t) (fun t => H₂ 0 - H₂ t) (Ici 0)) :
    (P.changeRate rate₂ hr).law H₂ = P.law H₁ :=
  (clockJointLaw_congr_clocks rate₁ rate₂ H₁ H₂ P.D (fun t => P.R t+P.U t) hr hH).symm

theorem PanPreModel.law_map_fst {rate : ℝ → ℝ} (P : PanPreModel rate) (H : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t) (htail : Tendsto H atTop atTop) :
    (P.law H).map Prod.fst = conditionalPairLaw rate H 0 := by
  apply clockJointLaw_map_fst rate H P.D (fun t => P.R t+P.U t)
    hr hH P.D_continuous (P.R_continuous.add P.U_continuous) hrn
    (fun t ht => (P.D_positive t ht).le)
    (fun t ht => add_nonneg (P.R_nonneg t ht) (P.U_nonneg t ht))
    (by simp [P.initial]) hclock htail
  exact fun t ht => P.total_derivative ht

end Rhone.Statistics.Identifiability
