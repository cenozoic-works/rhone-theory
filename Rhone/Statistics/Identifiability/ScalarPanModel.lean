/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.HalfLineIdentification

/-! # Constructing an admissible panmictic forward model from scalar data -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def realizedRecomb (rate D Ddot R : ℝ → ℝ) (t : ℝ) : ℝ :=
  reconstructedRecomb (rate (max t 0)) (D (max t 0)) (Ddot (max t 0)) (R (max t 0))

theorem realizedRecomb_at_nonneg (rate D Ddot R : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    realizedRecomb rate D Ddot R t = reconstructedRecomb (rate t) (D t) (Ddot t) (R t) := by
  simp only [realizedRecomb,max_eq_left ht]

theorem realizedRecomb_continuous (rate D Ddot R : ℝ → ℝ)
    (hr : Continuous rate) (hD : Continuous D) (hd : Continuous Ddot) (hR : Continuous R)
    (hpos : ∀ t, 0 ≤ t → 0 < D t) : Continuous (realizedRecomb rate D Ddot R) := by
  have hc : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  unfold realizedRecomb reconstructedRecomb
  exact ((((hr.comp hc).mul (hR.comp hc)).sub ((hr.comp hc).mul (hD.comp hc))).sub
    (hd.comp hc)).div (continuous_const.mul (hD.comp hc))
      (fun t => mul_ne_zero (by norm_num) (hpos (max t 0) (le_max_right _ _)).ne')

noncomputable def scalarPanModel (rate D Ddot N R : ℝ → ℝ)
    (hr : Continuous rate) (hD : Continuous D) (hd : Continuous Ddot)
    (hN : Continuous N) (hR : Continuous R)
    (hpos : ∀ t, 0 ≤ t → 0 < D t)
    (hRn : ∀ t, 0 ≤ t → 0 ≤ R t) (hUn : ∀ t, 0 ≤ t → R t ≤ N t)
    (hinit : D 0 = 1 ∧ N 0 = 0 ∧ R 0 = 0)
    (he : PanScalarEquations rate D Ddot N R)
    (hi : ∀ t, 0 ≤ t → Ddot t ≤ rate t * (R t - D t)) : PanPreModel rate where
  recomb := realizedRecomb rate D Ddot R
  D := D
  R := R
  U := fun t => N t-R t
  recomb_continuous := realizedRecomb_continuous rate D Ddot R hr hD hd hR hpos
  D_continuous := hD
  R_continuous := hR
  U_continuous := hN.sub hR
  recomb_nonneg := by
    intro t ht
    rw [realizedRecomb_at_nonneg rate D Ddot R ht]
    exact (reconstructedRecomb_nonneg_iff (hpos t ht)).mpr (hi t ht)
  D_positive := hpos
  R_nonneg := hRn
  U_nonneg := fun t ht => sub_nonneg.mpr (hUn t ht)
  initial := by simp [hinit]
  equations := by
    intro t ht
    have h := scalar_equations_give_pan_forward rate D Ddot N R
      (fun x hx => (hpos x hx).ne') he t ht
    simpa only [realizedRecomb_at_nonneg rate D Ddot R ht] using h

theorem scalarPanModel_law (rate D Ddot N R H : ℝ → ℝ)
    (hr : Continuous rate) (hD : Continuous D) (hd : Continuous Ddot)
    (hN : Continuous N) (hR : Continuous R)
    (hpos : ∀ t, 0 ≤ t → 0 < D t)
    (hRn : ∀ t, 0 ≤ t → 0 ≤ R t) (hUn : ∀ t, 0 ≤ t → R t ≤ N t)
    (hinit : D 0 = 1 ∧ N 0 = 0 ∧ R 0 = 0)
    (he : PanScalarEquations rate D Ddot N R)
    (hi : ∀ t, 0 ≤ t → Ddot t ≤ rate t * (R t - D t)) :
    (scalarPanModel rate D Ddot N R hr hD hd hN hR hpos hRn hUn hinit he hi).law H =
      clockJointLaw rate H D N := by
  unfold PanPreModel.law scalarPanModel
  congr 1
  funext t
  ring

end Rhone.Statistics.Identifiability
