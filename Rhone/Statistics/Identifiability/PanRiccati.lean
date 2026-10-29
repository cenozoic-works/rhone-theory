/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanPreGenerator

/-! # Scalar reconstruction of the panmictic pre-merger equations -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

noncomputable def reconstructedRecomb (rate D Ddot R : ℝ) : ℝ :=
  (rate*R-rate*D-Ddot)/(2*D)

noncomputable def panRiccatiDrift (rate D Ddot N R : ℝ) : ℝ :=
  -(6*rate+reconstructedRecomb rate D Ddot R)*R+4*rate*N-rate*D-Ddot

theorem pan_forward_scalar_reconstruction (rate recomb D R N Ddot Rdot Ndot : ℝ)
    (hD : D ≠ 0) :
    (Ddot = -(rate+2*recomb)*D+rate*R ∧
     Rdot = 2*recomb*D-(3*rate+recomb)*R+4*rate*(N-R) ∧
     Ndot-Rdot = recomb*R-6*rate*(N-R)) ↔
    (recomb = reconstructedRecomb rate D Ddot R ∧
     Ddot+Ndot = -rate*(D+2*N) ∧
     Rdot = panRiccatiDrift rate D Ddot N R) := by
  unfold reconstructedRecomb panRiccatiDrift reconstructedRecomb
  constructor
  · rintro ⟨h₀,h₁,h₂⟩
    have hr : recomb = (rate*R-rate*D-Ddot)/(2*D) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) hD)).mpr
      nlinarith
    refine ⟨hr,by nlinarith,?_⟩
    rw [← hr]
    nlinarith
  · rintro ⟨hr,hb,hd⟩
    have hmul := (eq_div_iff (mul_ne_zero (by norm_num) hD)).mp hr
    rw [← hr] at hd
    constructor
    · nlinarith
    constructor <;> nlinarith

theorem panRiccati_polynomial (rate D Ddot N R : ℝ) (hD : D ≠ 0) :
    panRiccatiDrift rate D Ddot N R =
      -(rate/(2*D))*R^2 + ((rate*D+Ddot)/(2*D)-6*rate)*R +
      4*rate*N-rate*D-Ddot := by
  unfold panRiccatiDrift reconstructedRecomb
  field_simp
  ring

theorem panRiccati_difference (rate D Ddot N R₁ R₂ : ℝ) (hD : D ≠ 0) :
    panRiccatiDrift rate D Ddot N R₁-panRiccatiDrift rate D Ddot N R₂ =
      (-(rate/(2*D))*(R₁+R₂)+(rate*D+Ddot)/(2*D)-6*rate)*(R₁-R₂) := by
  rw [panRiccati_polynomial _ _ _ _ _ hD,panRiccati_polynomial _ _ _ _ _ hD]
  ring

theorem reconstructedRecomb_nonneg_iff {rate D Ddot R : ℝ} (hD : 0 < D) :
    0 ≤ reconstructedRecomb rate D Ddot R ↔ Ddot ≤ rate*(R-D) := by
  unfold reconstructedRecomb
  rw [le_div_iff₀ (by positivity : 0 < 2*D)]
  constructor <;> intro h <;> nlinarith

end Rhone.Statistics.Identifiability
