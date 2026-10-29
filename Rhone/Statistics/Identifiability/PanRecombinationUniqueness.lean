/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.UnknownClockMembership

/-! # Recombination is identifiable inside the positive-clock panmictic family -/

@[expose] public section

open Set
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem pre_two_solutions_difference (rate r₁ r₂ D R₁ R₂ U₁ U₂ : ℝ)
    (hd : -(rate + 2 * r₁) * D + rate * R₁ = -(rate + 2 * r₂) * D + rate * R₂)
    (hn : R₁ + U₁ = R₂ + U₂) :
    2*D*(r₁-r₂) = rate*(R₁-R₂) ∧
    (2*r₁*D-(3*rate+r₁)*R₁+4*rate*U₁) -
      (2*r₂*D-(3*rate+r₂)*R₂+4*rate*U₂) =
      -(6*rate+r₁)*(R₁-R₂)-R₂*(r₁-r₂) := by
  have hn' := congrArg (fun x => 4*rate*x) hn
  constructor <;> nlinarith

theorem pre_two_solutions_contract (rate r₁ r₂ D R₁ R₂ U₁ U₂ : ℝ)
    (hRate : 0 ≤ rate) (hr : 0 ≤ r₁) (hD : 0 < D) (hR : 0 ≤ R₂)
    (hd : -(rate + 2 * r₁) * D + rate * R₁ = -(rate + 2 * r₂) * D + rate * R₂)
    (hn : R₁ + U₁ = R₂ + U₂) :
    2*(R₁-R₂)*((2*r₁*D-(3*rate+r₁)*R₁+4*rate*U₁) -
      (2*r₂*D-(3*rate+r₂)*R₂+4*rate*U₂)) ≤ 0 := by
  obtain ⟨he,hf⟩ := pre_two_solutions_difference rate r₁ r₂ D R₁ R₂ U₁ U₂ hd hn
  have hcross : 0 ≤ (R₁-R₂)*(r₁-r₂) := by
    have hc : (R₁-R₂)*(r₁-r₂) = rate*(R₁-R₂)^2/(2*D) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) hD.ne')).mpr
      linear_combination (R₁-R₂)*he
    rw [hc]
    positivity
  rw [hf]
  have hs := mul_nonneg (show 0 ≤ 6*rate+r₁ by positivity) (sq_nonneg (R₁-R₂))
  have hc := mul_nonneg hR hcross
  nlinarith

theorem pan_pre_law_identifies_recombination (rate H : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : Continuous rate) (hH : Continuous H) (hpos : ∀ t, 0 < t → 0 < rate t)
    (he : P.law H = Q.law H) :
    EqOn P.R Q.R (Ici 0) ∧ EqOn P.recomb Q.recomb (Ici 0) := by
  have hid := clockJointLaw_identifies_masses rate H P.D Q.D
    (fun t => P.R t+P.U t) (fun t => Q.R t+Q.U t) hr hH P.D_continuous Q.D_continuous
    (P.R_continuous.add P.U_continuous) (Q.R_continuous.add Q.U_continuous)
    (fun t ht => hpos t ht) (fun t ht => (P.D_positive t ht.le).le)
    (fun t ht => (Q.D_positive t ht.le).le)
    (fun t ht => add_nonneg (P.R_nonneg t ht.le) (P.U_nonneg t ht.le))
    (fun t ht => add_nonneg (Q.R_nonneg t ht.le) (Q.U_nonneg t ht.le)) he
  have heD := eqOn_closed_halfline P.D_continuous Q.D_continuous hid.1
  have heN := eqOn_closed_halfline (P.R_continuous.add P.U_continuous)
    (Q.R_continuous.add Q.U_continuous) hid.2
  let dfP : ℝ → ℝ := fun t => -(rate t+2*P.recomb t)*P.D t+rate t*P.R t
  let dfQ : ℝ → ℝ := fun t => -(rate t+2*Q.recomb t)*Q.D t+rate t*Q.R t
  have hpr := P.recomb_continuous
  have hqr := Q.recomb_continuous
  have hpd := P.D_continuous
  have hqd := Q.D_continuous
  have hpR := P.R_continuous
  have hqR := Q.R_continuous
  have hdP : Continuous dfP := by dsimp [dfP]; fun_prop
  have hdQ : Continuous dfQ := by dsimp [dfQ]; fun_prop
  have hedf := eqOn_halfline_derivatives hdP hdQ
    (fun t ht => (P.equations t ht).1) (fun t ht => (Q.equations t ht).1) hid.1
  let diffR : ℝ → ℝ := fun t => P.R t-Q.R t
  let drift : ℝ → ℝ := fun t =>
    (2*P.recomb t*P.D t-(3*rate t+P.recomb t)*P.R t+4*rate t*P.U t) -
    (2*Q.recomb t*Q.D t-(3*rate t+Q.recomb t)*Q.R t+4*rate t*Q.U t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => (diffR x)^2) (2*diffR t*drift t) t := by
    intro t ht
    convert! (((P.equations t ht).2.1).sub (Q.equations t ht).2.1).pow 2 using 1
    dsimp [diffR,drift]
    ring
  have hsign : ∀ t, 0 ≤ t → 2*diffR t*drift t ≤ 0 := by
    intro t ht
    have hd : -(rate t+2*P.recomb t)*P.D t+rate t*P.R t =
        -(rate t+2*Q.recomb t)*P.D t+rate t*Q.R t := by
      have hh := hedf ht
      dsimp [dfP,dfQ] at hh
      rwa [← heD ht] at hh
    have hn : P.R t+P.U t = Q.R t+Q.U t := heN ht
    dsimp [diffR,drift]
    rw [← heD ht]
    exact pre_two_solutions_contract _ _ _ _ _ _ _ _
      (rate_nonneg_of_positive_time rate hr hpos t ht) (P.recomb_nonneg t ht)
      (P.D_positive t ht) (Q.R_nonneg t ht) hd hn
  have ha : AntitoneOn (fun x => (diffR x)^2) (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hsign t (interior_subset ht))
  have hR : EqOn P.R Q.R (Ici 0) := by
    intro t ht
    have hh := ha self_mem_Ici ht ht
    have hz : diffR 0 = 0 := by simp [diffR,P.initial,Q.initial]
    change (diffR t)^2 ≤ (diffR 0)^2 at hh
    rw [hz] at hh
    dsimp [diffR] at hh
    nlinarith
  refine ⟨hR,?_⟩
  intro t ht
  have hh := hedf ht
  dsimp [dfP,dfQ] at hh
  rw [← heD ht,hR ht] at hh
  have hz : (2*P.D t)*(P.recomb t-Q.recomb t) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (by norm_num) (P.D_positive t ht).ne'))

theorem proper_pan_joint_law_identifies_both_rates (P Q : ProperPanModel)
    (hpos : ∀ t, 0 < t → 0 < P.rate t) (he : P.law = Q.law) :
    EqOn P.rate Q.rate (Ici 0) ∧ EqOn P.pre.recomb Q.pre.recomb (Ici 0) := by
  have hc := proper_pan_laws_identify_clock Q P he.symm
  let Q' := Q.pre.changeRate P.rate hc.2
  have hl : P.pre.law P.clock = Q'.law P.clock := by
    rw [Q.pre.changeRate_law P.rate Q.clock P.clock hc.2 hc.1]
    exact he
  have hr := pan_pre_law_identifies_recombination P.rate P.clock P.pre Q'
    P.rate_continuous P.clock_continuous hpos hl
  exact ⟨fun t ht => (hc.2 ht).symm,hr.2⟩

end Rhone.Statistics.Identifiability
