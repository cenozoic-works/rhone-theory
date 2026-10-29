/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanSilentInvariants
public import Rhone.Statistics.Identifiability.ZeroClockDynamics
public import Rhone.Statistics.Identifiability.UnknownClockMembership

/-! # The diagonal restriction of a pan joint law determines the law -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem regularJointLaw_diagonal_restriction_identifies_density
    {δ₁ δ₂ : ℝ → ℝ} {j₁ j₂ : ℝ × ℝ → ℝ}
    (hδ₁ : Continuous δ₁) (hδ₂ : Continuous δ₂)
    (hn₁ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ δ₁ t) (hn₂ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ δ₂ t)
    (he : (regularJointLaw δ₁ j₁).restrict timeDiagonal =
      (regularJointLaw δ₂ j₂).restrict timeDiagonal) : EqOn δ₁ δ₂ (Ioi 0) := by
  rw [regularJointLaw_restrict_diagonal,regularJointLaw_restrict_diagonal] at he
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [diagonalDensityLaw_map_fst,diagonalDensityLaw_map_fst] at hm
  have ha := (withDensity_eq_iff_of_sigmaFinite hδ₁.measurable.ennreal_ofReal.aemeasurable
    hδ₂.measurable.ennreal_ofReal.aemeasurable).mp hm
  have hreal : δ₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] δ₂ := by
    filter_upwards [ha,ae_restrict_mem measurableSet_Ioi] with t ht hpos
    exact (ENNReal.ofReal_eq_ofReal_iff (hn₁ t hpos) (hn₂ t hpos)).mp ht
  exact Measure.eqOn_open_of_ae_eq hreal isOpen_Ioi hδ₁.continuousOn hδ₂.continuousOn

theorem pan_pre_diagonal_identifies_flux (rate H : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : Continuous rate) (hn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (he : (P.law H).restrict timeDiagonal = (Q.law H).restrict timeDiagonal) :
    EqOn (fun t => rate t * P.D t) (fun t => rate t * Q.D t) (Ici 0) := by
  apply eqOn_closed_halfline (hr.mul P.D_continuous) (hr.mul Q.D_continuous)
  exact regularJointLaw_diagonal_restriction_identifies_density
    (hr.mul P.D_continuous) (hr.mul Q.D_continuous)
    (fun t ht => mul_nonneg (hn t ht.le) (P.D_positive t ht.le).le)
    (fun t ht => mul_nonneg (hn t ht.le) (Q.D_positive t ht.le).le) he

theorem pan_diagonal_flux_determines_law (rate H : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (he : EqOn (fun t => rate t * P.D t) (fun t => rate t * Q.D t) (Ici 0)) :
    P.law H = Q.law H := by
  have hG := pan_diagonal_flux_identifies_G rate P Q hr he
  apply clockJointLaw_congr_fluxes
  · intro t ht
    change 0 < t at ht
    have ht0 : 0 ≤ t := ht.le
    exact he ht0
  · intro t ht
    change 0 < t at ht
    have ht0 : 0 ≤ t := ht.le
    have hg := congrArg (fun x => rate t*x) (hG ht0)
    have hd := he ht0
    dsimp only [PanPreModel.G] at hg
    change rate t*(P.R t+P.U t) = rate t*(Q.R t+Q.U t)
    nlinarith only [hg,hd]

theorem pan_pre_law_eq_iff_diagonal (rate H : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : Continuous rate) (hn : ∀ t, 0 ≤ t → 0 ≤ rate t) :
    P.law H = Q.law H ↔
      (P.law H).restrict timeDiagonal = (Q.law H).restrict timeDiagonal := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact pan_diagonal_flux_determines_law rate H P Q hn
      (pan_pre_diagonal_identifies_flux rate H P Q hr hn h)

theorem proper_pan_marginals_identify_clock (P Q : ProperPanModel)
    (he : P.law.map Prod.fst = Q.law.map Prod.fst) :
    EqOn (fun t => P.clock 0-P.clock t) (fun t => Q.clock 0-Q.clock t) (Ici 0) ∧
      EqOn P.rate Q.rate (Ici 0) := by
  rw [P.law_map_fst,Q.law_map_fst] at he
  exact conditionalPairLaw_identifies_clock P.rate Q.rate P.clock Q.clock
    P.rate_continuous Q.rate_continuous P.clock_continuous Q.clock_continuous
    P.rate_nonneg Q.rate_nonneg P.clock_derivative Q.clock_derivative he

theorem proper_pan_joint_law_iff_marginal_and_diagonal (P Q : ProperPanModel) :
    P.law = Q.law ↔ P.law.map Prod.fst = Q.law.map Prod.fst ∧
      P.law.restrict timeDiagonal = Q.law.restrict timeDiagonal := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl,rfl⟩
  · rintro ⟨hm,hd⟩
    have hc := proper_pan_marginals_identify_clock Q P hm.symm
    let Q' := Q.pre.changeRate P.rate hc.2
    have hQ : Q'.law P.clock = Q.law := Q.pre.changeRate_law P.rate Q.clock P.clock hc.2 hc.1
    have hd' : (P.pre.law P.clock).restrict timeDiagonal =
        (Q'.law P.clock).restrict timeDiagonal := by
      rw [hQ]
      exact hd
    have h := (pan_pre_law_eq_iff_diagonal P.rate P.clock P.pre Q'
      P.rate_continuous P.rate_nonneg).mpr hd'
    exact h.trans hQ

end Rhone.Statistics.Identifiability
