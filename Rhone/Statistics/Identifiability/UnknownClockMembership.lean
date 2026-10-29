/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ClockReparameterization
public import Rhone.Statistics.Identifiability.PanMembership

/-! # Membership against every continuous proper panmictic size history -/

@[expose] public section

open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

structure ProperPanModel where
  rate : ℝ → ℝ
  clock : ℝ → ℝ
  rate_continuous : Continuous rate
  clock_continuous : Continuous clock
  rate_nonneg : ∀ t, 0 ≤ t → 0 ≤ rate t
  clock_derivative : ∀ t, 0 ≤ t → HasDerivAt clock (rate t) t
  clock_diverges : Tendsto clock atTop atTop
  pre : PanPreModel rate

noncomputable def ProperPanModel.law (P : ProperPanModel) : Measure (ℝ × ℝ) := P.pre.law P.clock

theorem ProperPanModel.law_probability (P : ProperPanModel) : IsProbabilityMeasure P.law :=
  P.pre.law_probability P.clock P.rate_continuous P.clock_continuous P.rate_nonneg
    P.clock_derivative P.clock_diverges

theorem ProperPanModel.law_map_fst (P : ProperPanModel) :
    P.law.map Prod.fst = conditionalPairLaw P.rate P.clock 0 :=
  P.pre.law_map_fst P.clock P.rate_continuous P.clock_continuous P.rate_nonneg
    P.clock_derivative P.clock_diverges

theorem proper_pan_laws_identify_clock (P Q : ProperPanModel) (he : P.law = Q.law) :
    EqOn (fun t => P.clock 0-P.clock t) (fun t => Q.clock 0-Q.clock t) (Ici 0) ∧
      EqOn P.rate Q.rate (Ici 0) := by
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [P.law_map_fst,Q.law_map_fst] at hm
  exact conditionalPairLaw_identifies_clock P.rate Q.rate P.clock Q.clock
    P.rate_continuous Q.rate_continuous P.clock_continuous Q.clock_continuous
    P.rate_nonneg Q.rate_nonneg P.clock_derivative Q.clock_derivative hm

theorem unknown_clock_membership_iff (rate H D Ddot N Ndot : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H)
    (hD : Continuous D) (hd : Continuous Ddot) (hN : Continuous N) (hn : Continuous Ndot)
    (hrpos : ∀ t, 0 < t → 0 < rate t) (hDpos : ∀ t, 0 ≤ t → 0 < D t)
    (hNpos : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hinit : D 0 = 1 ∧ N 0 = 0)
    (hDderiv : ∀ t, 0 ≤ t → HasDerivAt D (Ddot t) t)
    (hNderiv : ∀ t, 0 ≤ t → HasDerivAt N (Ndot t) t)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop)
    (hObserved : (clockJointLaw rate H D N).map Prod.fst = conditionalPairLaw rate H 0) :
    (∃ P : ProperPanModel, P.law = clockJointLaw rate H D N) ↔
    ∃ R : ℝ → ℝ, Continuous R ∧ R 0 = 0 ∧
      (∀ t, 0 ≤ t → 0 ≤ R t ∧ R t ≤ N t) ∧
      PanScalarEquations rate D Ddot N R ∧
      (∀ t, 0 ≤ t → Ddot t ≤ rate t*(R t-D t)) := by
  have hf := pan_clock_law_membership_iff rate H D Ddot N Ndot hr hH hD hd hN hn
    hrpos hDpos hNpos hinit hDderiv hNderiv
  constructor
  · rintro ⟨P,hp⟩
    have he : conditionalPairLaw P.rate P.clock 0 = conditionalPairLaw rate H 0 := by
      rw [← P.law_map_fst,hp,hObserved]
    have hid := conditionalPairLaw_identifies_clock P.rate rate P.clock H
      P.rate_continuous hr P.clock_continuous hH P.rate_nonneg
      (rate_nonneg_of_positive_time rate hr hrpos) P.clock_derivative hclock he
    apply hf.mp
    refine ⟨P.pre.changeRate rate hid.2,?_⟩
    rw [P.pre.changeRate_law rate P.clock H hid.2 hid.1]
    exact hp
  · intro hs
    obtain ⟨P,hp⟩ := hf.mpr hs
    let M : ProperPanModel :=
      { rate := rate
        clock := H
        rate_continuous := hr
        clock_continuous := hH
        rate_nonneg := rate_nonneg_of_positive_time rate hr hrpos
        clock_derivative := hclock
        clock_diverges := htail
        pre := P }
    refine ⟨M,?_⟩
    exact hp

end Rhone.Statistics.Identifiability
