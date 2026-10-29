/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ScalarPanModel

/-! # A measure-level scalar membership theorem at a specified positive pair clock -/

@[expose] public section

open Set MeasureTheory Filter
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem pan_clock_law_membership_iff (rate H D Ddot N Ndot : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H)
    (hD : Continuous D) (hd : Continuous Ddot) (hN : Continuous N) (hn : Continuous Ndot)
    (hrpos : ∀ t, 0 < t → 0 < rate t) (hDpos : ∀ t, 0 ≤ t → 0 < D t)
    (hNpos : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hinit : D 0 = 1 ∧ N 0 = 0)
    (hDderiv : ∀ t, 0 ≤ t → HasDerivAt D (Ddot t) t)
    (hNderiv : ∀ t, 0 ≤ t → HasDerivAt N (Ndot t) t) :
    (∃ P : PanPreModel rate, P.law H = clockJointLaw rate H D N) ↔
    ∃ R : ℝ → ℝ, Continuous R ∧ R 0 = 0 ∧
      (∀ t, 0 ≤ t → 0 ≤ R t ∧ R t ≤ N t) ∧
      PanScalarEquations rate D Ddot N R ∧
      (∀ t, 0 ≤ t → Ddot t ≤ rate t*(R t-D t)) := by
  constructor
  · rintro ⟨P,hmatch⟩
    have hid := clockJointLaw_identifies_masses rate H P.D D (fun t => P.R t+P.U t) N
      hr hH P.D_continuous hD (P.R_continuous.add P.U_continuous) hN
      (fun t ht => hrpos t ht)
      (fun t ht => (P.D_positive t ht.le).le) (fun t ht => (hDpos t ht.le).le)
      (fun t ht => add_nonneg (P.R_nonneg t ht.le) (P.U_nonneg t ht.le))
      (fun t ht => hNpos t ht.le) hmatch
    have heD := eqOn_closed_halfline P.D_continuous hD hid.1
    have heN := eqOn_closed_halfline (P.R_continuous.add P.U_continuous) hN hid.2
    let df : ℝ → ℝ := fun t => -(rate t+2*P.recomb t)*P.D t+rate t*P.R t
    let rf : ℝ → ℝ := fun t =>
      2*P.recomb t*P.D t-(3*rate t+P.recomb t)*P.R t+4*rate t*P.U t
    let uf : ℝ → ℝ := fun t => P.recomb t*P.R t-6*rate t*P.U t
    have hpc := P.recomb_continuous
    have hpd := P.D_continuous
    have hpr := P.R_continuous
    have hpu := P.U_continuous
    have hdf : Continuous df := by dsimp [df]; fun_prop
    have hnf : Continuous (fun t => rf t+uf t) := by dsimp [rf,uf]; fun_prop
    have hed : EqOn Ddot df (Ici 0) := eqOn_halfline_derivatives hd hdf hDderiv
      (fun t ht => (P.equations t ht).1) (fun t ht => (hid.1 ht).symm)
    have hen : EqOn Ndot (fun t => rf t+uf t) (Ici 0) := by
      apply eqOn_halfline_derivatives hn hnf hNderiv
      · intro t ht
        exact (P.equations t ht).2.1.add (P.equations t ht).2.2
      · intro t ht
        exact (hid.2 ht).symm
    have halg : ∀ t, 0 ≤ t →
        P.recomb t = reconstructedRecomb (rate t) (D t) (Ddot t) (P.R t) ∧
        Ddot t+Ndot t = -rate t*(D t+2*N t) ∧
        rf t = panRiccatiDrift (rate t) (D t) (Ddot t) (N t) (P.R t) := by
      intro t ht
      have hu : P.U t = N t-P.R t := by
        have hh : P.R t+P.U t = N t := heN ht
        linarith
      apply (pan_forward_scalar_reconstruction (rate t) (P.recomb t) (D t) (P.R t)
        (N t) (Ddot t) (rf t) (Ndot t) (hDpos t ht).ne').mp
      refine ⟨?_,?_,?_⟩
      · rw [hed ht]
        dsimp [df]
        rw [heD ht]
      · dsimp [rf]
        rw [heD ht,hu]
      · rw [hen ht]
        dsimp [uf]
        rw [hu]
        ring
    refine ⟨P.R,P.R_continuous,P.initial.2.1,?_,?_,?_⟩
    · intro t ht
      have hh : P.R t+P.U t = N t := heN ht
      exact ⟨P.R_nonneg t ht,by linarith [P.U_nonneg t ht]⟩
    · intro t ht
      refine ⟨hDderiv t ht,?_,?_⟩
      · convert! hNderiv t ht using 1
        linarith [(halg t ht).2.1]
      · rw [← (halg t ht).2.2]
        exact (P.equations t ht).2.1
    · intro t ht
      apply (reconstructedRecomb_nonneg_iff (hDpos t ht)).mp
      rw [← (halg t ht).1]
      exact P.recomb_nonneg t ht
  · rintro ⟨R,hR,hRzero,hbounds,he,hi⟩
    refine ⟨scalarPanModel rate D Ddot N R hr hD hd hN hR hDpos
      (fun t ht => (hbounds t ht).1) (fun t ht => (hbounds t ht).2)
      ⟨hinit.1,hinit.2,hRzero⟩ he hi,?_⟩
    exact scalarPanModel_law rate D Ddot N R H hr hD hd hN hR hDpos
      (fun t ht => (hbounds t ht).1) (fun t ht => (hbounds t ht).2)
      ⟨hinit.1,hinit.2,hRzero⟩ he hi

theorem pan_probability_law_membership_iff (rate H D Ddot N Ndot : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H)
    (hD : Continuous D) (hd : Continuous Ddot) (hN : Continuous N) (hn : Continuous Ndot)
    (hrpos : ∀ t, 0 < t → 0 < rate t) (hDpos : ∀ t, 0 ≤ t → 0 < D t)
    (hNpos : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hinit : D 0 = 1 ∧ N 0 = 0)
    (hDderiv : ∀ t, 0 ≤ t → HasDerivAt D (Ddot t) t)
    (hNderiv : ∀ t, 0 ≤ t → HasDerivAt N (Ndot t) t)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop) :
    (∃ P : PanPreModel rate, IsProbabilityMeasure (P.law H) ∧
      P.law H = clockJointLaw rate H D N) ↔
    ∃ R : ℝ → ℝ, Continuous R ∧ R 0 = 0 ∧
      (∀ t, 0 ≤ t → 0 ≤ R t ∧ R t ≤ N t) ∧
      PanScalarEquations rate D Ddot N R ∧
      (∀ t, 0 ≤ t → Ddot t ≤ rate t*(R t-D t)) := by
  have he := pan_clock_law_membership_iff rate H D Ddot N Ndot hr hH hD hd hN hn
    hrpos hDpos hNpos hinit hDderiv hNderiv
  constructor
  · rintro ⟨P,_,hp⟩
    exact he.mp ⟨P,hp⟩
  · intro hs
    obtain ⟨P,hp⟩ := he.mpr hs
    exact ⟨P,P.law_probability H hr hH (rate_nonneg_of_positive_time rate hr hrpos) hclock htail,hp⟩

end Rhone.Statistics.Identifiability
