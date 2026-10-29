/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ClockLawProbability
public import Rhone.Statistics.Identifiability.ClockDecay
public import Rhone.Statistics.Identifiability.PanReconstructionODE

/-! # A normalized full panmictic event law from the three-state forward equations -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem clockJointLaw_probability (rate H D N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hD : Continuous D) (hN : Continuous N)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hDn : ∀ t, 0 ≤ t → 0 ≤ D t) (hNn : ∀ t, 0 ≤ t → 0 ≤ N t)
    (hzero : D 0 + N 0 = 1)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop)
    (hbalance : ∀ t, 0 ≤ t →
      HasDerivAt (fun x => D x + N x) (-rate t * (D t + 2 * N t)) t) :
    IsProbabilityMeasure (clockJointLaw rate H D N) := by
  have hg : Tendsto (fun t => D t+N t) atTop (𝓝 0) := by
    apply clock_decay_tendsto_zero (fun t => D t+N t)
      (fun t => -rate t * (D t + 2 * N t)) H rate hbalance hclock
    · intro t ht
      have hn := mul_nonneg (hrn t ht) (hNn t ht)
      nlinarith
    · intro t ht
      exact add_nonneg (hDn t ht) (hNn t ht)
    · exact htail
  have hflux : ∀ t, 0 ≤ t → HasDerivAt (fun x => D x + N x)
      (-(rate t*D t+rate t*N t+rate t*N t)) t := by
    intro t ht
    convert! hbalance t ht using 1
    ring
  have he : clockJointLaw rate H D N = regularJointLaw (fun t => rate t*D t)
      (fun p => (rate p.1*N p.1)*conditionalPairDensity rate H p.1 p.2) := by
    unfold clockJointLaw conditionalPairDensity
    congr 1
    funext p
    ring
  rw [he]
  apply clockEventLaw_probability _ _ rate H (hr.mul hD).measurable (hr.mul hN).measurable
    hr.measurable hH.measurable
    (fun t ht => mul_nonneg (hrn t ht) (hDn t ht))
    (fun t ht => mul_nonneg (hrn t ht) (hNn t ht))
    (fun s hs => conditionalPair_lintegral_one rate H hs hrn hclock htail)
  exact firstFlux_lintegral_one _ _ _ hflux hzero hg
    (fun t ht => mul_nonneg (hrn t ht) (hDn t ht))
    (fun t ht => mul_nonneg (hrn t ht) (hNn t ht))

structure PanPreModel (rate : ℝ → ℝ) where
  recomb : ℝ → ℝ
  D : ℝ → ℝ
  R : ℝ → ℝ
  U : ℝ → ℝ
  recomb_continuous : Continuous recomb
  D_continuous : Continuous D
  R_continuous : Continuous R
  U_continuous : Continuous U
  recomb_nonneg : ∀ t, 0 ≤ t → 0 ≤ recomb t
  D_positive : ∀ t, 0 ≤ t → 0 < D t
  R_nonneg : ∀ t, 0 ≤ t → 0 ≤ R t
  U_nonneg : ∀ t, 0 ≤ t → 0 ≤ U t
  initial : D 0 = 1 ∧ R 0 = 0 ∧ U 0 = 0
  equations : PanPreEquations rate recomb D R U

noncomputable def PanPreModel.law {rate : ℝ → ℝ} (P : PanPreModel rate) (H : ℝ → ℝ) :
    Measure (ℝ × ℝ) := clockJointLaw rate H P.D (fun t => P.R t+P.U t)

theorem PanPreModel.total_derivative {rate : ℝ → ℝ} (P : PanPreModel rate)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun x => P.D x+(P.R x+P.U x))
      (-rate t * (P.D t+2*(P.R t+P.U t))) t := by
  rcases P.equations t ht with ⟨hd,hr,hu⟩
  convert! hd.add (hr.add hu) using 1
  ring

theorem PanPreModel.law_probability {rate : ℝ → ℝ} (P : PanPreModel rate) (H : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t) (htail : Tendsto H atTop atTop) :
    IsProbabilityMeasure (P.law H) := by
  apply clockJointLaw_probability rate H P.D (fun t => P.R t+P.U t)
    hr hH P.D_continuous (P.R_continuous.add P.U_continuous) hrn
    (fun t ht => (P.D_positive t ht).le)
    (fun t ht => add_nonneg (P.R_nonneg t ht) (P.U_nonneg t ht))
    (by simp [P.initial]) hclock htail
  exact fun t ht => P.total_derivative ht

end Rhone.Statistics.Identifiability
