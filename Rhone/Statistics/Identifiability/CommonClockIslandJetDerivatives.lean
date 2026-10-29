/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockIslandPhase
public import Rhone.Statistics.Identifiability.FlowSeries
public import Rhone.Statistics.Identifiability.FlowJetNormBound
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Derivatives of the finite matrix exponential, not prescribed jets -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

noncomputable def commonClockIslandPhaseDensity (k : ℕ) (c q r : ℝ) : ℝ → ℝ :=
  commonClockIslandJet k c q r 0

theorem commonClockIslandPhaseDensity_exp (k : ℕ) (c q r t : ℝ) :
    commonClockIslandPhaseDensity k c q r t =
      (NormedSpace.exp (t • commonClockIslandPhase k c q r) *ᵥ
        commonClockIslandReward c) 0 := by
  simp [commonClockIslandPhaseDensity, commonClockIslandJet, flowOutput]

theorem commonClockIslandPhaseDensity_iteratedDeriv (k : ℕ) (c q r : ℝ) (j : ℕ) :
    iteratedDeriv j (commonClockIslandPhaseDensity k c q r) =
      commonClockIslandJet k c q r j := by
  induction j with
  | zero => exact iteratedDeriv_zero
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (commonClockIslandJet_hasDerivAt k c q r j t).deriv

theorem commonClockIslandPhaseDensity_deriv_zero (k : ℕ) (c q r : ℝ) :
    deriv (commonClockIslandPhaseDensity k c q r) 0 =
      -c * (c + 2 * MarkovChain.Identifiability.totalMigration k q + 2*r) / 2 := by
  have h := congrFun (commonClockIslandPhaseDensity_iteratedDeriv k c q r 1) 0
  simpa only [iteratedDeriv_one] using h.trans (commonClockIslandJet_one k c q r)

theorem commonClockIslandPhaseDensity_third_deriv_zero (k : ℕ) (c q r : ℝ) :
    iteratedDeriv 3 (commonClockIslandPhaseDensity k c q r) 0 =
      -c * commonClockIslandCubic c (MarkovChain.Identifiability.totalMigration k q) q r / 2 := by
  rw [commonClockIslandPhaseDensity_iteratedDeriv, commonClockIslandJet_three]

noncomputable def commonClockIslandCoefficient (k : ℕ) (c q r : ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ)⁻¹ * commonClockIslandJet k c q r j 0

theorem commonClockIslandPhaseDensity_series (k : ℕ) (c q r t : ℝ) :
    HasSum (fun j : ℕ => commonClockIslandCoefficient k c q r j * t^j)
      (commonClockIslandPhaseDensity k c q r t) := by
  have h := flowOutput_series (commonClockIslandPhase k c q r) 0
    (commonClockIslandReward c) t
  convert h using 1
  · funext j
    simp only [commonClockIslandCoefficient, commonClockIslandJet_zero_time]
    ring
  · rfl

theorem commonClockIslandCoefficient_zero (k : ℕ) (c q r : ℝ) :
    commonClockIslandCoefficient k c q r 0 = c/2 := by
  unfold commonClockIslandCoefficient
  rw [commonClockIslandJet_initial]
  norm_num

theorem commonClockIslandCoefficient_one (k : ℕ) (c q r : ℝ) :
    commonClockIslandCoefficient k c q r 1 =
      -c*(c + 2*MarkovChain.Identifiability.totalMigration k q + 2*r)/2 := by
  unfold commonClockIslandCoefficient
  rw [commonClockIslandJet_one]
  norm_num

theorem commonClockIslandCoefficient_two (k : ℕ) (c q r : ℝ) :
    commonClockIslandCoefficient k c q r 2 =
      c*((c + 2*MarkovChain.Identifiability.totalMigration k q + 2*r)^2 +
        4*MarkovChain.Identifiability.totalMigration k q*q + 10*c*r)/4 := by
  unfold commonClockIslandCoefficient
  rw [commonClockIslandJet_two]
  norm_num
  ring

theorem commonClockIslandCoefficient_three (k : ℕ) (c q r : ℝ) :
    commonClockIslandCoefficient k c q r 3 =
      -c*commonClockIslandCubic c (MarkovChain.Identifiability.totalMigration k q) q r/12 := by
  unfold commonClockIslandCoefficient
  rw [commonClockIslandJet_three]
  norm_num
  ring

theorem commonClockIslandPhaseDensity_iteratedDerivWithin (k : ℕ) (c q r : ℝ)
    (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin j (commonClockIslandPhaseDensity k c q r) (Set.Ici 0) t =
      commonClockIslandJet k c q r j t := by
  have hc : ContDiff ℝ j (commonClockIslandPhaseDensity k c q r) :=
    flowOutput_contDiff_nat (commonClockIslandPhase k c q r) 0
      (commonClockIslandReward c) 0 j
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hc.contDiffAt ht]
  rw [commonClockIslandPhaseDensity_iteratedDeriv]

theorem commonClockIslandPhaseDensity_derivative_one (k : ℕ) (c q r : ℝ) :
    iteratedDerivWithin 1 (commonClockIslandPhaseDensity k c q r) (Set.Ici 0) 0 =
      -c * (c + 2 * MarkovChain.Identifiability.totalMigration k q + 2*r) / 2 := by
  rw [commonClockIslandPhaseDensity_iteratedDerivWithin k c q r 1 (le_refl 0),
    commonClockIslandJet_one]

theorem commonClockIslandPhaseDensity_derivative_three (k : ℕ) (c q r : ℝ) :
    iteratedDerivWithin 3 (commonClockIslandPhaseDensity k c q r) (Set.Ici 0) 0 =
      -c * commonClockIslandCubic c (MarkovChain.Identifiability.totalMigration k q) q r / 2 := by
  rw [commonClockIslandPhaseDensity_iteratedDerivWithin k c q r 3 (le_refl 0),
    commonClockIslandJet_three]

end Rhone.Statistics.Identifiability
