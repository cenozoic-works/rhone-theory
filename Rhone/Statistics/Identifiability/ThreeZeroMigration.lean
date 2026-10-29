/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingSeparation
public import Rhone.Statistics.Identifiability.ScalarClockIdentity

/-! # Exact panmictic law for the zero-migration boundary -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma preRow_zero_migration_initial (k : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (t : ℝ) :
    preRow k c (fun _ => 0) t 0 = Real.exp (-3 * integratedClock c t) := by
  have hd (u : ℝ) : HasDerivAt (fun v => preRow k c (fun _ => 0) v 0)
      (-(3 * c u) * preRow k c (fun _ => 0) u 0) u := by
    apply (preRow_derivative k c (fun _ => 0) hc continuous_const u 0).congr_deriv
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, threeGenerator,
        MarkovChain.Identifiability.totalMigration]
    ring
  have he := scalar_survival_clock_identity (fun u => 3 * c u)
    (fun u => preRow k c (fun _ => 0) u 0) (continuous_const.mul hc) hd 0 t
  simpa [preRow_initial k c (fun _ => 0) hc continuous_const, integratedClock_scale,
    integratedClock] using he

lemma pair_zero_migration_initial (k : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (s t : ℝ) :
    timeVaryingPairTransition k c (fun _ => 0) s t 0 0 =
      Real.exp (integratedClock c s - integratedClock c t) := by
  have hd (u : ℝ) : HasDerivAt (fun v => timeVaryingPairTransition k c (fun _ => 0) s v 0 0)
      (-c u * timeVaryingPairTransition k c (fun _ => 0) s u 0 0) u := by
    apply (inhomogeneousTransition_hasDerivAt_right _
      (timeVaryingPairGenerator_continuous k c (fun _ => 0) hc continuous_const)
      s u 0 0).congr_deriv
    change (∑ l, timeVaryingPairTransition k c (fun _ => 0) s u 0 l *
      MarkovChain.Identifiability.pairGenerator k (c u) 0 l 0) =
      -c u * timeVaryingPairTransition k c (fun _ => 0) s u 0 0
    simp [Fin.sum_univ_succ, MarkovChain.Identifiability.pairGenerator,
        MarkovChain.Identifiability.totalMigration]
    ring
  have he := scalar_survival_clock_identity c
    (fun u => timeVaryingPairTransition k c (fun _ => 0) s u 0 0) hc hd s t
  simpa [timeVaryingPairTransition_self k c (fun _ => 0) hc continuous_const] using he

lemma jointDensity_zero_migration (k : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (p : ℝ × ℝ) :
    jointDensity k c (fun _ => 0) p = PanThreeSample.jointDensity c p := by
  have hz := zero_migration_pre_support k c hc p.1 1 (by decide)
  simp [jointDensity, firstFlux, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    IslandThreeTimes.firstRate, hz, preRow_zero_migration_initial k c hc,
    timeVaryingPairExitDensity, pair_zero_migration_initial k c hc,
    PanThreeSample.jointDensity, PanThreeSample.firstDensity, conditionalPairDensity]
  ring

lemma jointDensity_zero_migration_halfLine (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hzero : ∀ t, 0 ≤ t → q t = 0)
    {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    jointDensity k c q p = PanThreeSample.jointDensity c p := by
  have hpre : preRow k c q p.1 = preRow k c (fun _ => 0) p.1 := by
    have he := inhomogeneousTransition_eq_of_eqOn
      (fun u => threeGenerator k (c u) (q u)) (fun u => threeGenerator k (c u) 0)
      (preGenerator_continuous k c q hc hq)
      (preGenerator_continuous k c (fun _ => 0) hc continuous_const) hp.1.le
      (fun u hu => by dsimp only; rw [hzero u hu.1])
    exact congrArg (fun M => M 0) he
  have hpair : timeVaryingPairTransition k c q p.1 p.2 =
      timeVaryingPairTransition k c (fun _ => 0) p.1 p.2 := by
    apply inhomogeneousTransition_eq_of_eqOn
      (fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u))
          (fun u => MarkovChain.Identifiability.pairGenerator k (c u) 0)
      (timeVaryingPairGenerator_continuous k c q hc hq)
      (timeVaryingPairGenerator_continuous k c (fun _ => 0) hc continuous_const) hp.2.le
    intro u hu
    dsimp only
    rw [hzero u (hp.1.le.trans hu.1)]
  rw [← jointDensity_zero_migration k c hc p]
  simp only [jointDensity, firstFlux, timeVaryingPairExitDensity, hpre, hpair]

theorem law_zero_migration_halfLine (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hzero : ∀ t, 0 ≤ t → q t = 0) :
    law k c q = PanThreeSample.law c := by
  unfold law PanThreeSample.law triangularDensityLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  rw [jointDensity_zero_migration_halfLine k c q hc hq hzero hp]

end Rhone.Statistics.Identifiability.ThreeTimeVarying
