/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableLawSeparation
public import Rhone.Statistics.Identifiability.ScalarACClockIdentity
public import Rhone.Statistics.Identifiability.IntegrableFlowCongruence

/-! # The zero-migration boundary is exactly panmictic for locally L1 source histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma preRow_zero_migration_initial (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (t : ℝ) :
    preRow k c (fun _ => 0) t 0 = Real.exp (-3 * integratedClock c t) := by
  have h3 : LocallyIntegrable (fun u => 3 * c u) volume := by
    convert! hc.smul (3 : ℝ) using 1
  have hd : ∀ᵐ u, u ∈ uIcc (0 : ℝ) t →
      HasDerivAt (fun v => preRow k c (fun _ => 0) v 0)
        (-(3 * c u) * preRow k c (fun _ => 0) u 0) u := by
    filter_upwards [preRow_derivative_ae k c (fun _ => 0) hc (locallyIntegrable_const 0)]
      with u hu _
    apply (hu 0).congr_deriv
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, threeGenerator,
        MarkovChain.Identifiability.totalMigration]
    ring
  have he := scalar_ac_survival_identity (fun u => 3 * c u)
    (fun u => preRow k c (fun _ => 0) u 0) h3 0 t
    (preRow_ac k c (fun _ => 0) hc (locallyIntegrable_const 0) 0 t 0) hd
  simpa [preRow_initial k c (fun _ => 0) hc (locallyIntegrable_const 0),
    intervalIntegral.integral_const_mul, integratedClock] using he

lemma preRow_zero_migration_support (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (t : ℝ) (i : ThreeState) (hi : i ≠ 0) :
    preRow k c (fun _ => 0) t i = 0 := by
  apply integrableTransition_zero_outside_closed _
    (preGenerator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0))
    (fun j : ThreeState => j = 0) _ 0 t 0 i rfl hi
  filter_upwards [] with u j l hj hl
  subst j
  fin_cases l <;> simp_all [threeGenerator, MarkovChain.Identifiability.totalMigration]

lemma pair_zero_migration_initial (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (s t : ℝ) :
    timeVaryingPairTransition k c (fun _ => 0) s t 0 0 =
      Real.exp (integratedClock c s - integratedClock c t) := by
  have hQi := PairIntegrable.generator_locallyIntegrable k c (fun _ => 0) hc
    (locallyIntegrable_const 0)
  have hd : ∀ᵐ u, u ∈ uIcc s t →
      HasDerivAt (fun v => timeVaryingPairTransition k c (fun _ => 0) s v 0 0)
        (-c u * timeVaryingPairTransition k c (fun _ => 0) s u 0 0) u := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right _ hQi] with u hu _
    apply (hu s 0 0).congr_deriv
    change (∑ l, timeVaryingPairTransition k c (fun _ => 0) s u 0 l *
      MarkovChain.Identifiability.pairGenerator k (c u) 0 l 0) = -c u * timeVaryingPairTransition k
          c (fun _ => 0) s u 0 0
    simp [Fin.sum_univ_succ, MarkovChain.Identifiability.pairGenerator,
        MarkovChain.Identifiability.totalMigration]
    ring
  have he := scalar_ac_survival_identity c
    (fun u => timeVaryingPairTransition k c (fun _ => 0) s u 0 0) hc s t
    (integrableTransition_entry_ac_right _ hQi s s t 0 0) hd
  rw [IntegrableExposure.interval_eq_clock_sub c hc] at he
  simpa [timeVaryingPairTransition, integrableTransition_self _ hQi] using he

lemma jointDensity_zero_migration (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (p : ℝ × ℝ) :
    jointDensity k c (fun _ => 0) p = PanThreeSample.jointDensity c p := by
  have hz := preRow_zero_migration_support k c hc p.1 1 (by decide)
  simp [jointDensity, firstFlux, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    IslandThreeTimes.firstRate, hz, preRow_zero_migration_initial k c hc,
    timeVaryingPairExitDensity, pair_zero_migration_initial k c hc,
    PanThreeSample.jointDensity, PanThreeSample.firstDensity, conditionalPairDensity]
  ring

theorem law_zero_migration_halfLine_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hzero : ∀ᵐ u, 0 ≤ u → q u = 0) : law k c q = PanThreeSample.law c := by
  unfold law PanThreeSample.law triangularDensityLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  have hpre : preRow k c q p.1 = preRow k c (fun _ => 0) p.1 := by
    apply congrArg (fun M : Matrix ThreeState ThreeState ℝ => M 0)
    apply integrableTransition_eq_of_ae_on_interval _ _
      (preGenerator_locallyIntegrable k c q hc hq)
      (preGenerator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0))
    filter_upwards [hzero] with u hu hmem
    rw [uIcc_of_le hp.1.le] at hmem
    rw [hu hmem.1]
  have hpair : timeVaryingPairTransition k c q p.1 p.2 =
      timeVaryingPairTransition k c (fun _ => 0) p.1 p.2 := by
    apply integrableTransition_eq_of_ae_on_interval _ _
      (PairIntegrable.generator_locallyIntegrable k c q hc hq)
      (PairIntegrable.generator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0))
    filter_upwards [hzero] with u hu hmem
    rw [uIcc_of_le hp.2.le] at hmem
    rw [hu (hp.1.le.trans hmem.1)]
  rw [← jointDensity_zero_migration k c hc p]
  simp only [jointDensity, firstFlux, timeVaryingPairExitDensity, hpre, hpair]

end Rhone.Statistics.Identifiability.ThreeIntegrable
