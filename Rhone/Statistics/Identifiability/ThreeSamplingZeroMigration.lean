/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingKernel
public import Rhone.Statistics.Identifiability.ThreeIntegrableZeroMigration

/-! # Without migration, only the initially all-together component yields a finite complete tree -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix ENNReal
namespace Rhone.Statistics.Identifiability.ThreeSampling

lemma zero_migration_same_mass (ρ : State → ℝ) (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (t : ℝ) :
    preRow ρ k c (fun _ => 0) t 0 = ρ 0 * Real.exp (-3 * integratedClock c t) := by
  have h3 : LocallyIntegrable (fun u => 3 * c u) volume := by
    convert! hc.smul (3 : ℝ) using 1
  have hd : ∀ᵐ u, u ∈ uIcc (0 : ℝ) t →
      HasDerivAt (fun v => preRow ρ k c (fun _ => 0) v 0)
        (-(3 * c u) * preRow ρ k c (fun _ => 0) u 0) u := by
    filter_upwards [preRow_derivative_ae ρ k c (fun _ => 0) hc (locallyIntegrable_const 0)]
      with u hu _
    apply (hu 0).congr_deriv
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, threeGenerator,
        MarkovChain.Identifiability.totalMigration]
    ring
  have he := scalar_ac_survival_identity (fun u => 3 * c u)
    (fun u => preRow ρ k c (fun _ => 0) u 0) h3 0 t
    (preRow_ac ρ k c (fun _ => 0) hc (locallyIntegrable_const 0) 0 t 0) hd
  simpa [preRow_initial ρ k c (fun _ => 0) hc (locallyIntegrable_const 0),
    intervalIntegral.integral_const_mul, integratedClock] using he

lemma zero_migration_pair_apart (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (s t : ℝ) :
    timeVaryingPairTransition k c (fun _ => 0) s t 1 0 = 0 := by
  apply integrableTransition_zero_outside_closed _
    (PairIntegrable.generator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0))
    (fun j : Fin 2 => j = 1) _ s t 1 0 rfl (by decide)
  filter_upwards [] with u j l hj hl
  subst j
  fin_cases l <;> simp_all
      [MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.totalMigration]

lemma jointDensity_zero_migration (ρ : State → ℝ) (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (p : ℝ × ℝ) :
    jointDensity ρ k c (fun _ => 0) p = ρ 0 * PanThreeSample.jointDensity c p := by
  simp [jointDensity, firstFlux, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    IslandThreeTimes.firstRate, timeVaryingPairExitDensity,
    zero_migration_same_mass ρ k c hc, zero_migration_pair_apart k c hc,
    ThreeIntegrable.pair_zero_migration_initial k c hc,
    PanThreeSample.jointDensity, PanThreeSample.firstDensity, conditionalPairDensity]
  ring

lemma jointDensity_zero_migration_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hzero : ∀ᵐ u, 0 ≤ u → q u = 0) {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    jointDensity ρ k c q p = ρ 0 * PanThreeSample.jointDensity c p := by
  have hpre : preRow ρ k c q p.1 = preRow ρ k c (fun _ => 0) p.1 := by
    apply congrArg (fun M : Matrix State State ℝ => ρ ᵥ* M)
    apply integrableTransition_eq_of_ae_on_interval _ _
      (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq)
      (ThreeIntegrable.preGenerator_locallyIntegrable k c (fun _ => 0) hc
        (locallyIntegrable_const 0))
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
  rw [← jointDensity_zero_migration ρ k c hc p]
  simp only [jointDensity, firstFlux, timeVaryingPairExitDensity, hpre, hpair]

lemma law_zero_migration (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ0 : 0 ≤ ρ 0) (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hzero : ∀ᵐ u, 0 ≤ u → q u = 0) :
    law ρ k c q = ENNReal.ofReal (ρ 0) • PanThreeSample.law c := by
  unfold law PanThreeSample.law triangularDensityLaw
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  rw [jointDensity_zero_migration_ae ρ k c q hc hq hzero hp, ENNReal.ofReal_mul hρ0]
  rfl

end Rhone.Statistics.Identifiability.ThreeSampling
