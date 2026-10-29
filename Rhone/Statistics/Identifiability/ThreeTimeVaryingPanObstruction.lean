/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingCanonicalRate
public import Rhone.Statistics.Identifiability.RegularDensityIdentification
public import Rhone.Statistics.Identifiability.TimeVaryingLawWitness

/-! # A complete obstruction for proper locally integrable pan histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

theorem equal_law_scaled_witness_zero (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law k c q = PanThreeSample.law rate) {t : ℝ} (ht : 0 < t) :
    (c t)^2 * witness k c q t = 0 := by
  let L := canonicalRate k c q
  have hL : Continuous L := canonicalRate_continuous k c q hc hq hqn
  have hLn : ∀ u, 0 ≤ L u := canonicalRate_nonnegative k c q hc hq hcn hqn
  have hAE := equal_law_rate_ae k c q hc hq hcn hqn hpair rate hr hn htail he
  have hLaw : law k c q = PanThreeSample.law L :=
    he.trans (PanThreeSample.law_congr_halfLine_ae hAE)
  have hHL := integratedClock_continuous L hL.locallyIntegrable
  have hJ : Continuous (PanThreeSample.jointDensity L) := by
    unfold PanThreeSample.jointDensity PanThreeSample.firstDensity conditionalPairDensity
    fun_prop
  have hJn (p : ℝ × ℝ) : 0 ≤ PanThreeSample.jointDensity L p := by
    rw [PanThreeSample.jointDensity_exp]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hLn p.1)) (hLn p.2))
      (Real.exp_pos _).le
  have hreg : regularJointLaw (fun _ => 0) (jointDensity k c q) =
      regularJointLaw (fun _ => 0) (PanThreeSample.jointDensity L) :=
    congrArg (fun μ : Measure (ℝ × ℝ) => diagonalDensityLaw (fun _ => 0) + μ + μ.map Prod.swap) hLaw
  have hupper := regularJointLaw_identifies_upper (jointDensity_continuous k c q hc hq) hJ
    (fun p hp => jointDensity_nonnegative k c q hc hq hcn hqn hp) (fun p _ => hJn p) hreg
  have htrace := upper_density_eq_trace (jointDensity_continuous k c q hc hq) hJ hupper ht
  have hClock := PanThreeSample.integratedClock_eq_of_halfLine_ae hAE ht.le
  have hSurv := equal_law_survival k c q hc hq hcn hqn hpair rate hr hn htail he ht.le
  have hExp : Real.exp (-2 * integratedClock L t - integratedClock L t) = survival k c q t := by
    rw [← hClock, hSurv]
    congr 1
    ring
  rw [PanThreeSample.jointDensity_exp L t t, hExp] at htrace
  have hCanon := canonicalRate_mul_survival k c q hc hq hqn ht.le
  change 3 * L t * survival k c q t = firstDensity k c q t at hCanon
  have hObs := observable_witness_identity k c q hc hq t
  rw [htrace, ← hCanon] at hObs
  have hz : 3 * survival k c q t * (3 * L t * L t * survival k c q t) -
      (3 * L t * survival k c q t)^2 = 0 := by ring
  rw [hz] at hObs
  exact hObs.symm

theorem law_ne_pan_of_positive_witness (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (hct : 0 < c t) (hw : 0 < witness k c q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop) :
    law k c q ≠ PanThreeSample.law rate := by
  intro he
  exact (ne_of_gt (mul_pos (sq_pos_of_pos hct) hw))
    (equal_law_scaled_witness_zero k c q hc hq hcn hqn hpair rate hr hn htail he ht)

end Rhone.Statistics.Identifiability.ThreeTimeVarying
