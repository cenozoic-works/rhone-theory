/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingJointMarginalMeasure
public import Rhone.Statistics.Identifiability.SimultaneousOnsetFlow
public import Rhone.Statistics.Identifiability.UnknownClockMembership

/-! # Observable-law consequences of the time-dependent finite-flow witness -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Matrix
namespace Rhone.Statistics.Identifiability

theorem timeVaryingBranchFlux_eq_firstA (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ) :
    timeVaryingBranchFlux k c q r 1 2 t =
      c t * ∑ i, SimultaneousOnset.preRow k c q r t i *
          (MarkovChain.Identifiability.firstATable i : ℝ) := by
  simp only [timeVaryingBranchFlux, timeVaryingMarkFlux, ← Finset.sum_add_distrib,
    ← mul_add, markRates_A_same, markRates_A_apart, firstAKernel]
  simp only [ite_true, Fin.isValue, Fin.reduceEq, ite_false]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = c t * (timeVaryingPreRow k c q r t i * _)
  ring

theorem timeVaryingUpperDensity_self (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (t : ℝ) :
    timeVaryingUpperDensity k c q r (t,t) =
      (c t)^2 * ∑ i, SimultaneousOnset.preRow k c q r t i *
          (MarkovChain.Identifiability.firstAThenBTable i : ℝ) := by
  simp only [timeVaryingUpperDensity, timeVaryingBranchDensity,
    timeVaryingPairExitDensity, timeVaryingPairTransition_self k c q hc hq,
    Matrix.one_apply, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    one_mul, zero_mul, mul_zero, add_zero]
  simp only [timeVaryingMarkFlux, markRates_A_same, firstAKernel, ite_true]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (c t)^2 * (timeVaryingPreRow k c q r t i * _)
  ring

theorem timeVarying_observable_determinant (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (t : ℝ) :
    timeVaryingPairSurvival k c q 0 0 t * timeVaryingUpperDensity k c q r (t,t) -
      timeVaryingPairExitDensity k c q 0 0 t * timeVaryingBranchFlux k c q r 1 2 t =
      (c t)^2 * SimultaneousOnset.witness k c q r t := by
  rw [timeVaryingUpperDensity_self k c q r hc hq,
    timeVaryingBranchFlux_eq_firstA]
  unfold timeVaryingPairSurvival timeVaryingPairExitDensity timeVaryingPairTransition
    SimultaneousOnset.witness SimultaneousOnset.pairRow
  ring

noncomputable def ProperPanModel.upperDensity (P : ProperPanModel) (p : ℝ × ℝ) : ℝ :=
  P.rate p.1 * (P.pre.R p.1 + P.pre.U p.1) * P.rate p.2 *
    Real.exp (P.clock p.1 - P.clock p.2)

noncomputable def ProperPanModel.branchFlux (P : ProperPanModel) (t : ℝ) : ℝ :=
  P.rate t * (P.pre.R t + P.pre.U t)

theorem ProperPanModel.upperDensity_continuous (P : ProperPanModel) :
    Continuous P.upperDensity := by
  have hr := P.rate_continuous
  have hR := P.pre.R_continuous
  have hU := P.pre.U_continuous
  have hH := P.clock_continuous
  unfold ProperPanModel.upperDensity
  fun_prop

theorem ProperPanModel.branchFlux_nonneg (P : ProperPanModel) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ P.branchFlux t :=
  mul_nonneg (P.rate_nonneg t ht) (add_nonneg (P.pre.R_nonneg t ht) (P.pre.U_nonneg t ht))

theorem ProperPanModel.upperDensity_nonneg (P : ProperPanModel) {p : ℝ × ℝ}
    (hp : p ∈ upperWedge) : 0 ≤ P.upperDensity p :=
  mul_nonneg (mul_nonneg (P.branchFlux_nonneg hp.1.le)
    (P.rate_nonneg p.2 (hp.1.trans hp.2).le)) (Real.exp_pos _).le

theorem ProperPanModel.upperDensity_self (P : ProperPanModel) (t : ℝ) :
    P.upperDensity (t,t) = P.branchFlux t * P.rate t := by
  simp [ProperPanModel.upperDensity, ProperPanModel.branchFlux]

theorem ProperPanModel.upperDensity_lintegral (P : ProperPanModel)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (P.upperDensity (s,t))) =
      ENNReal.ofReal (P.branchFlux s) := by
  have he : (fun t => P.upperDensity (s,t)) =
      fun t => P.branchFlux s * conditionalPairDensity P.rate P.clock s t := by
    funext t
    simp only [ProperPanModel.upperDensity, ProperPanModel.branchFlux, conditionalPairDensity]
    ring
  simp_rw [show ∀ t, P.upperDensity (s, t) =
    P.branchFlux s * conditionalPairDensity P.rate P.clock s t from fun t => congrFun he t]
  simp_rw [ENNReal.ofReal_mul (P.branchFlux_nonneg hs)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    conditionalPair_lintegral_one P.rate P.clock hs P.rate_nonneg
      P.clock_derivative P.clock_diverges, mul_one]

theorem timeVaryingJointLaw_eq_pan_upper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) (P : ProperPanModel)
    (he : timeVaryingJointLaw k c q r = P.law) :
    EqOn (timeVaryingUpperDensity k c q r) P.upperDensity upperWedge := by
  rw [timeVaryingJointLaw_eq_regular k c q r hc hq hr] at he
  exact regularJointLaw_identifies_upper
    (timeVaryingJointDensities_continuous k c q r hc hq hr).2.1 P.upperDensity_continuous
    (timeVaryingJointDensities_nonneg k c q r hc hq hr hcn hqn hrn).2.1
    (fun _ hp => P.upperDensity_nonneg hp) he

theorem upper_density_eq_trace {j₁ j₂ : ℝ × ℝ → ℝ}
    (h₁ : Continuous j₁) (h₂ : Continuous j₂) (he : EqOn j₁ j₂ upperWedge)
    {t : ℝ} (ht : 0 < t) : j₁ (t,t) = j₂ (t,t) := by
  have hsec : EqOn (fun u => j₁ (t,u)) (fun u => j₂ (t,u)) (Ioi t) :=
    fun u hu => he ⟨ht, hu⟩
  have hcl := hsec.closure (h₁.comp (continuous_const.prodMk continuous_id))
    (h₂.comp (continuous_const.prodMk continuous_id))
  exact hcl (by rw [closure_Ioi]; exact le_refl t)

theorem timeVaryingJointLaw_eq_pan_branchFlux (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) (P : ProperPanModel)
    (he : timeVaryingJointLaw k c q r = P.law) {t : ℝ} (ht : 0 < t)
    (hpair : ∀ i, Tendsto (timeVaryingPairSurvival k c q t i) atTop (𝓝 0)) :
    timeVaryingBranchFlux k c q r 1 2 t = P.branchFlux t := by
  have hu := timeVaryingJointLaw_eq_pan_upper k c q r hc hq hr hcn hqn hrn P he
  have hi : (∫⁻ u in Ioi t, ENNReal.ofReal (timeVaryingUpperDensity k c q r (t,u))) =
      ∫⁻ u in Ioi t, ENNReal.ofReal (P.upperDensity (t,u)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro u hu'
    exact congrArg ENNReal.ofReal (hu (show (t,u) ∈ upperWedge from ⟨ht, hu'⟩))
  unfold timeVaryingUpperDensity at hi
  rw [timeVaryingBranchDensity_lintegral k c q r hc hq hr hcn hqn hrn ht.le 1 2 hpair,
    P.upperDensity_lintegral ht.le] at hi
  exact (ENNReal.ofReal_eq_ofReal_iff
    (timeVaryingBranchFlux_nonneg k c q r hc hq hr hcn hqn hrn ht.le 1 2)
    (P.branchFlux_nonneg ht.le)).mp hi

end Rhone.Statistics.Identifiability
