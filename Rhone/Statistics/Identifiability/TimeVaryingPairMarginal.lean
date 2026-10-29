/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingAdmissibility
public import Rhone.Statistics.Identifiability.TimeVaryingProjectionDuhamel
public import Rhone.Statistics.Identifiability.TimeVaryingJointLaw
public import Rhone.Statistics.Identifiability.PairProjection

/-! # The surviving-pair marginal of the time-dependent event process -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Matrix
namespace Rhone.Statistics.Identifiability

noncomputable def timeVaryingPendingPair (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) : Fin 2 → ℝ := fun j =>
  ∫ s in (0 : ℝ)..t, ((timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s)) ᵥ*
    timeVaryingPairTransition k c q s t) j

theorem timeVaryingFirstARow_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    Continuous (fun t => timeVaryingPreRow k c q r t ᵥ* firstAKernel (c t)) := by
  apply continuous_pi; intro j
  simp only [Matrix.vecMul, dotProduct]
  apply continuous_finsetSum; intro i _
  apply ((continuous_apply i).comp (timeVaryingPreRow_continuous k c q r hc hq hr)).mul
  unfold firstAKernel
  split_ifs <;> fun_prop

theorem timeVaryingPreRow_projection_balance (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ)
    (hsupport : ∀ i, ¬ Admissible k i → timeVaryingPreRow k c q r t i = 0) :
    (timeVaryingPreRow k c q r t ᵥ* timeVaryingARGGenerator k c q r t) ᵥ* bProjection +
      timeVaryingPreRow k c q r t ᵥ* firstAKernel (c t) =
    (timeVaryingPreRow k c q r t ᵥ* bProjection) ᵥ* MarkovChain.Identifiability.pairGenerator k
        (c t) (q t) := by
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_add]
  funext j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Admissible k i
  · rw [show (timeVaryingARGGenerator k c q r t * bProjection + firstAKernel (c t)) i j =
      (bProjection * MarkovChain.Identifiability.pairGenerator k (c t) (q t)) i j from
      pair_projection_generator k (c t) (q t) (r t) i hi j]
  · simp [hsupport i hi]

theorem timeVaryingPreRow_projection_hasDerivAt (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hsupport : ∀ t i, ¬ Admissible k i → timeVaryingPreRow k c q r t i = 0)
    (t : ℝ) (j : Fin 2) :
    HasDerivAt (fun s => (timeVaryingPreRow k c q r s ᵥ* bProjection) j)
      (((timeVaryingPreRow k c q r t ᵥ* bProjection) ᵥ* MarkovChain.Identifiability.pairGenerator k
          (c t) (q t) -
        timeVaryingPreRow k c q r t ᵥ* firstAKernel (c t)) j) t := by
  have h := finiteRowMatrixProduct_hasDerivAt (timeVaryingPreRow k c q r)
    (fun s => timeVaryingPreRow k c q r s ᵥ* timeVaryingARGGenerator k c q r s)
    (fun _ => bProjection) (fun _ => 0)
    (fun s i => inhomogeneousTransition_hasDerivAt_right _
      (timeVaryingARGGenerator_continuous k c q r hc hq hr) 0 s 0 i)
    (fun s i j => hasDerivAt_const s (bProjection i j)) t j
  have hb := timeVaryingPreRow_projection_balance k c q r t (hsupport t)
  have hb' := congrFun hb j
  convert h using 1
  simp only [Matrix.vecMul_zero, add_zero]
  simp only [Pi.add_apply] at hb'
  simp only [Pi.sub_apply]
  linarith

theorem timeVaryingPair_projection_duhamel_of_support (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hsupport : ∀ t i, ¬ Admissible k i → timeVaryingPreRow k c q r t i = 0)
    (t : ℝ) :
    timeVaryingPreRow k c q r t ᵥ* bProjection + timeVaryingPendingPair k c q r t =
      timeVaryingPairTransition k c q 0 t 0 := by
  have h := finiteRow_projection_duhamel
      (fun s => MarkovChain.Identifiability.pairGenerator k (c s) (q s))
    (timeVaryingPairGenerator_continuous k c q hc hq)
    (fun s => timeVaryingPreRow k c q r s ᵥ* bProjection)
    (fun s => timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s))
    (timeVaryingFirstARow_continuous k c q r hc hq hr)
    (timeVaryingPreRow_projection_hasDerivAt k c q r hc hq hr hsupport) t
  have hi : timeVaryingPreRow k c q r 0 ᵥ* bProjection = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 := by
    funext j
    simp [timeVaryingPreRow, inhomogeneousTransition_self _
      (timeVaryingARGGenerator_continuous k c q r hc hq hr), Matrix.vecMul,
      dotProduct, Matrix.one_apply, bProjection_initial, eq_comm]
  rw [hi] at h
  change _ = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 ᵥ* timeVaryingPairTransition k c q 0 t at h
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 ᵥ* timeVaryingPairTransition k c q 0 t =
    timeVaryingPairTransition k c q 0 t 0 by
      ext j; simp [Matrix.vecMul, dotProduct, Matrix.one_apply]] at h
  exact h

theorem timeVaryingPair_projection_duhamel (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    timeVaryingPreRow k c q r t ᵥ* bProjection + timeVaryingPendingPair k c q r t =
      timeVaryingPairTransition k c q 0 t 0 :=
  timeVaryingPair_projection_duhamel_of_support k c q r hc hq hr
    (timeVaryingPreRow_not_admissible k c q r hc hq hr) t

theorem timeVaryingPendingPair_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {t : ℝ} (ht : 0 ≤ t) (j : Fin 2) :
    0 ≤ timeVaryingPendingPair k c q r t j := by
  apply intervalIntegral.integral_nonneg ht
  intro s hs
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg; intro i _
  apply mul_nonneg
  · apply Finset.sum_nonneg; intro l _
    exact mul_nonneg (timeVaryingPreRow_nonneg k c q r hc hq hr hcn hqn hrn hs.1 l)
      (firstAKernel_nonneg (hcn s hs.1) l i)
  · exact timeVaryingPairTransition_nonneg k c q hc hq hqn hs.1 hs.2 i j

theorem timeVaryingPair_survival_decomposition (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    timeVaryingPreSurvival k c q r t + (∑ j, timeVaryingPendingPair k c q r t j) =
      timeVaryingPairSurvival k c q 0 0 t := by
  have h := congrArg (fun v : Fin 2 → ℝ => ∑ j, v j)
    (timeVaryingPair_projection_duhamel k c q r hc hq hr t)
  have hb (i : MarkovChain.Identifiability.State) : (∑ j, bProjection i j) = 1 := by
    simp [bProjection, Fin.sum_univ_two]
  simpa only [Pi.add_apply, Finset.sum_add_distrib, Matrix.vecMul, dotProduct,
    Finset.sum_comm (f := fun j i => timeVaryingPreRow k c q r t i * bProjection i j),
    ← Finset.mul_sum, hb, mul_one, timeVaryingPreSurvival, timeVaryingPairSurvival] using h

theorem timeVaryingPreSurvival_le_pair (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {t : ℝ} (ht : 0 ≤ t) :
    timeVaryingPreSurvival k c q r t ≤ timeVaryingPairSurvival k c q 0 0 t := by
  rw [← timeVaryingPair_survival_decomposition k c q r hc hq hr t]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ =>
    timeVaryingPendingPair_nonneg k c q r hc hq hr hcn hqn hrn ht j))

theorem timeVaryingPreSurvival_tendsto_zero_of_pair (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ hpair
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Finset.sum_nonneg (fun i _ =>
      timeVaryingPreRow_nonneg k c q r hc hq hr hcn hqn hrn ht i)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact timeVaryingPreSurvival_le_pair k c q r hc hq hr hcn hqn hrn ht

theorem timeVaryingJointLaw_probability_of_pair (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (timeVaryingJointLaw k c q r) :=
  timeVaryingJointLaw_probability k c q r hc hq hr hcn hqn hrn
    (timeVaryingPreSurvival_tendsto_zero_of_pair k c q r hc hq hr hcn hqn hrn
      (hpair 0 le_rfl 0)) hpair

theorem markCount_B_projection (i : MarkovChain.Identifiability.State) :
    (if MarkovChain.Identifiability.bTogether (MarkovChain.Identifiability.shape i) then 1 else 0) =
      markCount i 0 + markCount i 3 + markCount i 4 := by
  fin_cases i <;> decide

theorem bProjection_density_split (c : ℝ) (i : MarkovChain.Identifiability.State) :
    bProjection i 0 * c = diagonalExit c i + markRates c i 3 + markRates c i 4 := by
  have h := markCount_B_projection i
  have h' : (if MarkovChain.Identifiability.bTogether (MarkovChain.Identifiability.shape i) then
      (1 : ℝ) else 0) =
      (markCount i 0 : ℝ) + (markCount i 3 : ℝ) + (markCount i 4 : ℝ) := by
    exact_mod_cast h
  simp only [bProjection, ↓reduceIte, diagonalExit, markRates]
  rw [h']
  ring

theorem timeVaryingPreRow_projection_exit (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ) :
    (timeVaryingPreRow k c q r t ᵥ* bProjection) 0 * c t =
      timeVaryingDiagonalDensity k c q r t + timeVaryingBranchFlux k c q r 3 4 t := by
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, mul_assoc,
    bProjection_density_split, mul_add, Finset.sum_add_distrib,
    timeVaryingDiagonalDensity, timeVaryingMarkFlux, timeVaryingBranchFlux, diagonalExit]
  ring

theorem timeVaryingPendingPair_exit (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ) :
    timeVaryingPendingPair k c q r t 0 * c t =
      ∫ s in (0 : ℝ)..t, timeVaryingUpperDensity k c q r (s,t) := by
  rw [timeVaryingPendingPair, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [timeVaryingUpperDensity_matrix]
  simp [dotProduct, Fin.sum_univ_two, MarkovChain.Identifiability.pairDensity]

theorem timeVaryingJoint_marginal_density (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    timeVaryingDiagonalDensity k c q r t + timeVaryingBranchFlux k c q r 3 4 t +
      (∫ s in (0 : ℝ)..t, timeVaryingUpperDensity k c q r (s,t)) =
      timeVaryingPairExitDensity k c q 0 0 t := by
  have h := congrArg (fun v : Fin 2 → ℝ => v 0 * c t)
    (timeVaryingPair_projection_duhamel k c q r hc hq hr t)
  simpa only [Pi.add_apply, add_mul, timeVaryingPreRow_projection_exit,
    timeVaryingPendingPair_exit, timeVaryingPairExitDensity] using h

theorem timeVaryingPendingPair_eq_integral (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    timeVaryingPendingPair k c q r t =
      ∫ s in (0 : ℝ)..t, (timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s)) ᵥ*
        timeVaryingPairTransition k c q s t := by
  have hcont : Continuous (fun s =>
      (timeVaryingPreRow k c q r s ᵥ* firstAKernel (c s)) ᵥ*
        timeVaryingPairTransition k c q s t) := by
    apply continuous_pi; intro j
    simp only [Matrix.vecMul, dotProduct]
    apply continuous_finsetSum; intro i _
    apply ((continuous_apply i).comp (timeVaryingFirstARow_continuous k c q r hc hq hr)).mul
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((timeVaryingPairTransition_continuous k c q hc hq).comp
        (continuous_id.prodMk continuous_const)))
  funext j
  exact ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ) (hcont.intervalIntegrable 0 t)

@[simp] theorem timeVaryingPendingPair_zero (k : ℕ) (c q r : ℝ → ℝ) :
    timeVaryingPendingPair k c q r 0 = 0 := by
  ext j
  simp [timeVaryingPendingPair]

theorem timeVaryingPendingPair_hasDerivAt (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) (j : Fin 2) :
    HasDerivAt (fun s => timeVaryingPendingPair k c q r s j)
      ((timeVaryingPendingPair k c q r t ᵥ* MarkovChain.Identifiability.pairGenerator k (c t)
          (q t) +
        timeVaryingPreRow k c q r t ᵥ* firstAKernel (c t)) j) t := by
  have heq : (fun s => timeVaryingPendingPair k c q r s j) =
      fun s => timeVaryingPairTransition k c q 0 s 0 j -
        (timeVaryingPreRow k c q r s ᵥ* bProjection) j := by
    funext s
    have h := congrFun (timeVaryingPair_projection_duhamel k c q r hc hq hr s) j
    simp only [Pi.add_apply] at h
    linarith
  rw [heq]
  have h := (inhomogeneousTransition_hasDerivAt_right _
    (timeVaryingPairGenerator_continuous k c q hc hq) 0 t 0 j).sub
    (timeVaryingPreRow_projection_hasDerivAt k c q r hc hq hr
      (timeVaryingPreRow_not_admissible k c q r hc hq hr) t j)
  convert! h using 1
  change _ = ((timeVaryingPairTransition k c q 0 t 0) ᵥ* MarkovChain.Identifiability.pairGenerator k
      (c t) (q t)) j - _
  rw [← timeVaryingPair_projection_duhamel k c q r hc hq hr t, Matrix.add_vecMul]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem timeVaryingRegularJointLaw_probability_of_pair (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (regularJointLaw (timeVaryingDiagonalDensity k c q r)
      (timeVaryingUpperDensity k c q r)) := by
  rw [← timeVaryingJointLaw_eq_regular k c q r hc hq hr]
  exact timeVaryingJointLaw_probability_of_pair k c q r hc hq hr hcn hqn hrn hpair

end Rhone.Statistics.Identifiability
