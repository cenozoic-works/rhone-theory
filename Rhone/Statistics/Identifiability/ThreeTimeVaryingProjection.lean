/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingFlux
public import Rhone.Statistics.Identifiability.TimeVaryingProjectionDuhamel

/-! # Sampling consistency supplies first-merger properness from the sampled pair -/

@[expose] public section

noncomputable section
open Set Matrix Filter MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def pairProjection : Matrix ThreeState (Fin 2) ℝ := !![1, 0; 1/3, 2/3; 0, 1]

lemma projection_generator (k : ℕ) (c q : ℝ) :
    threeGenerator k c q * pairProjection + (2/3 : ℝ) • IslandThreeTimes.firstRate c =
      pairProjection * MarkovChain.Identifiability.pairGenerator k c q := by
  ext i j
  change (∑ z : ThreeState, threeGenerator k c q i z * pairProjection z j) +
    (2/3 : ℝ) * IslandThreeTimes.firstRate c i j =
      ∑ z : Fin 2, pairProjection i z * MarkovChain.Identifiability.pairGenerator k c q z j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairProjection, threeGenerator, IslandThreeTimes.firstRate,
      MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.totalMigration,
          Fin.sum_univ_succ] <;> ring

def projectedRow (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  preRow k c q t ᵥ* pairProjection

def lostFlux (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ := (2/3 : ℝ) • firstFlux k c q t

lemma projectedRow_sum (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) :
    (∑ j, projectedRow k c q t j) = survival k c q t := by
  simp [projectedRow, survival, Matrix.vecMul, dotProduct, pairProjection, Fin.sum_univ_succ]
  ring

lemma projectedRow_initial (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    projectedRow k c q 0 = Pi.single 0 1 := by
  unfold projectedRow
  rw [preRow_initial k c q hc hq]
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, pairProjection, Pi.single_apply]

lemma projectedRow_derivative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) (j : Fin 2) :
    HasDerivAt (fun u => projectedRow k c q u j)
      ((projectedRow k c q t ᵥ* MarkovChain.Identifiability.pairGenerator k (c t) (q t) - lostFlux k
          c q t) j) t := by
  have h := finiteRowMatrixProduct_hasDerivAt (preRow k c q)
    (fun u => preRow k c q u ᵥ* threeGenerator k (c u) (q u))
    (fun _ => pairProjection) (fun _ => 0)
    (fun u i => preRow_derivative k c q hc hq u i)
    (fun u i j => hasDerivAt_const u (pairProjection i j)) t j
  simp only [Matrix.vecMul_zero, add_zero] at h
  have hb := congrArg (fun M => preRow k c q t ᵥ* M) (projection_generator k (c t) (q t))
  simp only [Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul] at hb
  apply h.congr_deriv
  exact congrFun (eq_sub_of_add_eq hb) j

lemma lostFlux_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    Continuous (lostFlux k c q) := by
  apply continuous_pi
  intro j
  exact continuous_const.mul (firstFlux_continuous k c q hc hq j)

lemma lostFlux_nonnegative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin 2) : 0 ≤ lostFlux k c q t j :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 2/3) (firstFlux_nonnegative k c q hc hq hcn hqn ht j)

lemma projection_duhamel (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) : projectedRow k c q t +
      (fun j => ∫ u in (0 : ℝ)..t,
        (lostFlux k c q u ᵥ* timeVaryingPairTransition k c q u t) j) =
      timeVaryingPairTransition k c q 0 t 0 := by
  have h := finiteRow_projection_duhamel
      (fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u))
    (SimultaneousOnset.pairGenerator_continuous k c q hc hq)
    (projectedRow k c q) (lostFlux k c q) (lostFlux_continuous k c q hc hq)
    (fun u j => projectedRow_derivative k c q hc hq u j) t
  rw [projectedRow_initial k c q hc hq] at h
  simpa only [Matrix.single_vecMul, one_smul, Matrix.row, timeVaryingPairTransition] using h

theorem survival_le_pair (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) : survival k c q t ≤ timeVaryingPairSurvival k c q 0 0 t := by
  rw [← projectedRow_sum]
  apply Finset.sum_le_sum
  intro j _
  have hi : 0 ≤ ∫ u in (0 : ℝ)..t,
      (lostFlux k c q u ᵥ* timeVaryingPairTransition k c q u t) j := by
    apply intervalIntegral.integral_nonneg ht
    intro u hu
    change 0 ≤ ∑ i, lostFlux k c q u i * timeVaryingPairTransition k c q u t i j
    exact Finset.sum_nonneg fun i _ => mul_nonneg (lostFlux_nonnegative k c q hc hq hcn hqn hu.1 i)
      (timeVaryingPairTransition_nonneg k c q hc hq hqn hu.1 hu.2 i j)
  have he := congrFun (projection_duhamel k c q hc hq t) j
  simp only [Pi.add_apply] at he
  linarith

theorem survival_tendsto_zero_of_pair (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (survival k c q) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hproper
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (survival_positive k c q hc hq hqn ht).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_le_pair k c q hc hq hcn hqn ht

end Rhone.Statistics.Identifiability.ThreeTimeVarying
