/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedPrefixMasses
public import Rhone.Statistics.Identifiability.TimeVaryingPairExitKernel

/-! # Proper pair tails propagate through the exact finite-state cocycle -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.PairProperness

lemma survival_nonnegative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : Fin 2) :
    0 ≤ timeVaryingPairSurvival k c q s i t :=
  Finset.sum_nonneg fun j _ => timeVaryingPairTransition_nonneg k c q hc hq hqn hs hst i j

lemma survival_restart (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (s u t : ℝ) (i : Fin 2) :
    timeVaryingPairSurvival k c q s i t =
      ∑ j, timeVaryingPairTransition k c q s u i j * timeVaryingPairSurvival k c q u j t := by
  unfold timeVaryingPairSurvival timeVaryingPairTransition
  rw [inhomogeneousTransition_cocycle _ (SimultaneousOnset.pairGenerator_continuous k c q hc hq)
    s u t]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem proper_at_reached_state (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {s : ℝ} (hs : 0 ≤ s) (j : Fin 2)
    (hp : 0 < timeVaryingPairTransition k c q 0 s 0 j) :
    Tendsto (timeVaryingPairSurvival k c q s j) atTop (𝓝 0) := by
  have hlim := hproper.div_const (timeVaryingPairTransition k c q 0 s 0 j)
  simp only [zero_div] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop s] with t ht
    exact survival_nonnegative k c q hc hq hqn hs ht j
  · filter_upwards [eventually_ge_atTop s] with t ht
    apply (le_div_iff₀ hp).mpr
    rw [survival_restart k c q hc hq 0 s t 0]
    rw [mul_comm]
    exact Finset.single_le_sum
      (fun l _ => mul_nonneg (timeVaryingPairTransition_nonneg k c q hc hq hqn le_rfl hs 0 l)
        (survival_nonnegative k c q hc hq hqn hs ht l)) (Finset.mem_univ j)

theorem proper_at_every_restart (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (a : ℝ)
    (ha : ∀ j : Fin 2, Tendsto (timeVaryingPairSurvival k c q a j) atTop (𝓝 0))
    (s : ℝ) (i : Fin 2) : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun j _ =>
    (ha j).const_mul (timeVaryingPairTransition k c q s a i j))
  simp only [mul_zero, Finset.sum_const_zero] at h
  have he : timeVaryingPairSurvival k c q s i =
      fun t => ∑ j, timeVaryingPairTransition k c q s a i j *
        timeVaryingPairSurvival k c q a j t := by
    funext t
    exact survival_restart k c q hc hq s a t i
  rwa [he]

theorem all_pair_tails_of_initial_proper (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hQ : 0 < ∫ u in (0 : ℝ)..a, q u) :
    ∀ s : ℝ, ∀ i : Fin 2, Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0) := by
  have hpa (j : Fin 2) : Tendsto (timeVaryingPairSurvival k c q a j) atTop (𝓝 0) := by
    apply proper_at_reached_state k c q hc hq hqn hproper ha j
    fin_cases j
    · exact DelayedOnset.pairRow_together_positive k c q hc hq hqn ha
    · exact DelayedOnset.pairRow_apart_positive k c q hc hq hqn ha hQ
  exact proper_at_every_restart k c q hc hq a hpa

end Rhone.Statistics.Identifiability.PairProperness
