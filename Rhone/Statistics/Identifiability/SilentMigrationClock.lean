/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentIslandMigrationKernel
public import Rhone.Statistics.Identifiability.SilentFirstSplitClock

/-! # Time-dependent symmetric migration supplies the normalized first-split daughter rows -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.SilentWindow

def migrationClock (k : ℕ) (q : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (-(k + 2 : ℝ) * (integratedClock q t - integratedClock q s))

lemma migrationClock_positive (k : ℕ) (q : ℝ → ℝ) (s t : ℝ) :
    0 < migrationClock k q s t := Real.exp_pos _

lemma migrationClock_compose (k : ℕ) (q : ℝ → ℝ) (s u t : ℝ) :
    migrationClock k q s u * migrationClock k q u t = migrationClock k q s t := by
  rw [migrationClock, migrationClock, migrationClock, ← Real.exp_add]
  congr 1
  ring

lemma migrationClock_continuous_start (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q) (t : ℝ) :
    Continuous (fun s => migrationClock k q s t) :=
  Real.continuous_exp.comp (continuous_const.mul
    (continuous_const.sub (integratedClock_continuous q hq.locallyIntegrable)))

lemma migrationClock_continuous_end (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q) (s : ℝ) :
    Continuous (migrationClock k q s) :=
  Real.continuous_exp.comp (continuous_const.mul
    ((integratedClock_continuous q hq.locallyIntegrable).sub continuous_const))

lemma migrationClock_le_one (k : ℕ) (q : ℝ → ℝ) (hq : Continuous q)
    (hqn : ∀ u, 0 ≤ u → 0 ≤ q u) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    migrationClock k q s t ≤ 1 := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hq.intervalIntegrable 0 s) (hq.intervalIntegrable s t)
  have hn : 0 ≤ ∫ u in s..t, q u :=
    intervalIntegral.integral_nonneg hst (fun u hu => hqn u (hs.trans hu.1))
  have hd : 0 ≤ integratedClock q t - integratedClock q s := by
    unfold integratedClock
    linarith
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd

lemma migrationClock_lt_one_of_exposure (k : ℕ) (q : ℝ → ℝ) {t : ℝ}
    (hexp : 0 < integratedClock q t) : migrationClock k q 0 t < 1 := by
  apply Real.exp_lt_one_iff.mpr
  simp only [integratedClock, intervalIntegral.integral_same, sub_zero] at hexp ⊢
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hexp

lemma islandRow_nonneg (k : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (x i : Fin (k + 2)) : 0 ≤ islandRow k z x i := by
  have hp : 0 ≤ (1 - z) / (k + 2 : ℝ) := div_nonneg (sub_nonneg.mpr hz1) (by positivity)
  by_cases h : x = i <;> simp only [islandRow, h, ite_true, ite_false, mul_one, mul_zero]
  · exact add_nonneg hz hp
  · simpa using hp

lemma islandRow_le_one (k : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (x i : Fin (k + 2)) : islandRow k z x i ≤ 1 := by
  rw [← islandRow_sum k z x]
  exact Finset.single_le_sum (fun j _ => islandRow_nonneg k hz hz1 x j) (Finset.mem_univ i)

lemma migration_mixture_mean (k : ℕ) (q : ℝ → ℝ) (s u t : ℝ) (x : Fin (k + 2)) :
    mixtureMean (islandRow k (migrationClock k q s u) x)
      (islandRow k (migrationClock k q u t)) = islandRow k (migrationClock k q s t) x := by
  funext j
  rw [mixtureMean, islandRow_compose, migrationClock_compose]

end Rhone.Statistics.Identifiability.SilentWindow
