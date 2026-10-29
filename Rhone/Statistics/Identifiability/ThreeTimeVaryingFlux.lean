/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSilentWindow
public import Rhone.Statistics.Identifiability.IslandThreeJointTimes
public import Rhone.Statistics.Identifiability.TimeVaryingPairExitKernel

/-! # First-merger flux and ordered first/root density for time-varying islands -/

@[expose] public section

noncomputable section
open Set Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma preRow_derivative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) (i : ThreeState) :
    HasDerivAt (fun u => preRow k c q u i) ((preRow k c q t ᵥ* threeGenerator k (c t) (q t)) i) t :=
  inhomogeneousTransition_hasDerivAt_right _ (preGenerator_continuous k c q hc hq) 0 t 0 i

lemma preRow_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (i : ThreeState) : Continuous (fun t => preRow k c q t i) :=
  continuous_iff_continuousAt.mpr fun t => (preRow_derivative k c q hc hq t i).continuousAt

lemma preRow_nonnegative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) (i : ThreeState) :
    0 ≤ preRow k c q t i :=
  inhomogeneousTransition_nonneg _ (preGenerator_continuous k c q hc hq)
    (fun u hu => threeGenerator_metzler k (c u) (hqn u hu)) le_rfl ht 0 i

lemma preRow_initial (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    preRow k c q 0 = Pi.single 0 1 := by
  ext i
  fin_cases i <;>
    simp [preRow, inhomogeneousTransition_self _ (preGenerator_continuous k c q hc hq)]

lemma survival_initial (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    survival k c q 0 = 1 := by
  simp only [survival, preRow_initial k c q hc hq]
  simp

lemma survival_positive (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) : 0 < survival k c q t := by
  exact (initial_pre_coordinate_positive k c q hc hq hqn ht).trans_le
    (Finset.single_le_sum (fun i _ => preRow_nonnegative k c q hc hq hqn ht i) (Finset.mem_univ 0))

lemma survival_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    Continuous (survival k c q) :=
  continuous_finsetSum _ (fun i _ => preRow_continuous k c q hc hq i)

def firstDensity (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * ∑ i, preRow k c q t i * mergerWeight i

def firstFlux (k : ℕ) (c q : ℝ → ℝ) (s : ℝ) (j : Fin 2) : ℝ :=
  (preRow k c q s ᵥ* IslandThreeTimes.firstRate (c s)) j

lemma firstFlux_sum (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) :
    (∑ j, firstFlux k c q t j) = firstDensity k c q t := by
  simp [firstFlux, firstDensity, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    IslandThreeTimes.firstRate, mergerWeight]
  ring

lemma firstFlux_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin 2) : 0 ≤ firstFlux k c q t j := by
  change 0 ≤ ∑ i, preRow k c q t i * IslandThreeTimes.firstRate (c t) i j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (preRow_nonnegative k c q hc hq hqn ht i)
    (IslandThreeTimes.firstRate_nonneg (hcn t ht) i j)

lemma firstDensity_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ firstDensity k c q t := by
  rw [← firstFlux_sum]
  exact Finset.sum_nonneg fun j _ => firstFlux_nonnegative k c q hc hq hcn hqn ht j

lemma firstDensity_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    Continuous (firstDensity k c q) := by
  unfold firstDensity
  exact hc.mul (continuous_finsetSum _ (fun i _ => (preRow_continuous k c q hc hq i).mul
    continuous_const))

lemma firstFlux_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (j : Fin 2) : Continuous (fun t => firstFlux k c q t j) := by
  fin_cases j
  · change Continuous (fun t => firstFlux k c q t 0)
    have he : (fun t => firstFlux k c q t 0) = fun t => preRow k c q t 0 * (3 * c t) := by
      funext t
      simp [firstFlux, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, IslandThreeTimes.firstRate]
    rw [he]
    exact (preRow_continuous k c q hc hq 0).mul (continuous_const.mul hc)
  · change Continuous (fun t => firstFlux k c q t 1)
    have he : (fun t => firstFlux k c q t 1) = fun t => preRow k c q t 1 * c t := by
      funext t
      simp [firstFlux, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, IslandThreeTimes.firstRate]
    rw [he]
    exact (preRow_continuous k c q hc hq 1).mul hc

lemma survival_derivative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) : HasDerivAt (survival k c q) (-firstDensity k c q t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => preRow_derivative k c q hc hq t i)
  apply h.congr_deriv
  simp [firstDensity, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    threeGenerator, MarkovChain.Identifiability.totalMigration, mergerWeight]
  ring

def jointDensity (k : ℕ) (c q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, firstFlux k c q p.1 j * timeVaryingPairExitDensity k c q p.1 j p.2

lemma jointDensity_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    Continuous (jointDensity k c q) := by
  apply continuous_finsetSum
  intro j _
  exact ((firstFlux_continuous k c q hc hq j).comp continuous_fst).mul
    (timeVaryingPairExitDensity_continuous k c q hc hq j)

lemma jointDensity_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {p : ℝ × ℝ} (hp : p ∈ upperWedge) : 0 ≤ jointDensity k c q p :=
  Finset.sum_nonneg fun j _ => mul_nonneg
    (firstFlux_nonnegative k c q hc hq hcn hqn hp.1.le j)
    (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hp.1.le hp.2.le j)

lemma jointDensity_trace (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) : jointDensity k c q (t,t) = 3 * (c t)^2 * preRow k c q t 0 := by
  simp [jointDensity, firstFlux, timeVaryingPairExitDensity,
    timeVaryingPairTransition_self k c q hc hq, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ, IslandThreeTimes.firstRate]
  ring

theorem observable_witness_identity (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) : 3 * survival k c q t * jointDensity k c q (t,t) - (firstDensity k c q t)^2 =
      (c t)^2 * witness k c q t := by
  rw [jointDensity_trace k c q hc hq]
  unfold firstDensity witness
  ring

end Rhone.Statistics.Identifiability.ThreeTimeVarying
