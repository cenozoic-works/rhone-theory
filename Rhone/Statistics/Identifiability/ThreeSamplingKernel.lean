/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingNormalized
public import Rhone.Statistics.Identifiability.ThreeIntegrableKernel

/-! # Two-time coalescence kernel with an arbitrary initial occupancy row -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeSampling

def firstDensity (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * (3 * preRow ρ k c q t 0 + preRow ρ k c q t 1)

def firstFlux (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) (j : Fin 2) : ℝ :=
  (preRow ρ k c q t ᵥ* IslandThreeTimes.firstRate (c t)) j

def firstKernel (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) (j : Fin 2) : ℝ :=
  (preRow ρ k c q t ᵥ* IslandThreeTimes.firstRate 1) j

def jointKernel (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, firstKernel ρ k c q p.1 j * timeVaryingPairTransition k c q p.1 p.2 j 0

def jointDensity (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, firstFlux ρ k c q p.1 j * timeVaryingPairExitDensity k c q p.1 j p.2

def law (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  triangularDensityLaw (jointDensity ρ k c q)

def firstLaw (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (firstDensity ρ k c q t))

lemma preRow_continuous (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (i : State) :
    Continuous (fun t => preRow ρ k c q t i) := by
  have hU := integrableTransition_continuous _
    (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq)
  change Continuous (fun t => ∑ j : State,
    ρ j * inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t j i)
  apply continuous_finsetSum
  intro j _
  fun_prop

lemma survival_continuous (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    Continuous (survival ρ k c q) :=
  continuous_finsetSum _ fun i _ => preRow_continuous ρ k c q hc hq i

lemma firstFlux_sum (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) :
    (∑ j, firstFlux ρ k c q t j) = firstDensity ρ k c q t := by
  simp [firstFlux, firstDensity, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    IslandThreeTimes.firstRate]
  ring

lemma firstDensity_locallyIntegrable (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    LocallyIntegrable (firstDensity ρ k c q) volume :=
  hc.mul_continuous ((continuous_const.mul (preRow_continuous ρ k c q hc hq 0)).add
    (preRow_continuous ρ k c q hc hq 1))

lemma firstFlux_nonnegative_at (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) (hct : 0 ≤ c t) (j : Fin 2) :
    0 ≤ firstFlux ρ k c q t j := by
  change 0 ≤ ∑ i, preRow ρ k c q t i * IslandThreeTimes.firstRate (c t) i j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (preRow_nonnegative ρ k c q hρ hc hq hqn ht i)
    (IslandThreeTimes.firstRate_nonneg hct i j)

lemma jointDensity_factor (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (p : ℝ × ℝ) :
    jointDensity ρ k c q p = c p.1 * c p.2 * jointKernel ρ k c q p := by
  simp [jointDensity, firstFlux, jointKernel, firstKernel, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ, IslandThreeTimes.firstRate, timeVaryingPairExitDensity]
  ring

lemma firstKernel_continuous (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (j : Fin 2) :
    Continuous (fun t => firstKernel ρ k c q t j) := by
  change Continuous (fun t => ∑ i, preRow ρ k c q t i * IslandThreeTimes.firstRate 1 i j)
  exact continuous_finsetSum _ fun i _ =>
    (preRow_continuous ρ k c q hc hq i).mul continuous_const

lemma jointKernel_continuous (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    Continuous (jointKernel ρ k c q) := by
  have hU := PairIntegrable.transition_continuous k c q hc hq
  apply continuous_finsetSum
  intro j _
  exact ((firstKernel_continuous ρ k c q hc hq j).comp continuous_fst).mul
    ((continuous_apply 0).comp ((continuous_apply j).comp hU))

lemma jointKernel_trace (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (t : ℝ) :
    jointKernel ρ k c q (t,t) = 3 * preRow ρ k c q t 0 := by
  simp [jointKernel, firstKernel, timeVaryingPairTransition,
    integrableTransition_self _ (PairIntegrable.generator_locallyIntegrable k c q hc hq),
    Matrix.vecMul, dotProduct, Fin.sum_univ_succ, IslandThreeTimes.firstRate]
  ring

lemma jointKernel_nonnegative (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    0 ≤ jointKernel ρ k c q p := by
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · change 0 ≤ ∑ i, preRow ρ k c q p.1 i * IslandThreeTimes.firstRate 1 i j
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (preRow_nonnegative ρ k c q hρ hc hq hqn hp.1.le i)
      (IslandThreeTimes.firstRate_nonneg (by norm_num) i j)
  · exact PairIntegrable.transition_nonnegative k c q hc hq hqn hp.1.le hp.2.le j 0

lemma jointDensity_aemeasurable (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    AEMeasurable (jointDensity ρ k c q) (planeVolume.restrict upperWedge) := by
  have hm : AEMeasurable c volume := hc.aestronglyMeasurable.aemeasurable
  have h1 : AEMeasurable (fun p : ℝ × ℝ => c p.1) (volume.prod volume) := hm.comp_fst
  have h2 : AEMeasurable (fun p : ℝ × ℝ => c p.2) (volume.prod volume) := hm.comp_snd
  have he : jointDensity ρ k c q = fun p => c p.1 * c p.2 * jointKernel ρ k c q p :=
    funext (jointDensity_factor ρ k c q)
  rw [he]
  exact ((h1.mul h2).mul
    (jointKernel_continuous ρ k c q hc hq).measurable.aemeasurable).restrict

end Rhone.Statistics.Identifiability.ThreeSampling
