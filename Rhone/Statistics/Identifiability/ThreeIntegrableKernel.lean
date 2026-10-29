/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableFlux
public import Rhone.Statistics.Identifiability.PairIntegrableFlow

/-! # The continuous normalized two-time kernel behind the locally L1 coalescence weights -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

def firstKernel (k : ℕ) (c q : ℝ → ℝ) (s : ℝ) (j : Fin 2) : ℝ :=
  (preRow k c q s ᵥ* IslandThreeTimes.firstRate 1) j

def jointKernel (k : ℕ) (c q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, firstKernel k c q p.1 j * timeVaryingPairTransition k c q p.1 p.2 j 0

lemma firstKernel_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (j : Fin 2) :
    Continuous (fun t => firstKernel k c q t j) := by
  change Continuous (fun t => ∑ i, preRow k c q t i * IslandThreeTimes.firstRate 1 i j)
  exact continuous_finsetSum _ fun i _ =>
    (preRow_continuous k c q hc hq i).mul continuous_const

lemma jointKernel_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    Continuous (jointKernel k c q) := by
  have hU := PairIntegrable.transition_continuous k c q hc hq
  apply continuous_finsetSum
  intro j _
  exact ((firstKernel_continuous k c q hc hq j).comp continuous_fst).mul
    ((continuous_apply 0).comp ((continuous_apply j).comp hU))

lemma jointDensity_factor (k : ℕ) (c q : ℝ → ℝ) (p : ℝ × ℝ) :
    jointDensity k c q p = c p.1 * c p.2 * jointKernel k c q p := by
  simp [jointDensity, firstFlux, jointKernel, firstKernel, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ, IslandThreeTimes.firstRate, timeVaryingPairExitDensity]
  ring

lemma jointKernel_trace (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (t : ℝ) :
    jointKernel k c q (t,t) = 3 * preRow k c q t 0 := by
  simp [jointKernel, firstKernel, timeVaryingPairTransition,
    integrableTransition_self _ (PairIntegrable.generator_locallyIntegrable k c q hc hq),
    Matrix.vecMul, dotProduct, Fin.sum_univ_succ, IslandThreeTimes.firstRate]
  ring

lemma jointKernel_nonnegative (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    0 ≤ jointKernel k c q p := by
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · change 0 ≤ ∑ i, preRow k c q p.1 i * IslandThreeTimes.firstRate 1 i j
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (preRow_nonnegative k c q hc hq hqn hp.1.le i)
      (IslandThreeTimes.firstRate_nonneg (by norm_num) i j)
  · exact PairIntegrable.transition_nonnegative k c q hc hq hqn hp.1.le hp.2.le j 0

lemma jointDensity_aemeasurable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    AEMeasurable (jointDensity k c q) (planeVolume.restrict upperWedge) := by
  have hm : AEMeasurable c volume := hc.aestronglyMeasurable.aemeasurable
  have h1 : AEMeasurable (fun p : ℝ × ℝ => c p.1) (volume.prod volume) := hm.comp_fst
  have h2 : AEMeasurable (fun p : ℝ × ℝ => c p.2) (volume.prod volume) := hm.comp_snd
  have he : jointDensity k c q = fun p => c p.1 * c p.2 * jointKernel k c q p :=
    funext (jointDensity_factor k c q)
  rw [he]
  exact ((h1.mul h2).mul (jointKernel_continuous k c q hc hq).measurable.aemeasurable).restrict

end Rhone.Statistics.Identifiability.ThreeIntegrable
