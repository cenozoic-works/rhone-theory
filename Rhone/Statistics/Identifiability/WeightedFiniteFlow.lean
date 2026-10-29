/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteFlowRestart
public import Rhone.Statistics.Identifiability.TimeVaryingProjectionDuhamel

/-! # Weighted finite-flow rows and their fixed-payoff derivatives -/

@[expose] public section

noncomputable section
open Set
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightedRow (Q : ℝ → Matrix ι ι ℝ) (ρ : ι → ℝ) (t : ℝ) : ι → ℝ :=
  ρ ᵥ* inhomogeneousTransition Q 0 t

lemma weightedRow_initial (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (ρ : ι → ℝ) : weightedRow Q ρ 0 = ρ := by
  simp [weightedRow, inhomogeneousTransition_self Q hQ]

lemma weightedRow_derivative (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (ρ : ι → ℝ) (t : ℝ) (j : ι) :
    HasDerivAt (fun u => weightedRow Q ρ u j) ((weightedRow Q ρ t ᵥ* Q t) j) t := by
  have h := finiteRowMatrixProduct_hasDerivAt (fun _ => ρ) (fun _ => 0)
    (inhomogeneousTransition Q 0) (fun u => inhomogeneousTransition Q 0 u * Q u)
    (fun u i => hasDerivAt_const u (ρ i))
    (fun u i j => inhomogeneousTransition_hasDerivAt_right Q hQ 0 u i j) t j
  simpa only [Matrix.zero_vecMul, zero_add, Matrix.vecMul_vecMul, weightedRow] using h

lemma weightedRow_nonnegative (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hQn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) {t : ℝ} (ht : 0 ≤ t) (j : ι) :
    0 ≤ weightedRow Q ρ t j := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hρ i) (inhomogeneousTransition_nonneg Q hQ hQn le_rfl ht i j)

lemma weightedRow_payoff (Q : ℝ → Matrix ι ι ℝ) (ρ v : ι → ℝ) (t : ℝ) :
    rowPayoff ρ (inhomogeneousTransition Q 0 t) v = weightedRow Q ρ t ⬝ᵥ v :=
  Matrix.dotProduct_mulVec _ _ _

lemma weightedRow_payoff_derivative (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (ρ v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u => weightedRow Q ρ u ⬝ᵥ v)
      (weightedRow Q ρ t ⬝ᵥ (Q t *ᵥ v)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (weightedRow_derivative Q hQ ρ t j).mul_const (v j))
  change HasDerivAt (fun u => weightedRow Q ρ u ⬝ᵥ v)
    ((weightedRow Q ρ t ᵥ* Q t) ⬝ᵥ v) t at h
  rwa [← Matrix.dotProduct_mulVec] at h

end Rhone.Statistics.Identifiability.SilentWindow
