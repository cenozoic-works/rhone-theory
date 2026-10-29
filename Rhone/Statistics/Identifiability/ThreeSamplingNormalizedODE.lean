/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingNormalized

/-! # Normalized occupancy derivatives for arbitrary initial sampling -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeSampling

lemma normalizedX_derivative_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (normalizedX ρ k c q)
      (xDrift (c t) (q t) (k + 2) (normalizedX ρ k c q t) (normalizedY ρ k c q t)) t := by
  filter_upwards [preRow_derivative_ae ρ k c q hc hq,
    survival_derivative_ae ρ k c q hc hq] with t hrow hsurv ht
  have hs := (survival_positive ρ k c q hρ hρsum hc hq hqn ht).ne'
  change HasDerivAt (fun u =>
    (3 * preRow ρ k c q u 0 + preRow ρ k c q u 1) / (3 * survival ρ k c q u)) _ t
  apply (((hrow 0).const_mul 3).add (hrow 1)).div (hsurv.const_mul 3)
    (mul_ne_zero (by norm_num) hs) |>.congr_deriv
  unfold xDrift normalizedX normalizedY
  field_simp [hs]
  simp [survival, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, threeGenerator,
      MarkovChain.Identifiability.totalMigration]
  ring

lemma normalizedY_derivative_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (normalizedY ρ k c q)
      (yDrift (c t) (q t) (k + 2) (normalizedX ρ k c q t) (normalizedY ρ k c q t)) t := by
  filter_upwards [preRow_derivative_ae ρ k c q hc hq,
    survival_derivative_ae ρ k c q hc hq] with t hrow hsurv ht
  have hs := (survival_positive ρ k c q hρ hρsum hc hq hqn ht).ne'
  change HasDerivAt (fun u => preRow ρ k c q u 0 / survival ρ k c q u) _ t
  apply ((hrow 0).div hsurv hs).congr_deriv
  unfold yDrift normalizedX normalizedY
  field_simp [hs]
  simp [survival, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, threeGenerator,
      MarkovChain.Identifiability.totalMigration]
  ring

end Rhone.Statistics.Identifiability.ThreeSampling
