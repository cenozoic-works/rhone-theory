/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentRecombinationMark
public import Rhone.Statistics.Identifiability.WeightedFiniteFlow
public import Rhone.Statistics.Identifiability.PositiveForcing
public import Rhone.Statistics.Identifiability.SimultaneousOnsetBounds

/-! # Product-flow positivity throughout a coalescence- and migration-free window -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
open SimultaneousOnset

theorem pure_recombination_payoff_positive (k : ℕ) (r : ℝ → ℝ)
    (hr : Continuous r) (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) (ρ : ProductState → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρp : 0 < ρ (0, 1)) (hstart : 0 ≤ ρ ⬝ᵥ witnessVec)
    {T : ℝ} (hT : 0 ≤ T) (hR : 0 < ∫ u in (0 : ℝ)..T, r u) :
    0 < rowPayoff ρ
      (inhomogeneousTransition (fun u => productGenerator k 0 0 (r u)) 0 T) witnessVec := by
  let Q := fun u => productGenerator k 0 0 (r u)
  have hQ := productGenerator_history_continuous k (fun _ => 0) (fun _ => 0) r
    continuous_const continuous_const hr
  have hQn (u : ℝ) (hu : 0 ≤ u) := productGenerator_metzler k le_rfl le_rfl (hrn u hu)
  have hvn (u : ℝ) (hu : 0 ≤ u) (i : ProductState) : 0 ≤ weightedRow Q ρ u i :=
    weightedRow_nonnegative Q hQ hQn ρ hρ hu i
  have hvp (u : ℝ) (hu : 0 ≤ u) : 0 < weightedRow Q ρ u (0, 1) := by
    apply inhomogeneous_row_coordinate_positive Q (weightedRow Q ρ) (0, 1)
      (hQ _ _) (fun s hs i hi => hQn s hs i (0, 1) hi)
      (fun s _ => weightedRow_derivative Q hQ ρ s (0, 1)) hvn _ hu
    simpa only [weightedRow_initial Q hQ ρ] using hρp
  have hvc : Continuous (fun u => weightedRow Q ρ u (0, 1)) :=
    continuous_iff_continuousAt.mpr fun u => (weightedRow_derivative Q hQ ρ u (0, 1)).continuousAt
  have hd (u : ℝ) : HasDerivAt (fun s => weightedRow Q ρ s ⬝ᵥ witnessVec)
      (2 * r u * weightedRow Q ρ u (0, 1)) u := by
    convert weightedRow_payoff_derivative Q hQ ρ witnessVec u using 1
    simp only [Q, productGenerator_affine, zero_smul, zero_add, Matrix.smul_mulVec,
      recombinationMark_witness]
    simp [dotProduct, Pi.single_apply]
    ring
  have hpos := intervalIntegral_positive_weight r (fun u => weightedRow Q ρ u (0, 1))
    hr hvc hT (fun u hu => hrn u hu.1) (fun u hu => hvp u hu.1) hR
  have hbint : 0 < ∫ u in (0 : ℝ)..T, 2 * r u * weightedRow Q ρ u (0, 1) := by
    have he (u : ℝ) : 2 * r u * weightedRow Q ρ u (0, 1) =
        2 * (weightedRow Q ρ u (0, 1) * r u) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    positivity
  rw [weightedRow_payoff]
  apply linear_forcing_positive (fun _ => 0)
    (fun u => 2 * r u * weightedRow Q ρ u (0, 1))
    (fun u => weightedRow Q ρ u ⬝ᵥ witnessVec) continuous_const
    ((continuous_const.mul hr).mul hvc) _ hT _ _ hbint
  · intro u
    simpa only [zero_mul, zero_add] using hd u
  · simpa only [weightedRow_initial Q hQ ρ] using hstart
  · intro u hu
    exact mul_nonneg (mul_nonneg (by norm_num) (hrn u hu.1)) (hvn u hu.1 (0, 1))

end Rhone.Statistics.Identifiability.SilentWindow
