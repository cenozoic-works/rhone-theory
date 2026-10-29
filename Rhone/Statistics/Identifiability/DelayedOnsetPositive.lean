/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedOnsetPrefixes
public import Rhone.Statistics.Identifiability.SingleMechanismPositive
public import Rhone.Statistics.Identifiability.SimultaneousOnsetBounds

/-! # Finite-generator payoff positivity for both delayed onset prefix types -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.DelayedOnset
open SimultaneousOnset

theorem recombination_prefix_positive_near_onset (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → (0 < ∫ u in (0 : ℝ)..t, r u) →
      0 < rowPayoff (recombinationPrefixRow x y)
        (inhomogeneousTransition (fun u => productGenerator k (c u) (q u) (r u)) 0 t)
        witnessVec := by
  obtain ⟨K, hK, _, hM, _, hD⟩ :=
    exists_common_contractiveBound k c q r hc hq hr hcn hqn hrn
  let C := fun u => productGenerator k (c u) (q u) 0
  have he : C + (fun u => r u • recombinationMark k) =
      fun u => productGenerator k (c u) (q u) (r u) := by
    funext u
    simp only [C, Pi.add_apply, productGenerator_affine, zero_smul, add_zero]
  have h := rowPayoff_positive_near_single_onset C r (recombinationMark k)
    (recombinationPrefixRow x y) witnessVec
    (productGenerator_history_continuous k c q (fun _ => 0) hc hq continuous_const)
    hr hrn hK hM (he.symm ▸ hD)
    (fun t => recombination_prefix_base_zero k c q hc hq x y 0 t)
    (by rw [recombination_prefix_leading]; positivity)
  simpa only [he] using h

theorem migration_prefix_positive_near_onset (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) (x z : ℝ) {b S : ℝ} (hb : 0 < b) (hS : 0 < S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → (0 < ∫ u in (0 : ℝ)..t, q u) →
      0 < rowPayoff (migrationPrefixRow x b z S)
        (inhomogeneousTransition (fun u => productGenerator k (c u) (q u) (r u)) 0 t)
        witnessVec := by
  obtain ⟨K, hK, _, _, hR, hD⟩ :=
    exists_common_contractiveBound k c q r hc hq hr hcn hqn hrn
  let C := fun u => productGenerator k (c u) 0 (r u)
  have he : C + (fun u => q u • migrationMark k) =
      fun u => productGenerator k (c u) (q u) (r u) := by
    funext u
    simp only [C, Pi.add_apply, productGenerator_affine, zero_smul, add_zero]
    abel
  have h := rowPayoff_positive_near_single_onset C q (migrationMark k)
    (migrationPrefixRow x b z S) witnessVec
    (productGenerator_history_continuous k c (fun _ => 0) r hc continuous_const hr)
    hq hqn hK hR (he.symm ▸ hD)
    (fun t => migration_prefix_base_zero k c r hc hr x b z S 0 t)
    (by rw [migration_prefix_leading]; positivity)
  simpa only [he] using h

end Rhone.Statistics.Identifiability.DelayedOnset
