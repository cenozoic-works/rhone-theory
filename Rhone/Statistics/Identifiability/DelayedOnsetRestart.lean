/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedOnsetPositive
public import Rhone.Statistics.Identifiability.FiniteFlowRestart

/-! # Restarting the product witness at an arbitrary finite prefix time -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.DelayedOnset
open SimultaneousOnset

theorem witness_restart (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (a t : ℝ) :
    SimultaneousOnset.witness k c q r (a + t) =
      rowPayoff (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2)
        (inhomogeneousTransition
          (fun u => productGenerator k (c (a + u)) (q (a + u)) (r (a + u))) 0 t)
        witnessVec := by
  rw [witness_eq_product_output k c q r hc hq hr,
    rowPayoff_restart _ (productGenerator_history_continuous k c q r hc hq hr) 0 a t]
  congr 1
  funext i
  exact productRow_factorization k c q r hc hq hr a i

theorem witness_positive_after_recombination_prefix (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {a x y : ℝ} (ha : 0 ≤ a)
    (hx : 0 < x) (hy : 0 < y)
    (hprefix : (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2) =
      recombinationPrefixRow x y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      (0 < ∫ u in (0 : ℝ)..t, r (a + u)) → 0 < SimultaneousOnset.witness k c q r (a + t) := by
  obtain ⟨δ, hδ, hpos⟩ := recombination_prefix_positive_near_onset k
    (fun u => c (a + u)) (fun u => q (a + u)) (fun u => r (a + u))
    (hc.comp (continuous_const.add continuous_id))
    (hq.comp (continuous_const.add continuous_id))
    (hr.comp (continuous_const.add continuous_id))
    (fun u hu => hcn _ (add_nonneg ha hu))
    (fun u hu => hqn _ (add_nonneg ha hu))
    (fun u hu => hrn _ (add_nonneg ha hu)) hx hy
  refine ⟨δ, hδ, fun t ht htδ hexp => ?_⟩
  rw [witness_restart k c q r hc hq hr, hprefix]
  exact hpos t ht htδ hexp

theorem witness_positive_after_migration_prefix (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {a b S : ℝ} (ha : 0 ≤ a)
    (x z : ℝ) (hb : 0 < b) (hS : 0 < S)
    (hprefix : (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2) =
      migrationPrefixRow x b z S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      (0 < ∫ u in (0 : ℝ)..t, q (a + u)) → 0 < SimultaneousOnset.witness k c q r (a + t) := by
  obtain ⟨δ, hδ, hpos⟩ := migration_prefix_positive_near_onset k
    (fun u => c (a + u)) (fun u => q (a + u)) (fun u => r (a + u))
    (hc.comp (continuous_const.add continuous_id))
    (hq.comp (continuous_const.add continuous_id))
    (hr.comp (continuous_const.add continuous_id))
    (fun u hu => hcn _ (add_nonneg ha hu))
    (fun u hu => hqn _ (add_nonneg ha hu))
    (fun u hu => hrn _ (add_nonneg ha hu)) x z hb hS
  refine ⟨δ, hδ, fun t ht htδ hexp => ?_⟩
  rw [witness_restart k c q r hc hq hr, hprefix]
  exact hpos t ht htδ hexp

end Rhone.Statistics.Identifiability.DelayedOnset
