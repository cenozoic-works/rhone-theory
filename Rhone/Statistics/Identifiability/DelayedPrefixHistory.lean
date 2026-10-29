/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.NoRecombinationPrefix

/-! # The delayed-onset prefix forms follow from literal zero-mechanism histories -/

@[expose] public section

open Set
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.DelayedOnset
open SimultaneousOnset

lemma extendPair_tensor (v : Fin 2 → ℝ) :
    (fun i : ProductState => extendPair v i.1 * v i.2) =
      recombinationPrefixRow (v 0) (v 1) := by
  funext i
  rcases i with ⟨i,j⟩
  fin_cases j <;> by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp_all [extendPair, recombinationPrefixRow]

theorem recombination_prefix_of_zero_history (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) {a : ℝ} (ha : 0 ≤ a)
    (hz : ∀ u ∈ Icc 0 a, r u = 0) :
    (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2) =
      recombinationPrefixRow (pairRow k c q a 0) (pairRow k c q a 1) := by
  have he := inhomogeneousTransition_eq_of_eqOn
    (fun u => MarkovChain.Identifiability.generator k (c u) (q u) (r u))
    (fun u => MarkovChain.Identifiability.generator k (c u) (q u) 0)
    (preGenerator_continuous k c q r hc hq hr)
    (preGenerator_continuous k c q (fun _ => 0) hc hq continuous_const)
    ha (fun u hu => by dsimp only; rw [hz u hu])
  have hp : preRow k c q r a = extendPair (pairRow k c q a) := by
    rw [← preRow_zero_recombination k c q hc hq a]
    exact congrArg (fun M => M 0) he
  simp_rw [hp]
  exact extendPair_tensor _

theorem migration_prefix_of_zero_history (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) {a : ℝ} (ha : 0 ≤ a)
    (hz : ∀ u ∈ Icc 0 a, q u = 0) :
    (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2) =
      migrationPrefixRow (preRow k c q r a 0) (preRow k c q r a 2)
        (preRow k c q r a 7) (pairRow k c q a 0) := by
  let D := fun u => productGenerator k (c u) (q u) (r u)
  let C := fun u => productGenerator k (c u) 0 (r u)
  have hD := productGenerator_history_continuous k c q r hc hq hr
  have hC := productGenerator_history_continuous k c (fun _ => 0) r hc continuous_const hr
  have he : inhomogeneousTransition D 0 a = inhomogeneousTransition C 0 a :=
    inhomogeneousTransition_eq_of_eqOn D C hD hC ha (fun u hu => by dsimp [D, C]; rw [hz u hu])
  have hclosed (i : ProductState) (hi : ¬zeroMigrationReachable i) :
      preRow k c q r a i.1 * pairRow k c q a i.2 = 0 := by
    rw [← productRow_factorization k c q r hc hq hr a i]
    change inhomogeneousTransition D 0 a (0, 0) i = 0
    rw [he]
    exact inhomogeneousTransition_zero_outside_closed C hC zeroMigrationReachable
      (fun u => zeroMigrationReachable_closed k (c u) (r u)) 0 a (0, 0) i
      zeroMigrationReachable_initial hi
  funext i
  by_cases hi : zeroMigrationReachable i
  · rcases i with ⟨i,j⟩
    rcases hi with ⟨hi, rfl⟩
    rcases hi with rfl | rfl | rfl <;> simp [migrationPrefixRow, mul_comm]
  · rw [hclosed i hi]
    rcases i with ⟨i,j⟩
    by_cases hj : j = 0
    · have h0 : i ≠ 0 := fun h => hi ⟨Or.inl h, hj⟩
      have h2 : i ≠ 2 := fun h => hi ⟨Or.inr (Or.inl h), hj⟩
      have h7 : i ≠ 7 := fun h => hi ⟨Or.inr (Or.inr h), hj⟩
      simp [migrationPrefixRow, h0, h2, h7]
    · simp [migrationPrefixRow, hj]

end Rhone.Statistics.Identifiability.DelayedOnset
