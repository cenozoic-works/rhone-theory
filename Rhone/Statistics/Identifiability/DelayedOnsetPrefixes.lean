/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SingleMechanismPayoff
public import Rhone.Statistics.Identifiability.SimultaneousOnsetFlow

/-! # Exact prefix payoffs for the two delayed-mechanism onset orders -/

@[expose] public section

open Set
open scoped BigOperators Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rowPayoff_single (i : ι) (a : ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    rowPayoff (Pi.single i a) M v = a * (M *ᵥ v) i := by
  simp [rowPayoff, Pi.single_apply]

omit [DecidableEq ι] in
lemma rowPayoff_add (ρ σ : ι → ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    rowPayoff (ρ + σ) M v = rowPayoff ρ M v + rowPayoff σ M v := by
  simp only [rowPayoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]

namespace DelayedOnset
open SimultaneousOnset

noncomputable def recombinationPrefixRow (x y : ℝ) : ProductState → ℝ :=
  Pi.single (0, 0) (x*x) + Pi.single (0, 1) (x*y) +
    Pi.single (1, 0) (y*x) + Pi.single (1, 1) (y*y)

noncomputable def migrationPrefixRow (x b z S : ℝ) : ProductState → ℝ :=
  Pi.single (0, 0) (S*x) + Pi.single (2, 0) (S*b) + Pi.single (7, 0) (S*z)

lemma recombinationMark_witness_one_one (k : ℕ) :
    (recombinationMark k *ᵥ witnessVec) (1, 1) = 0 := by
  rw [recombinationMark, productGenerator_mulVec]
  simp [MarkovChain.Identifiability.generator, MarkovChain.Identifiability.pairGenerator,
      MarkovChain.Identifiability.totalMigration, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, MarkovChain.Identifiability.recombinationTable, witnessVec,
        MarkovChain.Identifiability.firstATable, MarkovChain.Identifiability.firstAThenBTable]

lemma migrationMark_witness_seven_zero (k : ℕ) :
    (migrationMark k *ᵥ witnessVec) (7, 0) = 0 := by
  have hn : k + 2 - 1 = k + 1 := by omega
  rw [migrationMark, productGenerator_mulVec]
  simp [MarkovChain.Identifiability.generator, MarkovChain.Identifiability.pairGenerator,
      MarkovChain.Identifiability.totalMigration, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, MarkovChain.Identifiability.occupiedTable,
        MarkovChain.Identifiability.emptyTable, MarkovChain.Identifiability.occupiedDemes, hn,
    witnessVec, MarkovChain.Identifiability.firstATable,
        MarkovChain.Identifiability.firstAThenBTable]
  ring

theorem recombination_prefix_leading (k : ℕ) (x y : ℝ) :
    rowPayoff (recombinationPrefixRow x y) (recombinationMark k) witnessVec = 2*x*y := by
  simp only [recombinationPrefixRow, rowPayoff_add, rowPayoff_single,
    recombinationMark_witness_initial, recombinationMark_witness_zero_one,
    recombinationMark_witness_one_zero, recombinationMark_witness_one_one]
  ring

theorem migration_prefix_leading (k : ℕ) (x b z S : ℝ) :
    rowPayoff (migrationPrefixRow x b z S) (migrationMark k) witnessVec =
      S*b*(k+1 : ℝ) := by
  simp only [migrationPrefixRow, rowPayoff_add, rowPayoff_single,
    migrationMark_witness_initial, migrationMark_witness_two_zero,
    migrationMark_witness_seven_zero]
  ring

lemma recombination_prefix_base_zero (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (x y s t : ℝ) :
    rowPayoff (recombinationPrefixRow x y)
      (inhomogeneousTransition (fun u => productGenerator k (c u) (q u) 0) s t)
      witnessVec = 0 := by
  have h (i : ProductState) (hi : zeroRecombinationReachable i) :
      (inhomogeneousTransition (fun u => productGenerator k (c u) (q u) 0) s t *ᵥ
        witnessVec) i = 0 :=
    inhomogeneousTransition_mulVec_zero_of_closed _
      (productGenerator_history_continuous k c q (fun _ => 0) hc hq continuous_const)
      zeroRecombinationReachable (fun u => zeroRecombinationReachable_closed k (c u) (q u))
      witnessVec zeroRecombinationReachable_witness s t i hi
  simp only [recombinationPrefixRow, rowPayoff_add, rowPayoff_single]
  rw [h (0, 0) (by simp [zeroRecombinationReachable]),
    h (0, 1) (by simp [zeroRecombinationReachable]),
    h (1, 0) (by simp [zeroRecombinationReachable]),
    h (1, 1) (by simp [zeroRecombinationReachable])]
  ring

lemma migration_prefix_base_zero (k : ℕ) (c r : ℝ → ℝ)
    (hc : Continuous c) (hr : Continuous r) (x b z S s t : ℝ) :
    rowPayoff (migrationPrefixRow x b z S)
      (inhomogeneousTransition (fun u => productGenerator k (c u) 0 (r u)) s t)
      witnessVec = 0 := by
  have h (i : ProductState) (hi : zeroMigrationReachable i) :
      (inhomogeneousTransition (fun u => productGenerator k (c u) 0 (r u)) s t *ᵥ
        witnessVec) i = 0 :=
    inhomogeneousTransition_mulVec_zero_of_closed _
      (productGenerator_history_continuous k c (fun _ => 0) r hc continuous_const hr)
      zeroMigrationReachable (fun u => zeroMigrationReachable_closed k (c u) (r u))
      witnessVec zeroMigrationReachable_witness s t i hi
  simp only [migrationPrefixRow, rowPayoff_add, rowPayoff_single]
  rw [h (0, 0) (by simp [zeroMigrationReachable]),
    h (2, 0) (by simp [zeroMigrationReachable]),
    h (7, 0) (by simp [zeroMigrationReachable])]
  ring

end DelayedOnset
end Rhone.Statistics.Identifiability
