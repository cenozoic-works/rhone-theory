/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SimultaneousOnsetCertificates
public import Rhone.Statistics.Identifiability.FiniteProductFlow

/-! # The product-chain payoff is the unnormalized simultaneous-onset witness -/

@[expose] public section

open Set Filter
open scoped BigOperators Topology Matrix
open Rhone.MarkovChain.Identifiability Rhone.Statistics.Identifiability
namespace Rhone.Statistics.Identifiability.SimultaneousOnset

noncomputable def preRow (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ) : State → ℝ :=
  inhomogeneousTransition (fun u => generator k (c u) (q u) (r u)) 0 t 0

noncomputable def pairRow (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  inhomogeneousTransition (fun u => pairGenerator k (c u) (q u)) 0 t 0

noncomputable def witness (k : ℕ) (c q r : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∑ j, pairRow k c q t j) * (∑ i, preRow k c q r t i * (firstAThenBTable i : ℝ)) -
    pairRow k c q t 0 * (∑ i, preRow k c q r t i * (firstATable i : ℝ))

theorem preGenerator_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    ∀ i j, Continuous (fun u => generator k (c u) (q u) (r u) i j) := by
  intro i j; dsimp [generator]; fun_prop

theorem pairGenerator_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) :
    ∀ i j, Continuous (fun u => pairGenerator k (c u) (q u) i j) := by
  intro i j; fin_cases i <;> fin_cases j <;> dsimp [pairGenerator, totalMigration] <;> fun_prop

theorem productGenerator_history_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    ∀ i j, Continuous (fun u => productGenerator k (c u) (q u) (r u) i j) := by
  intro i j
  exact ((preGenerator_continuous k c q r hc hq hr i.1 j.1).mul continuous_const).add
    (continuous_const.mul (pairGenerator_continuous k c q hc hq i.2 j.2))

theorem productRow_factorization (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) (j : ProductState) :
    inhomogeneousTransition (fun u => productGenerator k (c u) (q u) (r u)) 0 t (0, 0) j =
      preRow k c q r t j.1 * pairRow k c q t j.2 :=
  inhomogeneousTransition_product _ _ (preGenerator_continuous k c q r hc hq hr)
    (pairGenerator_continuous k c q hc hq) 0 t (0, 0) j

theorem witness_eq_product_output (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    witness k c q r t =
      (inhomogeneousTransition (fun u => productGenerator k (c u) (q u) (r u)) 0 t *ᵥ
        witnessVec) (0, 0) := by
  simp only [Matrix.mulVec, dotProduct, productRow_factorization k c q r hc hq hr,
    Fintype.sum_prod_type, witnessVec, Fin.sum_univ_two, witness]
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, mul_one, mul_zero, sub_zero,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [add_mul, Finset.mul_sum, mul_assoc, mul_left_comm, Finset.sum_add_distrib]
  ring

theorem product_output_zero_migration (k : ℕ) (c r : ℝ → ℝ)
    (hc : Continuous c) (hr : Continuous r) (t : ℝ) :
    (inhomogeneousTransition (fun u => productGenerator k (c u) 0 (r u)) 0 t *ᵥ
      witnessVec) (0, 0) = 0 := by
  classical
  exact inhomogeneousTransition_mulVec_zero_of_closed _
    (productGenerator_history_continuous k c (fun _ => 0) r hc continuous_const hr)
    zeroMigrationReachable (fun u => zeroMigrationReachable_closed k (c u) (r u))
    witnessVec zeroMigrationReachable_witness 0 t (0, 0) zeroMigrationReachable_initial

theorem product_output_zero_recombination (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (t : ℝ) :
    (inhomogeneousTransition (fun u => productGenerator k (c u) (q u) 0) 0 t *ᵥ
      witnessVec) (0, 0) = 0 := by
  classical
  exact inhomogeneousTransition_mulVec_zero_of_closed _
    (productGenerator_history_continuous k c q (fun _ => 0) hc hq continuous_const)
    zeroRecombinationReachable (fun u => zeroRecombinationReachable_closed k (c u) (q u))
    witnessVec zeroRecombinationReachable_witness 0 t (0, 0) zeroRecombinationReachable_initial

end Rhone.Statistics.Identifiability.SimultaneousOnset
