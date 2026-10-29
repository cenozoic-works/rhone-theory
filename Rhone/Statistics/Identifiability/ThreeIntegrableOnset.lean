/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkedOnset
public import Rhone.Statistics.Identifiability.IntegrableProductFlow
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingWitness

/-! # Three-sample witness positivity for locally L1 migration histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma preGenerator_affine (k : ℕ) (c q : ℝ) :
    threeGenerator k c q = c • threeGenerator k 1 0 + q • threeGenerator k 0 1 := by
  ext i j
  change threeGenerator k c q i j =
    c * threeGenerator k 1 0 i j + q * threeGenerator k 0 1 i j
  fin_cases i <;> fin_cases j <;> simp
      [threeGenerator, MarkovChain.Identifiability.totalMigration] <;> ring

lemma preGenerator_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ i j, LocallyIntegrable (fun t => threeGenerator k (c t) (q t) i j) volume := by
  intro i j
  have he : (fun t => threeGenerator k (c t) (q t) i j) =
      fun t => c t * threeGenerator k 1 0 i j + q t * threeGenerator k 0 1 i j := by
    funext t
    rw [preGenerator_affine]
    rfl
  rw [he]
  exact (hc.mul_continuous continuous_const).add (hq.mul_continuous continuous_const)

lemma productGenerator_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ i j, LocallyIntegrable (fun t => productGenerator k (c t) (q t) i j) volume :=
  productRowGenerator_locallyIntegrable _ _
    (preGenerator_locallyIntegrable k c q hc hq) (preGenerator_locallyIntegrable k c q hc hq)

lemma productRow_factorization (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (t : ℝ) (j : ProductState) :
    inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 t (0,0) j =
      preRow k c q t j.1 * preRow k c q t j.2 :=
  integrableTransition_product _ _ (preGenerator_locallyIntegrable k c q hc hq)
    (preGenerator_locallyIntegrable k c q hc hq) 0 t (0,0) j

lemma witness_eq_product_output (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (t : ℝ) :
    ThreeTimeVarying.witness k c q t =
      (inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 t *ᵥ
        witnessVec) (0,0) := by
  simp only [Matrix.mulVec, dotProduct, productRow_factorization k c q hc hq,
    witnessVec, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [ThreeTimeVarying.witness, survival, pow_two, Finset.sum_mul_sum]
  norm_num [Fin.sum_univ_succ, mergerWeight]
  ring

lemma zero_migration_output (k : ℕ) (c : ℝ → ℝ) (hc : LocallyIntegrable c volume) (t : ℝ) :
    (inhomogeneousTransition (fun u => productGenerator k (c u) 0) 0 t *ᵥ witnessVec)
      (0,0) = 0 := by
  apply integrableTransition_mulVec_zero_of_closed _
    (productGenerator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0))
    (fun i : ProductState => i = (0,0)) _ witnessVec _ 0 t (0,0) rfl
  · filter_upwards [] with u i j hi hj
    subst i
    rcases j with ⟨j,b⟩
    fin_cases j <;> fin_cases b <;>
      simp_all [productGenerator, productRowGenerator, threeGenerator,
          MarkovChain.Identifiability.totalMigration]
  · intro i hi
    subst i
    exact witnessVec_initial

theorem witness_positive_near_migration_onset (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → (0 < ∫ u in (0 : ℝ)..t, q u) →
      0 < ThreeTimeVarying.witness k c q t := by
  have hmark (u : ℝ) : productGenerator k (c u) (q u) - productGenerator k (c u) 0 =
      q u • migrationMark k := by
    rw [productGenerator_affine, productGenerator_affine, zero_smul, add_zero,
      add_sub_cancel_left]
  obtain ⟨δ, hδ, hpos⟩ := integrable_payoff_positive_near_marked_onset
    (fun u => productGenerator k (c u) (q u)) (fun u => productGenerator k (c u) 0)
    q (migrationMark k) (productGenerator_locallyIntegrable k c q hc hq)
    (productGenerator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0)) hq hqn
    hmark witnessVec (0,0) (zero_migration_output k c hc)
    (by rw [migrationMark_witness_initial]; positivity)
  exact ⟨δ, hδ, fun t ht htδ hQ => by
    rw [witness_eq_product_output k c q hc hq]
    exact hpos t ht htδ hQ⟩

end Rhone.Statistics.Identifiability.ThreeIntegrable
