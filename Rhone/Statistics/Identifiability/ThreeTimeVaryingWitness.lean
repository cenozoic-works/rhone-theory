/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeGenerator
public import Rhone.Statistics.Identifiability.FiniteProductFlow
public import Rhone.Statistics.Identifiability.SingleMechanismPositive

/-! # A three-sample first/root hazard witness for continuous symmetric island histories -/

@[expose] public section

noncomputable section
open Set Matrix
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

abbrev ProductState := ThreeState × ThreeState

def mergerWeight : ThreeState → ℝ := ![3, 1, 0]

def preRow (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ThreeState → ℝ :=
  inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t 0

def survival (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ := ∑ i, preRow k c q t i

def witness (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  9 * preRow k c q t 0 * survival k c q t -
    (∑ i, preRow k c q t i * mergerWeight i)^2

def productGenerator (k : ℕ) (c q : ℝ) : Matrix ProductState ProductState ℝ :=
  productRowGenerator (threeGenerator k c q) (threeGenerator k c q)

def witnessVec (i : ProductState) : ℝ :=
  9 * (if i.1 = 0 then 1 else 0) - mergerWeight i.1 * mergerWeight i.2

def migrationMark (k : ℕ) : Matrix ProductState ProductState ℝ := productGenerator k 0 1

def coalescenceMark (k : ℕ) : Matrix ProductState ProductState ℝ := productGenerator k 1 0

lemma preGenerator_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q) :
    ∀ i j, Continuous (fun u => threeGenerator k (c u) (q u) i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · change Continuous (fun t => -3 * c t - 3 * ((k + 1 : ℝ) * q t))
    fun_prop
  · change Continuous (fun t => 3 * ((k + 1 : ℝ) * q t))
    fun_prop
  · exact continuous_const
  · exact hq
  · change Continuous (fun t => -c t - (2 * (k : ℝ) + 1) * q t)
    fun_prop
  · change Continuous (fun t => 2 * (k : ℝ) * q t)
    fun_prop
  · exact continuous_const
  · change Continuous (fun t => 6 * q t)
    fun_prop
  · change Continuous (fun t => -6 * q t)
    fun_prop

lemma productGenerator_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) :
    ∀ i j, Continuous (fun u => productGenerator k (c u) (q u) i j) := by
  intro i j
  exact ((preGenerator_continuous k c q hc hq i.1 j.1).mul continuous_const).add
    (continuous_const.mul (preGenerator_continuous k c q hc hq i.2 j.2))

lemma productGenerator_affine (k : ℕ) (c q : ℝ) :
    productGenerator k c q = c • coalescenceMark k + q • migrationMark k := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [productGenerator, productRowGenerator, coalescenceMark, migrationMark,
      threeGenerator, MarkovChain.Identifiability.totalMigration] <;> ring

lemma productRow_factorization (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (t : ℝ) (j : ProductState) :
    inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 t (0, 0) j =
      preRow k c q t j.1 * preRow k c q t j.2 :=
  inhomogeneousTransition_product _ _ (preGenerator_continuous k c q hc hq)
    (preGenerator_continuous k c q hc hq) 0 t (0, 0) j

lemma witness_eq_product_output (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (t : ℝ) :
    witness k c q t =
      (inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 t *ᵥ
        witnessVec) (0, 0) := by
  simp only [Matrix.mulVec, dotProduct, productRow_factorization k c q hc hq,
    witnessVec, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [witness, survival, pow_two, Finset.sum_mul_sum]
  norm_num [Fin.sum_univ_succ, mergerWeight]
  ring

lemma witnessVec_initial : witnessVec (0, 0) = 0 := by norm_num [witnessVec, mergerWeight]

lemma migrationMark_witness_initial (k : ℕ) :
    (migrationMark k *ᵥ witnessVec) (0, 0) = 9 * (k + 1 : ℝ) := by
  simp [migrationMark, productGenerator, productRowGenerator, threeGenerator,
    MarkovChain.Identifiability.totalMigration, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_succ, witnessVec, mergerWeight]
  ring

end Rhone.Statistics.Identifiability.ThreeTimeVarying
