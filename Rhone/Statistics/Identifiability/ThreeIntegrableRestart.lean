/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableOnset
public import Rhone.Statistics.Identifiability.IntegrableMarkedStart
public import Rhone.Statistics.Identifiability.IntegrableDiagonalLowerBound
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingOnset

/-! # Restart of the three-sample witness after an AE migration-free prefix -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma zero_migration_output_from (k : ℕ) (c : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (a t : ℝ) :
    (inhomogeneousTransition (fun u => productGenerator k (c u) 0) a t *ᵥ witnessVec)
      (0, 0) = 0 := by
  apply integrableTransition_mulVec_zero_of_closed _
    (productGenerator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0))
    (fun i : ProductState => i = (0, 0)) _ witnessVec _ a t (0, 0) rfl
  · filter_upwards [] with u i j hi hj
    subst i
    rcases j with ⟨j,b⟩
    fin_cases j <;> fin_cases b <;>
      simp_all [productGenerator, productRowGenerator, threeGenerator,
          MarkovChain.Identifiability.totalMigration]
  · intro i hi
    subst i
    exact witnessVec_initial

lemma witness_output_positive_after_start (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (a : ℝ)
    (hqn : ∀ᵐ u, a ≤ u → 0 ≤ q u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, a < t → t < a + δ → (0 < ∫ u in a..t, q u) →
      0 < (inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) a t *ᵥ
        witnessVec) (0, 0) := by
  apply integrable_payoff_positive_after_marked_start
    (fun u => productGenerator k (c u) (q u)) (fun u => productGenerator k (c u) 0)
    q (migrationMark k) (productGenerator_locallyIntegrable k c q hc hq)
    (productGenerator_locallyIntegrable k c (fun _ => 0) hc (locallyIntegrable_const 0)) hq a hqn
  · intro u
    rw [productGenerator_affine, productGenerator_affine, zero_smul, add_zero,
      add_sub_cancel_left]
  · exact zero_migration_output_from k c hc a
  · rw [migrationMark_witness_initial]
    positivity

lemma product_prefix_zero_outside (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ᵐ u, u ∈ Icc 0 a → q u = 0)
    (j : ProductState) (hj : j ≠ (0, 0)) :
    inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 a (0, 0) j = 0 := by
  apply integrableTransition_zero_outside_closed_on_interval _
    (productGenerator_locallyIntegrable k c q hc hq) (fun i : ProductState => i = (0, 0))
    0 a _ (0, 0) j rfl hj
  filter_upwards [hbefore] with u hu hmem i l hi hl
  have hq0 := hu (by simpa only [uIcc_of_le ha] using hmem)
  subst i
  rw [hq0]
  rcases l with ⟨l,b⟩
  fin_cases l <;> fin_cases b <;>
    simp_all [productGenerator, productRowGenerator, threeGenerator,
        MarkovChain.Identifiability.totalMigration]

lemma witness_restart_after_zero_prefix (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ᵐ u, u ∈ Icc 0 a → q u = 0) (t : ℝ) :
    ThreeTimeVarying.witness k c q t =
      inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 a (0, 0) (0, 0) *
        (inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) a t *ᵥ
          witnessVec) (0, 0) := by
  let Q := fun u => productGenerator k (c u) (q u)
  calc
    _ = ∑ j, inhomogeneousTransition Q 0 a (0, 0) j *
        (inhomogeneousTransition Q a t *ᵥ witnessVec) j := by
      rw [witness_eq_product_output k c q hc hq,
        integrableTransition_cocycle _ (productGenerator_locallyIntegrable k c q hc hq) 0 a t]
      rw [← Matrix.mulVec_mulVec]
      rfl
    _ = _ := by
      apply Finset.sum_eq_single (0, 0)
      · intro j _ hj
        rw [product_prefix_zero_outside k c q hc hq ha hbefore j hj, zero_mul]
      · simp

theorem witness_positive_after_zero_migration_prefix (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {a : ℝ} (ha : 0 ≤ a)
    (hbefore : ∀ᵐ u, u ∈ Icc 0 a → q u = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, a < t → t < a + δ → (0 < ∫ u in a..t, q u) →
      0 < ThreeTimeVarying.witness k c q t := by
  obtain ⟨δ, hδ, hpos⟩ := witness_output_positive_after_start k c q hc hq a (by
    filter_upwards [hqn] with u hu hau
    exact hu (ha.trans hau))
  have hmet : ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ productGenerator k (c u) (q u) i j := by
    filter_upwards [hqn] with u hu hnonneg
    exact productGenerator_metzler k (c u) (hu hnonneg)
  have hp := integrableTransition_diagonal_positive _
    (productGenerator_locallyIntegrable k c q hc hq) hmet le_rfl ha (0, 0)
  refine ⟨δ, hδ, fun t ht htδ hQ => ?_⟩
  rw [witness_restart_after_zero_prefix k c q hc hq ha hbefore t]
  exact mul_pos hp (hpos t ht htδ hQ)

end Rhone.Statistics.Identifiability.ThreeIntegrable
