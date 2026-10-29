/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableRestart
public import Rhone.Statistics.Identifiability.ThreeIntegrableMigration
public import Rhone.Statistics.Identifiability.IntegrableFlowCongruence

/-! # Exact silent-window witness positivity for locally L1 island histories -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma tensor_witness_identity (p : ThreeState → ℝ) :
    (∑ j : ProductState, p j.1 * p j.2 * witnessVec j) =
      9 * p 0 * (∑ j, p j) - (∑ j, p j * mergerWeight j)^2 := by
  simp only [witnessVec, Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, pow_two, Finset.sum_mul_sum]
  norm_num [Fin.sum_univ_succ, mergerWeight]
  ring

lemma migration_product_output (k : ℕ) (q : ℝ → ℝ) (hq : LocallyIntegrable q volume)
    (a t : ℝ) :
    (inhomogeneousTransition (fun u => productGenerator k 0 (q u)) a t *ᵥ witnessVec) (0, 0) =
      9 * (tripleSame k (migrationParameterFrom k q a t) -
        (pairCollision k (migrationParameterFrom k q a t))^2) := by
  have hG := preGenerator_locallyIntegrable k (fun _ => 0) q (locallyIntegrable_const 0) hq
  have he (j : ProductState) :
      inhomogeneousTransition (fun u => productGenerator k 0 (q u)) a t (0, 0) j =
        migrationRow k (migrationParameterFrom k q a t) j.1 *
          migrationRow k (migrationParameterFrom k q a t) j.2 := by
    calc
      _ = inhomogeneousTransition (fun u => threeGenerator k 0 (q u)) a t 0 j.1 *
          inhomogeneousTransition (fun u => threeGenerator k 0 (q u)) a t 0 j.2 :=
        integrableTransition_product _ _ hG hG a t (0, 0) j
      _ = _ := by rw [migration_only_transition_row k q hq a t]
  simp only [Matrix.mulVec, dotProduct, he, tensor_witness_identity,
    migrationRow_sum, migrationRow_weight]
  change 9 * tripleSame k (migrationParameterFrom k q a t) * 1 -
    (3 * pairCollision k (migrationParameterFrom k q a t))^2 = _
  ring

lemma migration_product_output_positive (k : ℕ) (q : ℝ → ℝ)
    (hq : LocallyIntegrable q volume) {a t : ℝ} (hQ : 0 < ∫ u in a..t, q u) :
    0 < (inhomogeneousTransition (fun u => productGenerator k 0 (q u)) a t *ᵥ
      witnessVec) (0, 0) := by
  rw [migration_product_output k q hq a t]
  apply mul_pos (by norm_num)
  apply tripleSame_sub_collision_sq_pos k (Real.exp_pos _)
  exact Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hQ)

theorem witness_positive_after_silent_window (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbefore : ∀ᵐ u, u ∈ Icc 0 a → q u = 0)
    (hsilent : ∀ᵐ u, u ∈ Icc a b → c u = 0) (hQ : 0 < ∫ u in a..b, q u) :
    0 < ThreeTimeVarying.witness k c q b := by
  have hmet : ∀ᵐ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ productGenerator k (c u) (q u) i j := by
    filter_upwards [hqn] with u hu hnonneg
    exact productGenerator_metzler k (c u) (hu hnonneg)
  have hp := integrableTransition_diagonal_positive _
    (productGenerator_locallyIntegrable k c q hc hq) hmet le_rfl ha (0, 0)
  have he : inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) a b =
      inhomogeneousTransition (fun u => productGenerator k 0 (q u)) a b := by
    apply integrableTransition_eq_of_ae_on_interval _ _
      (productGenerator_locallyIntegrable k c q hc hq)
      (productGenerator_locallyIntegrable k (fun _ => 0) q (locallyIntegrable_const 0) hq)
    filter_upwards [hsilent] with u hu hmem
    rw [hu (by simpa only [uIcc_of_le hab] using hmem)]
  rw [witness_restart_after_zero_prefix k c q hc hq ha hbefore b, he]
  exact mul_pos hp (migration_product_output_positive k q hq hQ)

lemma witness_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    Continuous (ThreeTimeVarying.witness k c q) := by
  have hU := integrableTransition_continuous _ (productGenerator_locallyIntegrable k c q hc hq)
  have he : ThreeTimeVarying.witness k c q = fun t =>
      (inhomogeneousTransition (fun u => productGenerator k (c u) (q u)) 0 t *ᵥ witnessVec)
        (0, 0) := funext (witness_eq_product_output k c q hc hq)
  rw [he]
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

lemma witness_positive_right (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) {b : ℝ}
    (hb : 0 < ThreeTimeVarying.witness k c q b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, b ≤ t → t < b + δ → 0 < ThreeTimeVarying.witness k c q t := by
  have hn := (witness_continuous k c q hc hq).continuousAt.eventually (eventually_gt_nhds hb)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨δ, hδ, fun t ht htδ => hnear ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht)]
  linarith

end Rhone.Statistics.Identifiability.ThreeIntegrable
